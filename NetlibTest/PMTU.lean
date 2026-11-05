import Netlib.Protocol.PMTUFacts

namespace NetlibTest.PMTU

open Netlib Netlib.Packet Netlib.Protocol Netlib.Protocol.InternetChecksum Netlib.Protocol.PMTU

private def policy : Policy := ⟨⟨552, by decide⟩, 600⟩
private def route : Route := ⟨⟨4096, by decide⟩, false⟩
private def empty : State := ⟨none⟩
private def socket : Header := ⟨3221225986, 3325256706, Packet.Protocol.udp, 41000, 9000⟩
private def router : Address := 3221225985
private def attacker : Address := 3405803777

example (before : State) (valid : before.Valid route) (now : Nat) (advertised : Word) :
    (update policy route before now advertised).state.Valid route := update_valid _ _ _ _ _ valid

example (before : State) (now : Nat) (advertised : Word) :
    ((update policy route before now advertised).state.current route now).val ≤
      (before.current route now).val := update_nonincrease _ _ _ _ _ (by decide)

example : ∃ result entry,
    feedback policy route socket empty 101 ⟨.fragmentationNeeded 576, socket, attacker⟩ = some result ∧
      result.disposition = .updated ∧ result.state.exception = some entry ∧
      entry.mtu.val = 576 ∧ entry.mtu.val < route.mtu.val :=
  feedback_forgery _ _ _ _ _ _ rfl (by decide) (by decide)

example (before : State) (now : Nat) (advertised : Word) (reporter : Address)
    (unlocked : (route.locked || ((before.age now).exception.map (·.locked)).getD false) = false)
    (above : policy.minimum.val ≤ advertised.val)
    (reducing : advertised.val < (before.current route now).val) :
    ∃ result entry,
      feedback policy route socket before now ⟨.fragmentationNeeded advertised, socket, reporter⟩ = some result ∧
      result.disposition = .updated ∧ result.state.exception = some entry ∧
      entry.mtu.val = advertised.val ∧ entry.mtu.val < (before.current route now).val :=
  feedback_forgery_cached _ _ _ _ _ _ _ unlocked above reducing

example (events : List (Nat × Word)) (length now : Nat) :
    68 ≤ ((updateTrace policy route empty (events.take length)).current route now).val ∧
      ((updateTrace policy route empty (events.take length)).current route now).val ≤ 4096 :=
  updateTrace_prefix_bounds _ _ _ _ (State.valid_initial route) _ _

private def ensure (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def current (state : State) (now : Nat) : Nat := (state.current route now).val

private def expectEntry (state : State) (mtu : Nat) (locked : Bool) (expires : Nat) : IO Unit := do
  match state.exception with
  | none => throw (IO.userError "Expected a PMTU exception.")
  | some entry =>
    ensure (entry.mtu.val == mtu && entry.locked == locked && entry.expires == expires)
      "PMTU exception must preserve its selected size, lock, and expiry."

private def updateTests : IO Unit := do
  let first := update policy route empty 100 600
  ensure (first.disposition == .updated && current first.state 100 == 600)
    "A smaller nonzero advertisement must reduce the route's PMTU."
  expectEntry first.state 600 false 700
  let forged := feedback policy route socket first.state 101 ⟨.fragmentationNeeded 576, socket, attacker⟩
  match forged with
  | none => throw (IO.userError "A matching forged quote must exercise the modeled spoofing limitation.")
  | some reduced =>
    ensure (reduced.disposition == .updated && current reduced.state 101 == 576)
      "A matching quote from an untrusted reporter can reduce the cached PMTU."
    expectEntry reduced.state 576 false 701
    ensure (forged == feedback policy route socket first.state 101 ⟨.fragmentationNeeded 576, socket, router⟩)
      "The PMTU feedback guard does not authenticate the reporter address."
  let increased := update policy route first.state 101 1200
  ensure (increased.disposition == .increase && increased.state == first.state)
    "Larger advertisements must leave the active cache and expiry unchanged."
  for advertised in ([0, 548, 551] : List Word) do
    let low := update policy route empty 10 advertised
    ensure (low.disposition == .updated && current low.state 10 == 552)
      "Advertisements below the configured floor must clamp to the floor."
    expectEntry low.state 552 true 610
    let locked := update policy route low.state 11 68
    ensure (locked.disposition == .locked && locked.state == low.state)
      "A floor-clamped exception must remain locked until expiry."
  let exactFloor := update policy route empty 10 552
  expectEntry exactFloor.state 552 false 610
  let tinyRoute : Route := ⟨⟨68, by decide⟩, false⟩
  let tiny := update policy tinyRoute empty 10 0
  expectEntry tiny.state 68 true 610
  ensure ((tiny.state.current tinyRoute 10).val == 68)
    "Floor clamping must never raise PMTU above a smaller physical route MTU."
  let lockedRoute := update policy { route with locked := true } empty 10 600
  ensure (lockedRoute.disposition == .locked && lockedRoute.state == empty)
    "A locked route must ignore PMTU advertisements."

private def refreshTests : IO Unit := do
  let first := update policy route empty 100 600
  for now in [100, 101, 399] do
    let early := update policy route first.state now 600
    ensure (early.disposition == .unchanged && early.state == first.state)
      "Equal advertisements before half-life must not refresh expiry."
  for now in [400, 401, 699] do
    let refreshed := update policy route first.state now 600
    ensure (refreshed.disposition == .updated && current refreshed.state now == 600)
      "An equal advertisement at or after half-life must refresh expiry."
    expectEntry refreshed.state 600 false (now + 600)
  ensure (current first.state 699 == 600 && current first.state 700 == 4096 &&
      current first.state 1000000 == 4096 && first.state.age 700 == empty)
    "Expiry at the exact deadline must restore the physical route MTU."
  let expired := update policy route first.state 700 1200
  ensure (expired.disposition == .updated && current expired.state 700 == 1200)
    "An expired lower cache must be aged before a fresh advertisement is compared."
  let locked := update policy route empty 100 0
  ensure (current locked.state 699 == 552 && current locked.state 700 == 4096)
    "Exception expiry must also clear a floor lock."
  let fresh := update policy route locked.state 700 600
  ensure (fresh.disposition == .updated && current fresh.state 700 == 600)
    "An expired floor lock must permit a new nonzero update."

private def feedbackTests : IO Unit := do
  let first := (update policy route empty 100 600).state
  ensure ((feedback policy route socket first 101 ⟨.timeExceeded, socket, router⟩).isNone)
    "Time Exceeded feedback must not update PMTU."
  for quote in [
      { socket with source := socket.source + 1 },
      { socket with destination := socket.destination + 1 },
      { socket with protocol := Packet.Protocol.tcp },
      { socket with sourcePort := socket.sourcePort + 1 },
      { socket with destinationPort := socket.destinationPort + 1 }] do
    ensure ((feedback policy route socket first 101 ⟨.fragmentationNeeded 576, quote, attacker⟩).isNone)
      "A PMTU update must match all five fields of the selected connected UDP socket."

private def sendTests : IO Unit := do
  let first := (update policy route empty 100 600).state
  ensure (send route first 101 true 1200 == .messageSize && send route first 101 true 500 == .accepted)
    "After pending socket errors are drained, DF sends must obey the cached PMTU."
  for size in [571, 572] do
    ensure (send route first 101 true size == .accepted)
      "DF payloads below and exactly at PMTU minus the IPv4/UDP headers must fit."
  ensure (send route first 101 true 573 == .messageSize && send route first 101 false 1200 == .accepted)
    "The first oversized DF payload must fail while a non-DF send may proceed."
  ensure (send route first 700 true 1200 == .accepted)
    "A send after cache expiry must use the physical route MTU."
  let maximum : Route := ⟨⟨65535, by decide⟩, false⟩
  ensure (send maximum empty 0 true 65507 == .accepted && send maximum empty 0 false 65507 == .accepted &&
      send maximum empty 0 true 65508 == .invalidLength && send maximum empty 0 false 65508 == .invalidLength)
    "IPv4 permits at most 65507 UDP payload bytes, independently of DF."
  let forged := (update policy route first 101 576).state
  ensure (send route forged 102 true 548 == .accepted && send route forged 102 true 549 == .messageSize &&
      send route forged 102 true 500 == .accepted)
    "A forged reduction must change the later send boundary, including odd payload sizes."

private def traceTests : IO Unit := do
  let events : List (Nat × Word) := [(100, 600), (101, 576), (102, 1200), (103, 0), (104, 68), (704, 800)]
  for length in List.range (events.length + 1) do
    let state := updateTrace policy route empty (events.take length)
    for now in [104, 704, 1000000] do
      ensure (68 ≤ current state now && current state now ≤ 4096)
        "Every update prefix must retain physical IPv4 PMTU bounds at every observation time."
  let final := updateTrace policy route empty events
  expectEntry final 800 false 1304
  ensure (current final 704 == 800 && current final 1304 == 4096)
    "A trace must retain locking before expiry and allow a fresh larger value after expiry."

def run : IO Unit := do
  updateTests
  refreshTests
  feedbackTests
  sendTests
  traceTests
  IO.println "Host PMTU feedback and send tests passed."

end NetlibTest.PMTU
