import Netlib.Protocol.ReassemblyForwarding

namespace NetlibTest.ReassemblyForwarding

open Netlib Packet Protocol Protocol.ReassemblyForwarding

private def ensure (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def unwrap (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

private def mtu (value : Nat) : IO IPv4Fragmentation.MTU := do
  if valid : 68 ≤ value ∧ value < 65536 then return ⟨value, valid⟩
  else throw (IO.userError "Invalid test route MTU.")

private def active (limit : IPv4Fragmentation.MTU) (permit : Bool := true) : Pipeline :=
  ⟨⟨⟨[⟨⟨0, 0⟩, some "out"⟩], [], if permit then .permit else .deny, [], .permit⟩, fun _ => limit⟩,
    fun zone header =>
      let translated := { header with
        source := 3405803777
        destination := 3325256706
        sourcePort := 40000
        destinationPort := 9000 }
      ⟨⟨header, translated.reverse, zone, zone, 0⟩, true, true⟩⟩

private def fragments (size : Nat) (df : Bool := false) (ttl : UInt8 := 64)
    (limit : IPv4Refragmentation.Budget := ⟨600, by decide⟩) : IO (List IPv4Fragment.Decoded) := do
  let data := (List.range size).map (fun index => UInt8.ofNat (index * 37))
  let udp ← unwrap (UDP.encodeComputed 3221225986 3405803778 41000 8080 data)
  let packet : IPv4.Packet := ⟨185, 3719, df, ttl, 17, 3221225986, 3405803778, udp⟩
  return (← unwrap (IPv4Refragmentation.checkGenerated packet limit df)).fragments

private def drive (early late : Pipeline) (family : List IPv4Fragment.Decoded) : IO Result := do
  let mut before := State.initial
  let mut final : Option Result := none
  for (fragment, index) in family.zipIdx do
    let selected := if index + 1 = family.length then late else early
    let result ← unwrap (step selected ⟨30⟩ before ⟨index + 1, ⟨65536, 0⟩, 0, fragment⟩)
    if index + 1 < family.length then
      ensure (result.completed.isNone && result.state.conntrack == before.conntrack)
        "Incomplete fragments must leave conntrack unchanged and cannot reach forwarding."
    before := result.state
    final := some result
  match final with
  | some result => return result
  | none => throw (IO.userError "Supply a test fragment family.")

private def completion (result : Result) : IO Completed := do
  match result.completed with
  | some completed => return completed
  | none => throw (IO.userError "The final arrival must complete the datagram.")

private def expectForwarded (result : Result) (cap : Nat) : IO Unit := do
  let completed ← completion result
  let some emission := completed.outcome.output | throw (IO.userError "The datagram must forward.")
  let some budget := completed.outcome.sizeCap | throw (IO.userError "Forwarding requires a computed size cap.")
  ensure (completed.outcome.disposition == .forwarded && budget.val == cap &&
      emission.decoded.ip.packet.ttl == 63 && emission.decoded.header.source == 3405803777 &&
      emission.decoded.header.destination == 3325256706 && result.state.conntrack.records.length == 1 &&
      emission.decoded.datagram.payload == completed.source.packet.datagram.payload)
    "Completion must compose current policy, NAT, payload preservation, TTL, and the ingress fragment cap."
  let family ← unwrap (IPv4Refragmentation.checkGenerated emission.decoded.ip.packet budget false)
  ensure (family.fragments.all (fun part => decide (part.packet.wireLength ≤ cap)))
    "Re-fragmented output must fit both the route and ingress maximum."

def run : IO Unit := do
  let large := active (← mtu 1500)
  let denied := active (← mtu 1500) false
  let family ← fragments 1200
  ensure (family.length == 3) "The selected source must arrive as three fragments."
  expectForwarded (← drive large large family) 596
  expectForwarded (← drive denied large family.reverse) 596
  let loggedOff ← drive large denied family
  let completed ← completion loggedOff
  ensure (completed.outcome.disposition == .forwardDrop && completed.outcome.output.isNone &&
      loggedOff.state.conntrack.records.isEmpty)
    "A policy installed before completion must deny fragments admitted under an earlier permit."
  let dfFamily ← fragments 1200 true
  let through ← drive (active (← mtu 600)) (active (← mtu 600)) dfFamily
  expectForwarded through 596
  let completed ← completion through
  ensure (completed.reassembled.packet.dontFragment && completed.reassembled.maxSize == 596 &&
      allowsDF completed.reassembled false && allowsDF completed.reassembled true)
    "A reassembled DF datagram may forward when its original maximum fits, with explicit output-path DF choices."
  let narrow := active (← mtu 400) false
  let rejected ← drive large narrow dfFamily
  let completed ← completion rejected
  ensure (completed.outcome.disposition == .mtuExceeded && completed.outcome.afterSource.isNone &&
      rejected.state.conntrack.records.isEmpty)
    "An original DF maximum above the outgoing MTU must reject before forward filtering or confirmation."
  let context : ICMPForwarding.Context :=
    { returnPath := fun _ => some ⟨"peer", 3221225985, ⟨600, by decide⟩, 64⟩ }
  let control := completed.control context 73
  ensure (control.disposition == .sent && control.reason == some (.fragmentationNeeded ⟨400, by decide⟩))
    "Reassembled DF rejection must retain the existing related ICMP generation semantics."
  expectForwarded (← drive large (active (← mtu 400)) family) 400
  let tiny ← fragments 13 false 64 ⟨28, by decide⟩
  expectForwarded (← drive large large tiny) 28
  let expired ← drive large large (← fragments 1200 false 1)
  let completed ← completion expired
  ensure (completed.outcome.disposition == .ttlExpired && completed.outcome.output.isNone &&
      (completed.control context 74).reason == some .timeExceeded)
    "The reassembled offset-zero TTL must select ordinary forwarding expiry and related ICMP output."
  IO.println "Ingress reassembly and current forwarding policy tests passed."

end NetlibTest.ReassemblyForwarding
