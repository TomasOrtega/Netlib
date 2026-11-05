import Netlib.Protocol.IPv4ReassemblyLayout

namespace NetlibTest.IPv4Reassembly

open Netlib Packet Protocol Protocol.IPv4Reassembly

private def policy : Policy := ⟨30⟩
private def domain : Domain := ⟨0, 0⟩
private def base : IPv4.Packet := ⟨42, 1234, false, 51, Packet.Protocol.udp, 3221225986, 3325256706, []⟩

private def part (start size : Nat) (more : Bool) (df : Bool := false) (tos : UInt8 := 42)
    (fill : Option UInt8 := none) : IPv4Fragment.Decoded :=
  let payload := (List.range size).map (fun index => fill.getD (UInt8.ofNat (start + index)))
  let packet : IPv4Fragment.Packet := ⟨{ base with payload, dontFragment := df, tos }, more,
    ⟨start / 8 % 8192, Nat.mod_lt _ (by decide)⟩⟩
  ⟨packet, IPv4Fragment.computedChecksum packet, []⟩

example (before : State) (now : Nat) (fragment : IPv4Fragment.Decoded) (result : Result) (packet : Output)
    (accepted : arrive policy before now domain fragment = .ok result) (emitted : result.output = some packet)
    (valid : before.Valid) : packet.packet.Encodable :=
  (arrive_output_valid _ _ _ _ _ _ _ accepted emitted valid).encodable

example (before : State) (now : Nat) (fragment : IPv4Fragment.Decoded) (result : Result)
    (accepted : arrive policy before now domain fragment = .ok result)
    (duplicate : result.disposition = .duplicate) : result.output = none :=
  arrive_duplicate_no_output _ _ _ _ _ _ accepted duplicate

example (events : List Arrival) (final : State) (results : List Result)
    (accepted : execute policy State.initial events = .ok (final, results)) :
    final.Valid ∧ ∀ result ∈ results, result.state.Valid :=
  execute_valid _ _ _ _ _ accepted State.initial_valid

example (events : List Arrival) (final : State) (results : List Result)
    (accepted : execute policy State.initial events = .ok (final, results)) :
    final.Sources (events.map (·.fragment)) := by
  simpa only [List.append_nil] using execute_sources _ _ _ _ _ [] accepted State.initial_sources

example (events : List Arrival) (prefixLength : Nat) (final : State) (results : List Result)
    (accepted : execute policy State.initial (events.take prefixLength) = .ok (final, results)) :
    final.LayoutValid ∧ ∀ result ∈ results, result.state.LayoutValid ∧ result.disposition ≠ .invalidLayout :=
  execute_layout _ _ _ _ _ accepted State.initial_layout

example (before : State) (now : Nat) (fragment : IPv4Fragment.Decoded) (result : Result)
    (accepted : arrive policy before now domain fragment = .ok result) (valid : before.LayoutValid) :
    result.disposition ≠ .invalidLayout := arrive_no_invalidLayout _ _ _ _ _ _ accepted valid

private def ensure (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def step (state : State) (fragment : IPv4Fragment.Decoded) (now : Nat := 0)
    (selected : Domain := domain) : IO Result :=
  match arrive policy state now selected fragment with
  | .ok result => pure result
  | .error error => throw (IO.userError error.describe)

private def queue (state : State) (fragment : IPv4Fragment.Decoded := part 0 8 true)
    (selected : Domain := domain) : IO Queue :=
  match state.lookup (key selected fragment) with
  | some value => pure value
  | none => throw (IO.userError "Expected an incomplete fragment queue.")

private def output (result : Result) : IO Output :=
  match result.output with
  | some value => pure value
  | none => throw (IO.userError "Expected a completed IPv4 input packet.")

private def permutationsTests : IO Unit := do
  let first := part 0 16 true
  let middle := part 16 16 true
  let last := part 32 5 false
  for order in [[first, middle, last], [first, last, middle], [middle, first, last],
      [middle, last, first], [last, first, middle], [last, middle, first]] do
    let mut state := State.initial
    let mut completed := []
    for fragment in order do
      let result ← step state fragment
      state := result.state
      if let some packet := result.output then completed := packet :: completed
    ensure (completed.length == 1 && state.queues.isEmpty) "Every nonoverlapping arrival order must emit once and remove its queue."
    let some packet := completed.head? | throw (IO.userError "Expected one completed packet.")
    ensure (packet.packet.payload == (List.range 37).map UInt8.ofNat && packet.packet.ttl == 51 &&
        packet.packet.tos == 42 && !packet.packet.dontFragment && packet.reassembled &&
        packet.maxSize == 36 && packet.maxDFSize == 0 && packet.pieces.map (·.start) == [0, 16, 32])
      "Completed payload order, first-fragment header, and fragment-size metadata must be independent of arrival order."
    let repeated ← step state last
    ensure (repeated.output.isNone && repeated.state.queues.length == 1)
      "A repeated final fragment after completion cannot emit the removed datagram again."

private def duplicateTests : IO Unit := do
  let first ← step State.initial (part 0 8 true)
  let second ← step first.state (part 8 8 true)
  let before ← queue second.state
  ensure (before.runs.length == 1 && before.pieces.length == 2) "Adjacent global-tail arrivals must share one run."
  let duplicate ← step second.state (part 0 16 true true 3 (some 255)) 29
  let after ← queue duplicate.state
  ensure (duplicate.disposition == .duplicate && duplicate.output.isNone && after == before)
    "A byte-different interval contained in one run must not replace data or refresh ECN, DF, sizes, or timeout."
  let finalDuplicate ← step second.state (part 8 8 false false 3 (some 255))
  let marked ← queue finalDuplicate.state
  ensure (finalDuplicate.disposition == .duplicate && finalDuplicate.output.isNone && marked.last &&
      marked.length == 16 && marked.meat == 16 && marked.ecn == before.ecn && marked.expires == 30)
    "Duplicate final arrivals must retain LAST/length mutation while skipping completion and ECN updates."
  let later ← step finalDuplicate.state (part 8 8 false)
  ensure (later.disposition == .duplicate && later.output.isNone)
    "A full queue marked final by a duplicate must still skip completion on another duplicate."
  let gap ← step first.state (part 16 8 true)
  let filled ← step gap.state (part 8 8 true)
  let separate ← queue filled.state
  ensure (separate.runs.length == 3) "Internal gap fills must retain distinct runs despite adjacency."
  let overlap ← step filled.state (part 0 16 true)
  ensure (overlap.disposition == .overlap && overlap.state.queues.isEmpty && overlap.output.isNone)
    "An interval crossing separate adjacent runs is overlap, even when forward arrival order would classify it duplicate."
  let wide ← step State.initial (part 0 16 true)
  let overlapping ← step wide.state (part 8 16 true)
  ensure (overlapping.disposition == .overlap && overlapping.state.queues.isEmpty)
    "Any partial overlap must kill the queue."

private def lengthTests : IO Unit := do
  let final ← step State.initial (part 16 8 false)
  let overrun ← step final.state (part 0 32 true)
  ensure (overrun.disposition == .inconsistentLength && overrun.state.queues.isEmpty)
    "A nonfinal interval extending past an established final length must kill the queue."
  let wide ← step State.initial (part 0 16 true)
  let short ← step wide.state (part 8 4 false)
  ensure (short.disposition == .inconsistentLength && short.state.queues.isEmpty)
    "A final fragment cannot shorten an already observed queue extent."
  let inconsistent ← step final.state (part 8 8 false)
  ensure (inconsistent.disposition == .inconsistentLength && inconsistent.state.queues.isEmpty)
    "Conflicting final lengths must kill the queue before interval insertion."
  let empty ← step wide.state (part 16 7 true)
  ensure (empty.disposition == .empty && empty.state.queues.isEmpty)
    "An MF payload shorter than eight bytes normalizes to zero and kills its queue."
  let trimmed ← step State.initial (part 0 11 true)
  let stored ← queue trimmed.state
  ensure (stored.meat == 8 && stored.length == 8 && stored.maxSize == 28)
    "Unaligned MF payloads must trim to complete eight-byte units before queue accounting."
  let finished ← step trimmed.state (part 8 3 false)
  ensure ((← output finished).packet.payload == (List.range 11).map UInt8.ofNat)
    "Trimmed bytes must not leak into the completed payload."
  let huge ← step wide.state (part 65528 8 false)
  ensure (huge.disposition == .buffered && huge.output.isNone && (← queue huge.state).length == 65536)
    "An incomplete excessive extent remains queued until completion or expiry."
  let maximum ← step State.initial (part 0 65512 true)
  let excessive ← step maximum.state (part 65512 4 false)
  ensure (excessive.disposition == .tooLarge && excessive.output.isNone && excessive.state.queues.isEmpty)
    "A completed payload exceeding the IPv4 total-length limit must kill the queue."

private def metadataTests : IO Unit := do
  for firstDF in [false, true] do
    for lastDF in [false, true] do
      let first ← step State.initial (part 0 16 true firstDF)
      let final ← step first.state (part 16 5 false lastDF)
      let packet ← output final
      ensure (packet.maxSize == 36 && packet.maxDFSize == (if firstDF then 36 else if lastDF then 25 else 0) &&
          packet.packet.dontFragment == firstDF)
        "Reassembled DF must depend on whether a DF fragment attains the largest fragment size."
  let equalFirst ← step State.initial (part 0 8 true false)
  let equalFinal ← step equalFirst.state (part 8 8 false true)
  ensure ((← output equalFinal).packet.dontFragment)
    "A later DF fragment tied for the maximum size must set reassembled DF."
  let ect ← step State.initial (part 0 8 true false 42)
  let ce ← step ect.state (part 8 3 false false 3)
  ensure ((← output ce).packet.tos == 43 && (← output ce).packet.ttl == 51)
    "CE must combine with the offset-zero DSCP and TTL."
  let mixed ← step State.initial (part 0 8 true false 0)
  let invalid ← step mixed.state (part 8 3 false false 2)
  ensure (invalid.disposition == .invalidECN && invalid.state.queues.isEmpty)
    "Not-ECT mixed with an ECN-capable fragment must reject completion."
  let ect1 ← step ect.state (part 8 3 false false 1)
  ensure ((← output ect1).packet.tos == 42)
    "ECT(0) and ECT(1) without CE must retain the first fragment's ECN bits."

private def expiryAndKeyTests : IO Unit := do
  let first := part 0 8 true false 42 (some 1)
  let queued ← step State.initial first
  let repeated ← step queued.state first 29
  ensure ((← queue repeated.state).expires == 30) "Fragment arrival must not refresh the fixed queue timeout."
  let expired ← step repeated.state (part 8 3 false false 42 (some 2)) 30
  ensure (expired.output.isNone && (← queue expired.state).first.isNone && (← queue expired.state).expires == 60)
    "An arrival at the timeout boundary must start a fresh queue and cannot mix with expired bytes."
  let fresh ← step expired.state (part 0 8 true false 42 (some 3)) 31
  ensure ((← output fresh).packet.payload == List.replicate 8 3 ++ List.replicate 3 2)
    "Completion after timeout must use only the new queue generation."
  let same := part 0 8 true
  let packet := same.packet
  let variants := [
    { packet with identification := packet.identification + 1 },
    { packet with source := packet.source + 1 },
    { packet with destination := packet.destination + 1 },
    { packet with protocol := Packet.Protocol.icmp }]
  let mut state := (← step State.initial same).state
  for changed in variants do
    state := (← step state ⟨changed, IPv4Fragment.computedChecksum changed, []⟩).state
  state := (← step state same 0 ⟨1, 0⟩).state
  state := (← step state same 0 ⟨0, 1⟩).state
  ensure (state.queues.length == 7) "All five IPv4 key fields and the user/vif domain must isolate fragment queues."
  let before := (state.erase (key domain same)).queues
  let finished ← step state (part 8 3 false)
  ensure (finished.state.queues == before && finished.output.isSome)
    "Completing one key must preserve all unrelated queues."
  let whole ← step queued.state (part 0 5 false true)
  ensure (whole.disposition == .whole && !(← output whole).reassembled && (← output whole).maxSize == 0 &&
      whole.state.queues == queued.state.queues)
    "Unfragmented input must bypass queues even when its identification matches an incomplete queue."
  match arrive policy queued.state 0 domain { first with checksum := first.checksum + 1 } with
  | .error .invalidFragment => pure ()
  | _ => throw (IO.userError "A bad IPv4 checksum must fail before queue processing.")
  match arrive policy fresh.state 30 domain same with
  | .error .backwardsClock => pure ()
  | _ => throw (IO.userError "A backwards model clock must be rejected.")

def run : IO Unit := do
  permutationsTests
  duplicateTests
  lengthTests
  metadataTests
  expiryAndKeyTests
  IO.println "Stateful IPv4 input reassembly tests passed."

end NetlibTest.IPv4Reassembly
