import Netlib.Check.ReassemblyForwarding

namespace NetlibTest.ReassemblyForwardingCheck

open Netlib Packet Protocol Check.ReassemblyForwarding

example (report : Report environment initial observations) :
    report.compliant = true ↔ Agreement environment initial observations := report.compliant_iff

example (report : Report environment initial observations) (valid : initial.fragments.Valid) :
    report.final.fragments.Valid ∧ ∀ finding ∈ report.findings, finding.result.state.fragments.Valid := report.queue_valid valid

private def ensure (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def unwrap (value : Except String α) : IO α :=
  match value with
  | .ok result => pure result
  | .error error => throw (IO.userError error)

private def reject (value : Except String α) (message : String) : IO Unit :=
  match value with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError message)

private def element (items : List α) (index : Nat) : IO α :=
  match items[index]? with
  | some value => pure value
  | none => throw (IO.userError s!"Expected replay element {index}.")

private def events (json : Lean.Json) : Except String (Array Lean.Json) := do
  (← json.getObjVal? "events").getArr?

private def changeEvent (json : Lean.Json) (index : Nat) (change : Lean.Json → Lean.Json) : Except String Lean.Json := do
  let values ← events json
  return json.setObjVal! "events" (.arr (values.set! index (change values[index]!)))

private def changeObserved (json : Lean.Json) (index : Nat) (change : Lean.Json → Lean.Json) : Except String Lean.Json := do
  let values ← events json
  let observed ← values[index]!.getObjVal? "observed"
  changeEvent json index (·.setObjVal! "observed" (change observed))

private def emptyObserved : Lean.Json := Lean.Json.mkObj [("reassembled", .null), ("forwarded", .arr #[])]

private def fragmentBytes (packet : IPv4.Packet) (start count : Nat) (more : Bool) : Except String (List UInt8) :=
  IPv4InputFragment.encode (IPv4Fragmentation.fragmentPacket packet
    ⟨start, packet.payload.drop start |>.take count, more⟩)

private def fragmentEvent (now : Nat) (config policy : String) (raw : List UInt8) : Lean.Json := Lean.Json.mkObj [
  ("type", .str "fragment"), ("at", Lean.toJson now), ("config", .str config), ("queuePolicy", .str policy),
  ("zone", Lean.toJson (0 : Nat)), ("vif", Lean.toJson (0 : Nat)),
  ("rawIPv4", .str (Import.EAPOL.bytesToHex raw)), ("observed", emptyObserved), ("state", .null)]

private def waitEvent (now : Nat) : Lean.Json := Lean.Json.mkObj [
  ("type", .str "wait"), ("at", Lean.toJson now), ("state", .null)]

private def eraseEvent (now : Nat) (raw : List UInt8) : Lean.Json := Lean.Json.mkObj [
  ("type", .str "erase"), ("at", Lean.toJson now), ("zone", Lean.toJson (0 : Nat)),
  ("rawIPv4", .str (Import.EAPOL.bytesToHex raw)), ("state", .null)]

private def base (fixture : Lean.Json) (values : Array Lean.Json) : Except String Lean.Json := do
  let fields ← ["schema", "routing", "mtus"].mapM fun key => do return (key, ← fixture.getObjVal? key)
  let configs ← (← (← fixture.getObjVal? "configs").getArr?).toList.mapM fun config => do
    let fields ← ["id", "forward", "late", "nat"].mapM fun key => do return (key, ← config.getObjVal? key)
    return Lean.Json.mkObj fields
  return Lean.Json.mkObj (fields ++ [("configs", Lean.toJson configs), ("initial", .null),
    ("reassembly", Lean.Json.mkObj [("userBase", Lean.toJson (2 : Nat)),
      ("policies", Lean.toJson [Lean.Json.mkObj [("id", .str "normal"), ("timeout", Lean.toJson (10 : Nat))],
        Lean.Json.mkObj [("id", .str "short"), ("timeout", Lean.toJson (1 : Nat))]])]),
    ("events", .arr values)])

private def source (fixture : Lean.Json) : IO (IPv4.Packet × Import.EthernetIPv4.Envelope) := do
  let values ← unwrap (events fixture)
  let bytes ← unwrap (Import.EAPOL.bytesFromHex (← unwrap ((← unwrap (values[0]!.getObjVal? "raw")).getStr?)))
  let checked ← unwrap (Check.Wire.checkBytes bytes)
  let ip := checked.packet.ip.packet
  let udp := checked.packet.datagram
  let datagram := UDP.computed ip.source ip.destination udp.sourcePort udp.destinationPort (List.range 25 |>.map UInt8.ofNat)
  let payload ← unwrap (UDP.encode ip.source ip.destination datagram)
  return ({ ip with payload, identification := 0x4abc, ttl := 64, dontFragment := false }, checked.envelope)

private def observedFamily (envelope : Import.EthernetIPv4.Envelope) (packet : IPv4.Packet) : IO Lean.Json := do
  let parts ← [(0, 8, true), (8, 8, true), (16, packet.payload.length - 16, false)].mapM fun (start, count, more) => do
    let payload ← unwrap (fragmentBytes packet start count more)
    return Import.EAPOL.bytesToHex (Import.EthernetIPv4.encode { envelope with payload })
  return Lean.toJson parts

private def populate (json : Lean.Json) (envelope : Import.EthernetIPv4.Envelope) : IO Lean.Json := do
  let input ← unwrap (Input.fromJson json)
  let report ← unwrap input.check
  let mut result := json
  for finding in report.findings do
    if let some actual := finding.result.fragment then
      if let some output := actual.reassembly.output then
        let raw ← unwrap (IPv4.encode output.packet)
        let forwarded ← match actual.completed with
          | none => pure (.arr #[])
          | some completed => match completed.outcome.output with
            | none => pure (.arr #[])
            | some emission => observedFamily envelope emission.decoded.ip.packet
        result ← unwrap (changeEvent result finding.observation.index (·.setObjVal! "observed"
          (Lean.Json.mkObj [("reassembled", .str (Import.EAPOL.bytesToHex raw)), ("forwarded", forwarded)])))
  return result

private def report (json : Lean.Json) : IO (Input × Bool) := do
  let input ← unwrap (Input.fromJson json)
  let actual ← unwrap input.check
  return (input, actual.compliant)

private def baseTests (fixture : Lean.Json) : IO Lean.Json := do
  let (packet, envelope) ← source fixture
  let first ← unwrap (fragmentBytes packet 0 8 true)
  let last ← unwrap (fragmentBytes packet 8 (packet.payload.length - 8) false)
  let json ← populate (← unwrap (base fixture #[fragmentEvent 0 "unauthenticated" "normal" first,
    fragmentEvent 1 "credential-permitted" "short" last])) envelope
  let input ← unwrap (Input.fromJson json)
  let actual ← unwrap input.check
  let pending ← element actual.findings 0
  let complete ← element actual.findings 1
  ensure (actual.compliant && pending.result.state.conntrack.records.isEmpty &&
      pending.result.state.fragments.queues.length == 1 && complete.result.state.fragments.queues.isEmpty &&
      complete.result.state.conntrack.records.length == 1)
    "Only completion may apply the current permitted policy and confirm a connection."
  let some completed := complete.result.fragment.bind (·.completed) | throw (IO.userError "Expected completed forwarding.")
  ensure (completed.reassembled.packet == packet && completed.reassembled.maxSize == 45 &&
      completed.outcome.sizeCap.map (·.val) == some 45 && completed.outcome.output.isSome)
    "Reassembly must preserve the whole packet and retain the largest accepted fragment size."
  let reversed ← unwrap (changeObserved json 1 fun observed => observed.setObjVal! "forwarded"
    (.arr ((observed.getObjVal? "forwarded").toOption.get! |>.getArr?.toOption.get! |>.reverse)))
  ensure ((← report reversed).2) "Observed fragment order must not select a different output contract."
  let denied ← populate (← unwrap (base fixture #[fragmentEvent 0 "credential-permitted" "normal" first,
    fragmentEvent 1 "unauthenticated" "short" last])) envelope
  let deniedInput ← unwrap (Input.fromJson denied)
  let deniedReport ← unwrap deniedInput.check
  ensure (deniedReport.compliant && deniedReport.final.conntrack.records.isEmpty)
    "A policy change before completion must deny the reassembled packet under the completion policy."
  return json

private def mismatchTests (json : Lean.Json) : IO Unit := do
  let input ← unwrap (Input.fromJson json)
  let original ← unwrap input.check
  let values ← unwrap (events json)
  let observed ← unwrap (values[1]!.getObjVal? "observed")
  let output ← unwrap ((← unwrap (observed.getObjVal? "forwarded")).getArr?)
  let empty := observed.setObjVal! "forwarded" (.arr #[])
  let duplicate := observed.setObjVal! "forwarded" (.arr (output.push output[0]!))
  let missing := observed.setObjVal! "forwarded" (.arr (output.extract 1 output.size))
  let absent := observed.setObjVal! "reassembled" .null
  let bytes ← unwrap (Import.EAPOL.bytesFromHex (← unwrap output[0]!.getStr?))
  let wire ← unwrap (wireFragment bytes)
  let altered ← unwrap (IPv4InputFragment.encode { wire.decoded.packet with ttl := 62 })
  let changedTTL := observed.setObjVal! "forwarded" (.arr (output.set! 0 (.str (Import.EAPOL.bytesToHex
    (Import.EthernetIPv4.encode { wire.envelope with payload := altered })))))
  for changed in [empty, duplicate, missing, absent, changedTTL] do
    let selected ← unwrap (Input.fromJson (← unwrap (changeEvent json 1 (·.setObjVal! "observed" changed))))
    let actual ← unwrap selected.check
    ensure (!actual.compliant && actual.final.conntrack == original.final.conntrack &&
        actual.final.fragments == original.final.fragments)
      "A well-framed observation mismatch must not replace computed queue or conntrack state."
  let snapshot ← unwrap ((← unwrap (events (← unwrap (Import.Json.parse (← IO.FS.readFile "examples/icmp/replay.json")))))[0]!.getObjVal? "state")
  let stateMismatch ← unwrap (Input.fromJson (← unwrap (changeEvent json 1 (·.setObjVal! "state" snapshot))))
  let stateReport ← unwrap stateMismatch.check
  ensure (!stateReport.compliant && stateReport.final.conntrack == original.final.conntrack)
    "An observed empty conntrack snapshot must mismatch a computed confirmation without replacing it."

private def controlTests (fixture : Lean.Json) : IO Unit := do
  let (packet, envelope) ← source fixture
  let first ← unwrap (fragmentBytes packet 0 8 true)
  let last ← unwrap (fragmentBytes packet 8 (packet.payload.length - 8) false)
  let whole ← unwrap (IPv4.encode packet)
  let json ← populate (← unwrap (base fixture #[fragmentEvent 0 "credential-permitted" "normal" first,
    fragmentEvent 1 "credential-permitted" "short" last,
    fragmentEvent 2 "credential-permitted" "normal" first, eraseEvent 3 whole, waitEvent 4, waitEvent 12,
    fragmentEvent 13 "credential-permitted" "normal" last])) envelope
  let input ← unwrap (Input.fromJson json)
  let actual ← unwrap input.check
  let erased ← element actual.findings 3
  let waited ← element actual.findings 4
  let expired ← element actual.findings 5
  ensure (actual.compliant && erased.result.state.conntrack.records.isEmpty &&
      erased.result.state.fragments.queues.length == 1 && waited.result.state.fragments.queues.length == 1 &&
      expired.result.state.fragments.queues.isEmpty && actual.final.fragments.queues.length == 1 &&
      actual.final.conntrack.records.isEmpty)
    "Conntrack erase must retain live IP queues, and expiry must prevent old bytes from completing a later family."
  let backwards ← unwrap (Input.fromJson (← unwrap (changeEvent json 4 (·.setObjVal! "at" (Lean.toJson (1 : Nat))))))
  reject backwards.check "Wait events must reject a backwards clock."

private def wholeLayoutTests (fixture : Lean.Json) : IO Unit := do
  let (source, envelope) ← source fixture
  for df in [false, true] do
    let packet := { source with dontFragment := df }
    let bytes ← unwrap (IPv4.encode packet)
    let split ← populate (← unwrap (base fixture #[fragmentEvent 0 "credential-permitted" "normal" bytes])) envelope
    let splitInput ← unwrap (Input.fromJson split)
    let splitReport ← unwrap splitInput.check
    ensure (!splitReport.compliant)
      "A whole packet that fits its route MTU must reject an artificially split observed family."
    let finding ← element splitReport.findings 0
    let some completed := finding.result.fragment.bind (·.completed) | throw (IO.userError "Expected whole forwarding.")
    let some emission := completed.outcome.output | throw (IO.userError "Expected a whole output packet.")
    let output := Lean.toJson [Import.EAPOL.bytesToHex (Import.EthernetIPv4.encode { envelope with payload := emission.bytes })]
    let whole ← unwrap (changeObserved split 0 (·.setObjVal! "forwarded" output))
    ensure ((← report whole).2) "The same fitting input must accept its single whole output with the source DF flag."

private def parserTests (json : Lean.Json) : IO Unit := do
  reject (Input.fromJson (json.setObjVal! "extra" .null)) "Unknown root fields must fail."
  reject (Input.parse "{\"schema\":1,\"schema\":1}") "Duplicate JSON fields must fail."
  reject (Input.fromJson (← unwrap (changeEvent json 0 (·.setObjVal! "rawIPv4" (.str "0")))))
    "Malformed input hex must fail before replay."
  reject (Input.fromJson (← unwrap (changeEvent json 0 (·.setObjVal! "queuePolicy" (.str "missing")))))
    "Unknown queue policy bindings must fail."
  reject (Input.fromJson (← unwrap (changeEvent json 0 (·.setObjVal! "zone" (Lean.toJson (65536 : Nat))))))
    "Conntrack zone values must fit the native key width."
  let values ← unwrap (events json)
  let raw ← unwrap (values[0]!.getObjVal? "rawIPv4")
  reject (Input.fromJson (← unwrap (changeObserved json 0 (·.setObjVal! "reassembled" raw))))
    "A fragmented post-defragmentation observation is invalid framing for that capture stage."

def run : IO Unit := do
  let fixture ← unwrap (Import.Json.parse (← IO.FS.readFile "examples/icmp/replay.json"))
  let json ← baseTests fixture
  mismatchTests json
  controlTests fixture
  wholeLayoutTests fixture
  parserTests json
  IO.println "IPv4 ingress reassembly forwarding replay tests passed."

end NetlibTest.ReassemblyForwardingCheck
