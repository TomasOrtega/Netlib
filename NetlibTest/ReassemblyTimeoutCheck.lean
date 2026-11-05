import Netlib.Check.ReassemblyTimeout

namespace NetlibTest.ReassemblyTimeoutCheck

open Netlib Packet Protocol Check.ReassemblyTimeout

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

private def object := Lean.Json.mkObj
private def number (value : Nat) := Lean.toJson value

private def controlPolicy (code : Nat := 1) (state : Nat := 1) : Lean.Json := object [("nftables", Lean.toJson [
  object [("metainfo", object [("version", .str "1.1.3"), ("release_name", .str "Commodore Bullmoose #4"), ("json_schema_version", number 1)])],
  object [("table", object [("family", .str "ip"), ("name", .str "reassembly_timeout"), ("handle", number 4)])],
  object [("chain", object [("family", .str "ip"), ("table", .str "reassembly_timeout"), ("name", .str "output"),
    ("handle", number 1), ("type", .str "filter"), ("hook", .str "output"), ("prio", number 0), ("policy", .str "drop")])],
  object [("rule", object [("family", .str "ip"), ("table", .str "reassembly_timeout"), ("chain", .str "output"),
    ("handle", number 2), ("expr", Lean.toJson [
      object [("match", object [("op", .str "=="), ("left", object [("payload", object [("protocol", .str "icmp"), ("field", .str "type")])]), ("right", number 11)])],
      object [("match", object [("op", .str "=="), ("left", object [("payload", object [("protocol", .str "icmp"), ("field", .str "code")])]), ("right", number code)])],
      object [("match", object [("op", .str "in"), ("left", object [("ct", object [("key", .str "state")])]), ("right", number state)])],
      object [("counter", object [("packets", number 1), ("bytes", number 576)])], object [("accept", .null)]])])]])]

private def first (size : Nat) (offset : Nat := 0) (protocol : Packet.Protocol := Packet.Protocol.udp) : IPv4Fragment.Packet :=
  ⟨⟨0, 41229, false, 64, protocol, 3221225986, 3405803778, List.range size |>.map UInt8.ofNat⟩,
    true, ⟨offset % 8192, Nat.mod_lt _ (by decide)⟩⟩

private def frameBytes (packet : IPv4.Packet) : Except String (List UInt8) := do
  let envelope ← Import.EAPOL.bytesFromHex "02000000ea0202000000ea010800"
  return envelope ++ (← IPv4.encode packet)

private def expectedPacket (fragment : IPv4Fragment.Packet) (mtu : Nat) (identification : InternetChecksum.Word := 73)
    (kind : ICMP.Kind := .reassemblyTimeout) : IPv4.Packet :=
  let normalized := fragment.payload.take (fragment.payload.length / 8 * 8)
  let stored := IPv4Fragment.headerBytes fragment (IPv4Fragment.computedChecksum fragment) ++ normalized
  let quote := stored.take (min (normalized.length + 20) (min mtu 576 - 28))
  ⟨192, identification, false, 64, Packet.Protocol.icmp, fragment.destination, fragment.source, ICMP.encode ⟨kind, quote⟩⟩

private def baseJSON (fixture : Lean.Json) (fragment : IPv4Fragment.Packet) : Except String Lean.Json := do
  let fields ← ["schema", "routing", "mtus"].mapM fun key => do return (key, ← fixture.getObjVal? key)
  let configs ← (← (← fixture.getObjVal? "configs").getArr?).toList.mapM fun config => do
    let selected ← ["id", "forward", "late", "nat"].mapM fun key => do return (key, ← config.getObjVal? key)
    return object selected
  let raw ← IPv4InputFragment.encode fragment
  let event := object [("type", .str "fragment"), ("at", number 0), ("config", .str "credential-permitted"),
    ("queuePolicy", .str "short"), ("zone", number 0), ("vif", number 0),
    ("rawIPv4", .str (Import.EAPOL.bytesToHex raw)), ("observed", object [("reassembled", .null), ("forwarded", .arr #[])]), ("state", .null)]
  return object (fields ++ [("configs", Lean.toJson configs), ("initial", .null),
    ("reassembly", object [("userBase", number 2), ("policies", Lean.toJson [object [("id", .str "short"), ("timeout", number 10)]])]),
    ("events", Lean.toJson [event, object [("type", .str "wait"), ("at", number 10), ("state", .null)],
      object [("type", .str "wait"), ("at", number 11), ("state", .null)]])])

private def allocation (identifier : Nat := 41229) (outer : Nat := 73) : Lean.Json := object [
  ("key", object [("zone", number 0), ("vif", number 0), ("source", .str "192.0.2.2"),
    ("destination", .str "203.0.113.2"), ("protocol", number 17), ("identification", number identifier)]),
  ("identification", number outer)]

private def contextJSON (fixture : Lean.Json) (mtu : Nat) : Except String Lean.Json := do
  let configs ← (← fixture.getObjVal? "configs").getArr?
  let late ← configs[0]!.getObjVal? "late"
  return object [("id", .str "local"),
    ("inputRoutes", Lean.toJson [object [("destination", .str "203.0.113.2"), ("local", .bool true)]]),
    ("returns", Lean.toJson [object [("destination", .str "192.0.2.2"), ("nextHop", .str "peer"),
      ("source", .str "203.0.113.2"), ("mtu", number mtu), ("ttl", number 64)]]),
    ("output", controlPolicy), ("late", late), ("broadcasts", .arr #[])]

private def wrapper (fixture : Lean.Json) (size mtu : Nat) : Except String Lean.Json := do
  let fragment := first size
  let bytes ← frameBytes (expectedPacket fragment mtu)
  let controls := [0, 1, 2].map fun index => object [("event", number index), ("context", .str "local"),
    ("identifications", if index == 1 then Lean.toJson [allocation] else .arr #[]),
    ("observed", if index == 1 then Lean.toJson [Import.EAPOL.bytesToHex bytes] else .arr #[])]
  return object [("schema", number 1), ("forwarding", ← baseJSON fixture fragment),
    ("contexts", Lean.toJson [← contextJSON fixture mtu]), ("controls", Lean.toJson controls)]

private def changeControl (json : Lean.Json) (index : Nat) (change : Lean.Json → Lean.Json) : Except String Lean.Json := do
  let controls ← (← json.getObjVal? "controls").getArr?
  return json.setObjVal! "controls" (.arr (controls.set! index (change controls[index]!)))

private def changeContext (json : Lean.Json) (change : Lean.Json → Lean.Json) : Except String Lean.Json := do
  let contexts ← (← json.getObjVal? "contexts").getArr?
  return json.setObjVal! "contexts" (.arr (contexts.set! 0 (change contexts[0]!)))

private def omitControl (json : Lean.Json) : Except String Lean.Json :=
  changeControl json 1 (fun control => control.setObjVal! "identifications" (.arr #[]) |>.setObjVal! "observed" (.arr #[]))

private def resultAt (report : Report environment initial observations) (index : Nat) : IO Finding :=
  match report.findings[index]? with
  | some finding => pure finding
  | none => throw (IO.userError "Expected a timeout replay finding.")

example (report : Report environment initial observations) :
    report.compliant = true ↔ Agreement environment initial observations := report.compliant_iff

example (report : Report environment initial observations) (valid : initial.fragments.LayoutValid) :
    report.final.fragments.LayoutValid ∧ ∀ finding ∈ report.findings, finding.result.state.fragments.LayoutValid := report.queue_layout valid

private def quotationTests (fixture : Lean.Json) : IO Lean.Json := do
  for size in [11, 576] do
    for mtu in [68, 600] do
      let input ← unwrap (Input.fromJson (← unwrap (wrapper fixture size mtu)))
      let report ← unwrap input.check
      let initialFinding ← resultAt report 0
      let expired ← resultAt report 1
      let later ← resultAt report 2
      ensure (report.compliant && initialFinding.result.state.fragments.queues.length == 1 &&
          initialFinding.result.expiration.findings.isEmpty && expired.result.state.fragments.queues.isEmpty &&
          expired.result.expiration.findings.length == 1 && later.result.expiration.findings.isEmpty &&
          report.final.conntrack.records.isEmpty)
        "Only an expired live queue may emit once, without changing ordinary conntrack state."
      let some selected := expired.result.expiration.findings.head? | throw (IO.userError "Expected an expired queue.")
      let some emission := selected.control.output | throw (IO.userError "Expected a computed timeout emission.")
      ensure (selected.control.classification == some .invalid && emission.packet.wireLength ==
          (if size == 11 then 56 else if mtu == 68 then 68 else 576) &&
          emission.quote.flags.val == 8192 && emission.quote.declaredLength.val == size + 20 &&
          emission.quote.checksum == IPv4Fragment.computedChecksum (first size))
        "Timeout errors must use code one and retain the original fragmented header, including odd declared lengths."
  unwrap (wrapper fixture 576 600)

private def mismatchTests (json : Lean.Json) : IO Unit := do
  let input ← unwrap (Input.fromJson json)
  let original ← unwrap input.check
  let correct := expectedPacket (first 576) 600
  let quote ← unwrap (ICMP.decode correct.payload)
  let alteredQuote := (quote.message.quote.toArray.modify 10 (· + 1)).toList
  let quotePacket := { correct with payload := ICMP.encode { quote.message with quote := alteredQuote } }
  let altered : List IPv4.Packet := [
    { correct with identification := 74 }, { correct with ttl := 63 }, quotePacket,
    expectedPacket (first 576) 600 73 .timeExceeded]
  let frames ← altered.mapM fun packet => do return Import.EAPOL.bytesToHex (← unwrap (frameBytes packet))
  let correctHex := Import.EAPOL.bytesToHex (← unwrap (frameBytes correct))
  let outputs := frames.map (fun value => Lean.toJson [value]) ++ [.arr #[], Lean.toJson [correctHex, correctHex]]
  for observed in outputs do
    let selected ← unwrap (Input.fromJson (← unwrap (changeControl json 1 (·.setObjVal! "observed" observed))))
    let report ← unwrap selected.check
    ensure (!report.compliant && report.final.conntrack == original.final.conntrack &&
        report.final.fragments == original.final.fragments && (← resultAt report 2).passed)
      "Wrong kind, ID, quoted bytes, TTL, or output multiplicity must mismatch without changing later state."
  let wrongID ← unwrap (Input.fromJson (← unwrap (changeControl json 1
    (·.setObjVal! "identifications" (Lean.toJson [allocation 41229 74])))))
  ensure (!(← unwrap wrongID.check).compliant) "An allocator ID must match the observed outer identification."

private def suppressionTests (fixture json : Lean.Json) : IO Unit := do
  let noOutput ← unwrap (omitControl json)
  let contexts : List (Lean.Json → Lean.Json) := [
    fun context => context.setObjVal! "inputRoutes" (Lean.toJson [object [("destination", .str "203.0.113.2"), ("local", .bool false)]]),
    fun context => context.setObjVal! "inputRoutes" (.arr #[]),
    fun context => context.setObjVal! "returns" (.arr #[]),
    fun context => context.setObjVal! "output" (controlPolicy 0),
    fun context => context.setObjVal! "output" (controlPolicy 1 4)]
  for change in contexts do
    let input ← unwrap (Input.fromJson (← unwrap (changeContext noOutput change)))
    ensure ((← unwrap input.check).compliant)
      "Locality, absent routes, wrong ICMP code guards, and related-only policy must suppress the selected INVALID error."
  let noninitial ← unwrap (baseJSON fixture (first 576 1))
  let noFirst ← unwrap (Input.fromJson (noOutput.setObjVal! "forwarding" noninitial))
  let result ← unwrap noFirst.check
  ensure (result.compliant && ((← resultAt result 1).result.expiration.findings.map (·.control.disposition)) == [.noFirst])
    "A family without offset zero must expire without an error or identification allocation."
  let contexts ← unwrap ((← unwrap (json.getObjVal? "contexts")).getArr?)
  let late ← unwrap (contexts[0]!.getObjVal? "late")
  let objects ← unwrap ((← unwrap (late.getObjVal? "nftables")).getArr?)
  let chain ← unwrap (objects[2]!.getObjVal? "chain")
  let deniedLate := late.setObjVal! "nftables" (.arr (objects.set! 2 (object [("chain", chain.setObjVal! "policy" (.str "drop"))])))
  let lateInput ← unwrap (Input.fromJson (← unwrap (changeContext noOutput (·.setObjVal! "late" deniedLate))))
  let lateReport ← unwrap lateInput.check
  ensure (lateReport.compliant && ((← resultAt lateReport 1).result.expiration.findings.map (·.control.disposition)) == [.lateDrop])
    "The late INVALID filter must independently gate a timeout permitted by the output chain."

private def multipleTests (fixture : Lean.Json) : IO Unit := do
  let firstPacket := first 576
  let secondPacket := { firstPacket with identification := 41230 }
  let base ← unwrap (baseJSON fixture firstPacket)
  let events ← unwrap ((← unwrap (base.getObjVal? "events")).getArr?)
  let raw ← unwrap (IPv4InputFragment.encode secondPacket)
  let secondEvent := events[0]!.setObjVal! "at" (number 1) |>.setObjVal! "rawIPv4" (.str (Import.EAPOL.bytesToHex raw))
  let forwarding := base.setObjVal! "events" (Lean.toJson [events[0]!, secondEvent,
    events[1]!.setObjVal! "at" (number 11), events[2]!.setObjVal! "at" (number 12)])
  let observed ← [expectedPacket firstPacket 600, expectedPacket secondPacket 600 74].mapM fun packet => do
    return Import.EAPOL.bytesToHex (← unwrap (frameBytes packet))
  let controls := [0, 1, 2, 3].map fun index => object [("event", number index), ("context", .str "local"),
    ("identifications", if index == 2 then Lean.toJson [allocation, allocation 41230 74] else .arr #[]),
    ("observed", if index == 2 then Lean.toJson observed else .arr #[])]
  let json := object [("schema", number 1), ("forwarding", forwarding),
    ("contexts", Lean.toJson [← unwrap (contextJSON fixture 600)]), ("controls", Lean.toJson controls)]
  let input ← unwrap (Input.fromJson json)
  let report ← unwrap input.check
  ensure (report.compliant && (← resultAt report 2).result.expiration.findings.length == 2 &&
      report.final.fragments.queues.isEmpty && report.final.conntrack.records.isEmpty)
    "Every expired key needs one allocation and one observed error, independent of capture order."

private def zeroRepresentationTests (fixture json : Lean.Json) : IO Unit := do
  let original := expectedPacket (first 576) 600
  let value := (original.identification.val + (IPv4.computedChecksum original).val) % 65535
  let identification : InternetChecksum.Word := ⟨value, by have := Nat.mod_lt (original.identification.val + (IPv4.computedChecksum original).val) (by decide : 0 < 65535); omega⟩
  let selected := { original with identification }
  ensure (IPv4.computedChecksum selected == 0) "The synthetic outer header must have checksum zero."
  let bytes ← unwrap (IPv4.encode selected)
  let alternative := (bytes.toArray.set! 10 255 |>.set! 11 255).toList
  let ethernet ← unwrap (Import.EAPOL.bytesFromHex "02000000ea0202000000ea010800")
  let changed ← unwrap (changeControl json 1 fun control =>
    control.setObjVal! "identifications" (Lean.toJson [allocation 41229 identification.val])
      |>.setObjVal! "observed" (Lean.toJson [Import.EAPOL.bytesToHex (ethernet ++ alternative)]))
  let input ← unwrap (Input.fromJson changed)
  ensure ((← unwrap input.check).compliant) "Validated outer IPv4 zero checksum representations must compare equally."
  let basePacket := first 576
  let initialMessage ← unwrap (ICMP.decode original.payload)
  let value := (1 + (ICMP.computedChecksum initialMessage.message).val) % 65535
  let word : InternetChecksum.Word := ⟨value, by have := Nat.mod_lt (1 + (ICMP.computedChecksum initialMessage.message).val) (by decide : 0 < 65535); omega⟩
  let fragment := { basePacket with payload := InternetChecksum.wordBytes word ++ basePacket.payload.drop 2 }
  let packet := expectedPacket fragment 600
  let control ← unwrap (ICMP.decode packet.payload)
  ensure (control.checksum == 0) "The synthetic ICMP message must have checksum zero."
  let bytes ← unwrap (IPv4.encode packet)
  let alternative := (bytes.toArray.set! 22 255 |>.set! 23 255).toList
  let changed := json.setObjVal! "forwarding" (← unwrap (baseJSON fixture fragment))
  let changed ← unwrap (changeControl changed 1 (·.setObjVal! "observed"
    (Lean.toJson [Import.EAPOL.bytesToHex (ethernet ++ alternative)])))
  let input ← unwrap (Input.fromJson changed)
  ensure ((← unwrap input.check).compliant) "Validated ICMP zero checksum representations must not change exact quote comparison."

private def parserTests (fixture json : Lean.Json) : IO Unit := do
  reject (Input.fromJson (json.setObjVal! "extra" .null)) "Unknown timeout root fields must fail."
  reject (Input.fromJson (json.setObjVal! "controls" (.arr #[]))) "Every forwarding event needs one timeout binding."
  reject (Input.fromJson (← unwrap (changeControl json 1 (·.setObjVal! "event" (number 2)))))
    "Timeout control order must follow forwarding event order."
  reject (Input.fromJson (← unwrap (changeControl json 1 (·.setObjVal! "identifications" (Lean.toJson [allocation, allocation])))))
    "Duplicate allocator keys must fail before replay."
  let unknown ← unwrap (Input.fromJson (← unwrap (changeControl json 1
    (·.setObjVal! "identifications" (Lean.toJson [allocation 41230])))))
  reject unknown.check "An allocator key must identify an actually sent expired queue."
  let missing ← unwrap (Input.fromJson (← unwrap (changeControl json 1 (·.setObjVal! "identifications" (.arr #[])))))
  reject missing.check "A sent timeout requires an explicit allocator choice."
  let unsupported ← unwrap (Input.fromJson (json.setObjVal! "forwarding" (← unwrap (baseJSON fixture (first 576 0 Packet.Protocol.tcp)))))
  reject unsupported.check "An unsupported first-fragment transport must not be reported as a native drop."

private def trackerTests (json : Lean.Json) : IO Unit := do
  let input ← unwrap (Input.fromJson json)
  let original : Header := ⟨3221225986, 3405803778, Packet.Protocol.udp, 1, 515⟩
  let entry : NetfilterNAT.Entry := ⟨⟨original, original.reverse, 0, 0, 0⟩, false, false⟩
  let associated : ConntrackLifecycle.State := ⟨[⟨entry, false⟩]⟩
  if valid : associated.check = true then
    let forwarding := { input.forwarding with
      initial := ⟨.initial, associated⟩
      initialValid := (ConntrackLifecycle.State.check_correct _).mp valid }
    let selected : Input := { input with forwarding }
    reject selected.check "A reverse-quote association must leave the selected unassociated timeout profile."
  else throw (IO.userError "The synthetic identity conntrack record must be valid.")
  let wire := { original with source := 3405803777, destination := 3325256706, sourcePort := 40000, destinationPort := 9000 }
  let nated : NetfilterNAT.Entry := ⟨⟨original, wire.reverse, 0, 0, 0⟩, true, true⟩
  let tracker : ConntrackLifecycle.State := ⟨[⟨nated, true⟩]⟩
  if valid : tracker.check = true then
    let forwarding := { input.forwarding with
      initial := ⟨.initial, tracker⟩
      initialValid := (ConntrackLifecycle.State.check_correct _).mp valid }
    let selected : Input := { input with forwarding }
    let report ← unwrap selected.check
    ensure (report.compliant && report.final.conntrack == tracker)
      "Timeout generation must preserve an existing NATed flow when the pre-DNAT reverse quote has no association."
  else throw (IO.userError "The synthetic NATed conntrack record must be valid.")
  let some observation := input.events[1]? | throw (IO.userError "Expected an expiry observation.")
  let fragment := first 576
  let before ← match IPv4Reassembly.arrive ⟨10⟩ .initial 0 ⟨1, 0⟩
      ⟨fragment, IPv4Fragment.computedChecksum fragment, []⟩ with
    | .error error => throw (IO.userError error.describe)
    | .ok result => pure ({ fragments := result.state, conntrack := .initial } : Core.State)
  reject (step input.forwarding.environment before observation)
    "A queue outside the configured effective-user zone range must be unsupported."

private def inheritedZoneTests (json : Lean.Json) : IO Unit := do
  let forwarding ← unwrap (json.getObjVal? "forwarding")
  let events ← unwrap ((← unwrap (forwarding.getObjVal? "events")).getArr?)
  let forwarding := forwarding.setObjVal! "events" (.arr (events.set! 0 (events[0]!.setObjVal! "zone" (number 10))))
  let entry := allocation
  let key ← unwrap (entry.getObjVal? "key")
  let entry := entry.setObjVal! "key" (key.setObjVal! "zone" (number 10))
  let changed ← unwrap (changeControl (json.setObjVal! "forwarding" forwarding) 1
    (·.setObjVal! "identifications" (Lean.toJson [entry])))
  let input ← unwrap (Input.fromJson changed)
  let original : Header := ⟨3221225986, 3405803778, Packet.Protocol.udp, 1, 515⟩
  for zone in [0, 10] do
    let entry : NetfilterNAT.Entry := ⟨⟨original, original.reverse, zone, zone, 0⟩, false, false⟩
    let tracker : ConntrackLifecycle.State := ⟨[⟨entry, false⟩]⟩
    if valid : tracker.check = true then
      let forwarding := { input.forwarding with
        initial := ⟨.initial, tracker⟩
        initialValid := (ConntrackLifecycle.State.check_correct _).mp valid }
      let selected : Input := { input with forwarding }
      if zone == 0 then
        let report ← unwrap selected.check
        ensure (report.compliant && report.final.conntrack == tracker &&
            ((← resultAt report 1).result.expiration.findings.map (·.control.classification)) == [some .invalid])
          "A zone-ten queue must inherit zone ten and miss an identical untranslated flow stored only in zone zero."
      else
        let some head := selected.events[0]? | throw (IO.userError "Expected the zone-ten fragment.")
        let some expiry := selected.events[1]? | throw (IO.userError "Expected the zone-ten expiry.")
        let before ← unwrap (step selected.forwarding.environment selected.forwarding.initial head)
        let expired ← match Timeout.expire (expiry.context.model selected.forwarding.environment.userBase)
            before.state.conntrack before.state.fragments (eventTime expiry.base.event) expiry.identification with
          | .error error => throw (IO.userError error.describe)
          | .ok result => pure result
        ensure (before.state.conntrack == tracker && expired.conntrack == tracker &&
            expired.findings.all (fun finding => finding.control.disposition == .unsupportedAssociation))
          "Inherited-zone association must preserve the table while identifying an unsupported related error."
        reject selected.check "The zone-ten reverse-quote hit must not be misclassified as an INVALID-zone-zero miss."
    else throw (IO.userError "The synthetic scoped conntrack record must be valid.")

def run : IO Unit := do
  let fixture ← unwrap (Import.Json.parse (← IO.FS.readFile "examples/icmp/replay.json"))
  let json ← quotationTests fixture
  mismatchTests json
  suppressionTests fixture json
  multipleTests fixture
  zeroRepresentationTests fixture json
  parserTests fixture json
  trackerTests json
  inheritedZoneTests json
  IO.println "IPv4 reassembly timeout replay checks passed."

end NetlibTest.ReassemblyTimeoutCheck
