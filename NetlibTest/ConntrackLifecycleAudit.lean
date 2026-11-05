import Netlib.Check.ConntrackLifecycle

namespace NetlibTest.ConntrackLifecycleAudit

open Netlib Packet Protocol
open Netlib.Check.ConntrackLifecycle

private def unwrap (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error message => throw (IO.userError message)

private def ensure (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def change (json : Lean.Json) : List String → (Lean.Json → Lean.Json) → Except String Lean.Json
  | [], f => .ok (f json)
  | key :: keys, f => do
    match json with
    | .arr values =>
      let some index := key.toNat? | throw "An array mutation requires an index."
      let some old := values[index]? | throw "The array mutation index is missing."
      return .arr (values.set! index (← change old keys f))
    | _ =>
      let old ← json.getObjVal? key
      return json.setObjVal! key (← change old keys f)

private def replace (json : Lean.Json) (path : List String) (value : Lean.Json) : IO Lean.Json :=
  unwrap (change json path (fun _ => value))

private def rejected (json : Lean.Json) (label : String) : IO Unit := do
  match Input.fromJson json with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError s!"Unsupported replay input passed: {label}.")

private def noncompliant (json : Lean.Json) (label : String) : IO Unit := do
  let input ← unwrap (Input.fromJson json)
  let report ← unwrap input.check
  ensure (!report.compliant) s!"An incorrect observation passed: {label}."

private def modelError (json : Lean.Json) (label : String) : IO Unit := do
  let input ← unwrap (Input.fromJson json)
  match input.check with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError s!"An unsupported model execution passed: {label}.")

private def nativeTests (json : Lean.Json) : IO Unit := do
  let input ← unwrap (Input.parse json.compress)
  let report ← unwrap input.check
  ensure (report.compliant && report.findings.length == 10 && input.configs.length == 4)
    "The native replay must cover all ten operations and four selected configurations."
  ensure ((report.findings.filter (·.observation.event.isPacket)).length == 9 &&
    (report.findings.filter (·.observation.event.stateObservation.isSome)).length == 8)
    "The native replay must distinguish packet observations from eight supplied table snapshots."
  ensure (report.final.records.isEmpty && report.findings.all (·.result.state.check))
    "Every modeled prefix must retain ordinary-table validity; deletion must remove the binding."
  let cached ← match report.findings[3]? with
    | none => throw (IO.userError "The cached flow finding is missing.")
    | some finding => pure finding
  let some cachedPacket := cached.result.packet | throw (IO.userError "The cached packet output is missing.")
  ensure (cachedPacket.attachment.classification == StatefulACL.CTState.new && !cachedPacket.attachment.fresh &&
    cachedPacket.output.map (·.sourcePort) == some 40000 && cachedPacket.output.map (·.destinationPort) == some 9000)
    "The unreplied NEW hit must retain its confirmed binding after the NAT table changes."
  let dropped ← match report.findings[4]? with
    | none => throw (IO.userError "The first reply finding is missing.")
    | some finding => pure finding
  ensure (dropped.result.packet.all (·.output.isNone) && dropped.result.state.records.all (·.seenReply))
    "A dropped first valid reply must mark seen-reply before the forward filter."
  let encoded := report.renderJson
  ensure ((encoded.getObjVal? "eventCount").toOption.bind (·.getNat?.toOption) == some 10 &&
    ((encoded.getObjVal? "findings").toOption.bind (·.getArr?.toOption)).map (·.size) == some 10)
    "The rendered report must retain all ordered findings."
  let source ← unwrap ((← unwrap (json.getObjVal? "events")).getArr?)
  let initial ← unwrap (source[2]!.getObjVal? "state")
  let seeded ← replace json ["initial"] initial
  let seeded ← replace seeded ["events"] (.arr #[source[3]!])
  let seededInput ← unwrap (Input.fromJson seeded)
  let seededReport ← unwrap seededInput.check
  ensure (seededReport.compliant && seededInput.initial.records.all (·.entry.flow.remainingTTL == 0))
    "A native initial table must normalize timeout evidence and reuse its existing binding."
  let record ← match seededInput.initial.records with
    | record :: _ => pure record
    | _ => throw (IO.userError "The seeded record is missing.")
  let peer : Protocol.ConntrackLifecycle.Record :=
    { record with entry := { record.entry with flow := { record.entry.flow with
      original := { record.entry.flow.original with sourcePort := 32001 }
      reply := { record.entry.flow.reply with destinationPort := 40002 } } } }
  ensure (sameRecords ⟨[record, peer]⟩ ⟨[peer, record]⟩ && !sameRecords ⟨[record, peer]⟩ ⟨[record]⟩)
    "Stable table comparison must ignore iteration order and detect missing records."

private def observationTests (json : Lean.Json) : IO Unit := do
  for (field, value) in [
    ("classification", Lean.Json.str "established"), ("fresh", Lean.Json.bool false),
    ("afterDestination", Lean.Json.null), ("afterSource", Lean.Json.null),
    ("nextHop", Lean.Json.str "wrong-next-hop"), ("disposition", Lean.Json.str "forwardDrop"),
    ("output", Lean.Json.null)] do
    if field != "afterDestination" then
      noncompliant (← replace json ["events", "2", "observed", field] value) field
  let wrongStage ← replace json ["events", "2", "observed", "afterDestination", "sourcePort"] (Lean.toJson (40000 : Nat))
  noncompliant wrongStage "source NAT applied before the forward filter"
  let changed ← replace json ["events", "3", "observed", "afterDestination", "destinationPort"] (Lean.toJson (9003 : Nat))
  let changed ← replace changed ["events", "3", "observed", "afterSource", "destinationPort"] (Lean.toJson (9003 : Nat))
  let changed ← replace changed ["events", "3", "observed", "afterSource", "sourcePort"] (Lean.toJson (40001 : Nat))
  let changed ← replace changed ["events", "3", "observed", "output", "destinationPort"] (Lean.toJson (9003 : Nat))
  let changed ← replace changed ["events", "3", "observed", "output", "sourcePort"] (Lean.toJson (40001 : Nat))
  noncompliant changed "regenerating a cached NEW binding from changed NAT rules"
  let wrongSeen ← replace json ["events", "4", "state", "entries", "0", "status"] (Lean.toJson (440 : Nat))
  let input ← unwrap (Input.fromJson wrongSeen)
  let report ← unwrap input.check
  ensure (!report.compliant && report.findings[5]?.any (·.passed) && report.findings[6]?.any (·.passed))
    "A false table observation must not overwrite model state or alter later expectations."
  let wrongTuple ← replace json ["events", "3", "state", "entries", "0", "reply", "destinationPort"] (Lean.toJson (40002 : Nat))
  noncompliant wrongTuple "incorrect stored reply tuple"
  let ignored ← replace json ["events", "3", "state", "entries", "0", "remainingTTL"] (Lean.toJson (4294967295 : Nat))
  let ignored ← replace ignored ["events", "3", "state", "entries", "0", "id"] (Lean.toJson (4294967295 : Nat))
  let ignored ← replace ignored ["events", "3", "state", "entries", "0", "status"] (Lean.toJson (444 : Nat))
  let input ← unwrap (Input.fromJson ignored)
  ensure (← unwrap input.check).compliant
    "Timeout, native ID, and accepted unrelated status metadata must not change stable tuple agreement."
  let unobserved ← replace json ["events", "4", "state"] .null
  let input ← unwrap (Input.fromJson unobserved)
  let report ← unwrap input.check
  ensure (report.compliant && (report.findings.filter (·.observation.event.stateObservation.isSome)).length == 7)
    "A null table observation must stay unobserved while the modeled state still advances."

private def inputTests (json : Lean.Json) : IO Unit := do
  for (path, value) in [
    (["schema"], Lean.toJson (2 : Nat)), (["routing", "version"], Lean.Json.str "6.18.0"),
    (["configs", "1", "id"], Lean.Json.str "initial"),
    (["events", "0", "config"], Lean.Json.str "unknown"),
    (["events", "0", "zone"], Lean.toJson (65536 : Nat)),
    (["events", "0", "packet", "protocol"], Lean.toJson (256 : Nat)),
    (["events", "0", "packet", "sourcePort"], Lean.toJson (65536 : Nat)),
    (["events", "0", "observed", "classification"], Lean.Json.str "unknown"),
    (["events", "0", "observed", "fresh"], Lean.toJson (1 : Nat)),
    (["events", "0", "observed", "disposition"], Lean.Json.str "confirmed"),
    (["configs", "0", "forward", "nftables", "2", "chain", "hook"], Lean.Json.str "postrouting"),
    (["configs", "0", "late", "nftables", "2", "chain", "hook"], Lean.Json.str "forward"),
    (["configs", "0", "late", "nftables", "2", "chain", "prio"], Lean.toJson (100 : Nat)),
    (["configs", "0", "late", "nftables", "2", "chain", "prio"], Lean.toJson (2147483647 : Nat)),
    (["configs", "0", "nat", "nftables", "2", "chain", "prio"], Lean.toJson (-99 : Int))
  ] do rejected (← replace json path value) (String.intercalate "/" path)
  for path in [[], ["routing"], ["routing", "bindings", "0"], ["configs", "0"],
    ["events", "0"], ["events", "0", "observed"], ["events", "0", "packet"]] do
    let mutated ← unwrap (change json path (fun node => node.setObjVal! "unexpected" .null))
    rejected mutated "unknown field"
  for key in ["candidate", "authorized"] do
    let mutated ← unwrap (change json ["events", "0"] (fun node => node.setObjVal! key (.bool true)))
    rejected mutated s!"caller-supplied {key}"
  let events ← unwrap ((← unwrap (json.getObjVal? "events")).getArr?)
  rejected (← replace json ["events"] (.arr #[events[8]!])) "no packet events"
  let duplicate := "{\"schem\\u0061\":1," ++ (json.compress.drop 1).toString
  match Input.parse duplicate with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "Duplicate decoded JSON keys must fail.")
  modelError (← replace json ["events", "0", "packet", "protocol"] (Lean.toJson (1 : Nat)))
    "unsupported transport"
  let row ← unwrap (events[2]!.getObjVal? "state")
  let collision ← replace row ["entries", "0", "original", "sourcePort"] (Lean.toJson (32001 : Nat))
  let collision ← replace json ["initial"] collision
  let collision ← replace collision ["events"] (.arr #[events[2]!])
  modelError collision "late confirmation collision"

example (report : Report routing initial observations) :
    report.findings.map Finding.observation = observations := report.covered

example (report : Report routing initial observations) :
    report.compliant = true ↔ Agreement routing initial observations := report.compliant_iff

example (report : Report routing initial observations) (valid : initial.Valid) :
    report.final.Valid ∧ ∀ finding ∈ report.findings, finding.result.state.Valid := report.prefixes_valid valid

def run : IO Unit := do
  let json ← unwrap (Import.Json.parse (← IO.FS.readFile "examples/lifecycle/replay.json"))
  nativeTests json
  observationTests json
  inputTests json
  IO.println "Tracked lifecycle replay audit tests passed."

end NetlibTest.ConntrackLifecycleAudit
