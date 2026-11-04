import Netlib.Import.Conntrack
import Netlib.Import.ConntrackNetlink
import Netlib.Compile.Policy

/-!
# Policy checks for reported original flows

The report covers the supplied visible records.
It does not infer firewall admission or complete kernel state from a dump.
-/

namespace Netlib.Check.Conntrack

open Packet Protocol

structure Row where
  source : String
  flow : FlowNAT.Entry
  status : Option Nat
  id : Option Nat
  line : Option Nat
  deriving Repr, DecidableEq

inductive Snapshot where
  | xml (snapshot : Import.Conntrack.Snapshot)
  | netlink (snapshot : Import.ConntrackNetlink.Snapshot)

def Snapshot.parse (text : String) : Except String Snapshot :=
  if text.trimAscii.toString.startsWith "<" then .xml <$> Import.Conntrack.Snapshot.parse text
  else .netlink <$> Import.ConntrackNetlink.Snapshot.parse text

def Snapshot.format : Snapshot → String
  | .xml _ => "conntrack-xml"
  | .netlink _ => "conntrack-netlink-json"

def Snapshot.rows : Snapshot → List Row
  | .xml snapshot => snapshot.entries.map fun row =>
    ⟨row.sourcePath, row.entry, none, row.metadata.id, some row.line⟩
  | .netlink snapshot => snapshot.entries.map fun row =>
    ⟨row.sourcePath, row.entry.flow, some row.status, row.id, none⟩

structure Finding where
  row : Row
  passed : Bool

structure Report (intents : List Compile.ACL.Intent) (rows : List Row) where
  findings : List Finding
  covered : findings.map Finding.row = rows
  correct : findings.all Finding.passed = true ↔
    ∀ row ∈ rows, Compile.ACL.Meaning intents row.flow.original

def audit (compiled : Compile.ACL.Certified intents) (rows : List Row) : Report intents rows :=
  { findings := rows.map fun row => ⟨row, compiled.rules.allows row.flow.original⟩
    covered := by simp only [List.map_map, Function.comp_def]; exact List.map_id rows
    correct := by
      simp only [List.all_map, Function.comp_def, List.all_eq_true]
      exact forall_congr' fun row => imp_congr_right fun _ => compiled.correct row.flow.original }

def Report.compliant (report : Report intents rows) : Bool := report.findings.all Finding.passed

theorem Report.compliant_iff (report : Report intents rows) :
    report.compliant = true ↔ ∀ row ∈ rows, Compile.ACL.Meaning intents row.flow.original := report.correct

structure Input where
  snapshot : Snapshot
  intents : List Compile.ACL.Intent
  compiled : Compile.ACL.Certified intents

def Input.parse (snapshot policy : String) (budget : Nat := 100000) : Except String Input := do
  let snapshot ← Snapshot.parse snapshot
  let intents ← Compile.Policy.parse policy
  let compiled ← (Compile.ACL.compile intents budget).mapError (·.describe)
  return ⟨snapshot, intents, compiled⟩

def Input.check (input : Input) : Report input.intents input.snapshot.rows :=
  audit input.compiled input.snapshot.rows

private def rowJson (row : Row) (passed : Bool) : Lean.Json :=
  Lean.Json.mkObj [
    ("source", Lean.toJson row.source), ("line", Lean.toJson row.line),
    ("original", Import.PacketFields.headerJson row.flow.original),
    ("reply", Import.PacketFields.headerJson row.flow.reply),
    ("originalZone", Lean.toJson row.flow.originalZone), ("replyZone", Lean.toJson row.flow.replyZone),
    ("remainingSeconds", Lean.toJson row.flow.remainingTTL), ("nativeStatus", Lean.toJson row.status),
    ("nativeId", Lean.toJson row.id), ("permittedByIntent", Lean.toJson passed)]

def renderJson (input : Input) (report : Report input.intents input.snapshot.rows) : Lean.Json :=
  Lean.Json.mkObj [
    ("compliant", Lean.toJson report.compliant), ("scope", Lean.toJson "reported-original-flow-policy"),
    ("format", Lean.toJson input.snapshot.format), ("entryCount", Lean.toJson input.snapshot.rows.length),
    ("requirements", Lean.toJson input.compiled.requirementIds),
    ("findings", Lean.toJson (report.findings.map fun finding => rowJson finding.row finding.passed))]

def render (input : Input) (report : Report input.intents input.snapshot.rows) : String :=
  String.intercalate "\n" ((if report.compliant then "COMPLIANT" else "NONCOMPLIANT") ::
    "Scope: reported original flow tuples under the declared packet intent." ::
    s!"Format: {input.snapshot.format}; entries: {input.snapshot.rows.length}." ::
    report.findings.map fun finding =>
      s!"{finding.row.source}: {if finding.passed then "permitted" else "not permitted"}; " ++
      (Import.PacketFields.headerJson finding.row.flow.original).compress)

/-- This reports a frozen association, not whether Linux will admit the packet. -/
def mapPacket (text : String) (zone : Nat) (packet : Header) : Except String (Bool × Lean.Json) := do
  if zone ≥ 65536 then throw "A conntrack zone must fit in 16 bits."
  let snapshot ← Import.ConntrackNetlink.Snapshot.parse text
  let found := snapshot.model.lookup zone packet
  let source := found.bind fun hit => snapshot.entries.find? (fun row => row.entry.flow == hit.entry)
  if found.isSome && source.isNone then throw "The conntrack lookup lost its source record."
  return (found.isSome, Lean.Json.mkObj [
    ("associated", Lean.toJson found.isSome), ("scope", Lean.toJson "frozen-full-status-tuple-projection"),
    ("zone", Lean.toJson zone), ("input", Import.PacketFields.headerJson packet),
    ("output", Import.PacketFields.optionalHeaderJson (found.map FlowNAT.Hit.output)),
    ("source", Lean.toJson (source.map (·.sourcePath))),
    ("nativeStatus", Lean.toJson (source.map (·.status))),
    ("direction", Lean.toJson (found.map fun hit => match hit.direction with
      | .original => "original" | .reply => "reply"))])

end Netlib.Check.Conntrack
