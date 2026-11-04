import Lean

namespace Netlib.Standards

/-- A source records the exact document version and clause. -/
structure Source where
  document : String
  version : String
  clause : String
  url : String
  deriving Repr, BEq, DecidableEq

/-- A requirement records its meaning, scope, and assumptions. -/
structure Requirement where
  id : String
  source : Source
  statement : String
  applicability : String
  assumptions : List String := []
  deriving Repr, BEq

/-- Missing evidence and unsupported checks must remain visible. -/
inductive Status where
  | satisfied
  | violated
  | unsupported
  | missingEvidence
  | notApplicable
  deriving Repr, BEq, DecidableEq

namespace Status

def render : Status → String
  | .satisfied => "satisfied"
  | .violated => "violated"
  | .unsupported => "unsupported"
  | .missingEvidence => "missing evidence"
  | .notApplicable => "not applicable"

def passes (status : Status) : Bool :=
  decide (status = .satisfied) || decide (status = .notApplicable)

@[simp] theorem passes_iff (status : Status) :
    status.passes = true ↔ status = .satisfied ∨ status = .notApplicable := by
  cases status <;> simp [passes]

end Status

/-- Each finding preserves the requirement and its source. -/
structure Finding where
  requirement : Requirement
  status : Status
  evidence : List String
  deriving Repr

/-- A report covers one named profile. -/
structure Report where
  profile : String
  findings : List Finding
  deriving Repr

namespace Report

def compliant (report : Report) : Bool :=
  !report.findings.isEmpty && report.findings.all (·.status.passes)

def complete (report : Report) : Bool :=
  report.findings.all (fun f => f.status != .unsupported && f.status != .missingEvidence)

theorem compliant_status (report : Report) (passed : report.compliant = true)
    (finding : Finding) (member : finding ∈ report.findings) :
    finding.status = .satisfied ∨ finding.status = .notApplicable := by
  have both := passed
  simp only [compliant, Bool.and_eq_true] at both
  have all : report.findings.all (·.status.passes) = true := both.2
  exact Status.passes_iff finding.status |>.mp ((List.all_eq_true.mp all) finding member)

def render (report : Report) : String :=
  String.intercalate "\n" (
    [report.profile, if report.compliant then "PROFILE SATISFIED" else "PROFILE NOT SATISFIED"] ++
    report.findings.flatMap (fun finding =>
      [s!"{finding.status.render}: {finding.requirement.id}: {finding.requirement.statement}",
       s!"  source: {finding.requirement.source.document} {finding.requirement.source.version}, {finding.requirement.source.clause}",
       s!"  link: {finding.requirement.source.url}",
       s!"  scope: {finding.requirement.applicability}"] ++
      finding.requirement.assumptions.map ("  assumption: " ++ ·) ++
      finding.evidence.map ("  evidence: " ++ ·)))

def renderJson (report : Report) : Lean.Json :=
  Lean.Json.mkObj [
    ("profile", Lean.toJson report.profile),
    ("compliant", Lean.toJson report.compliant),
    ("complete", Lean.toJson report.complete),
    ("findings", Lean.toJson (report.findings.map fun finding => Lean.Json.mkObj [
      ("id", Lean.toJson finding.requirement.id),
      ("status", Lean.toJson finding.status.render),
      ("statement", Lean.toJson finding.requirement.statement),
      ("applicability", Lean.toJson finding.requirement.applicability),
      ("assumptions", Lean.toJson finding.requirement.assumptions),
      ("source", Lean.Json.mkObj [
        ("document", Lean.toJson finding.requirement.source.document),
        ("version", Lean.toJson finding.requirement.source.version),
        ("clause", Lean.toJson finding.requirement.source.clause),
        ("url", Lean.toJson finding.requirement.source.url)]),
      ("evidence", Lean.toJson finding.evidence)]))]

end Report
end Netlib.Standards
