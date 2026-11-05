import Netlib.Check.ConntrackRevocation
import Netlib.Protocol.BufferedLifecycle

/-!
# Buffered lifecycle replay

The schedule consumes every lifecycle operation in order and interleaves declared FIFO service.
Only computed operation outputs enter the queue. Observations do not replace model state.
Queue completeness, service interpretation, and native correspondence remain assumptions.
-/

namespace Netlib.Check.BufferedReplay

open Packet
abbrev BufferedState := Protocol.BufferedLifecycle.State
abbrev BufferedResult := Protocol.BufferedLifecycle.Result

inductive Event where
  | operation (source : ConntrackLifecycle.Observation)
  | serve (capacity : Nat) (observed : List Header)

def Event.toModel (routing : Import.LinuxRoute.Snapshot) (before : BufferedState) : Event → Protocol.BufferedLifecycle.Event
  | .operation source => .operation (source.event.toModel routing before.tracker)
  | .serve capacity _ => .serve capacity

def Event.capacity : Event → Nat
  | .operation _ => 0
  | .serve capacity _ => capacity

def Event.isPacket : Event → Bool
  | .operation source => source.event.isPacket
  | .serve .. => false

structure Observation where
  index : Nat
  event : Event
  pending : Option (List Header)
  raw : Lean.Json

def Event.Matches (event : Event) (result : BufferedResult) : Prop :=
  match event with
  | .operation source => ∃ operation, result.operation = some operation ∧
      ConntrackLifecycle.Matches source operation ∧ result.served = []
  | .serve _ observed => result.operation = none ∧ result.served = observed

def Event.matches (event : Event) (result : BufferedResult) : Bool :=
  match event with
  | .operation source => match result.operation with
    | none => false
    | some actual => (ConntrackLifecycle.finding source actual).passed && decide (result.served = [])
  | .serve _ observed => result.operation.isNone && decide (result.served = observed)

theorem Event.matches_correct (event : Event) (result : BufferedResult) :
    event.matches result = true ↔ event.Matches result := by
  cases event with
  | serve capacity observed => simp [Event.matches, Event.Matches]
  | operation source =>
    cases found : result.operation with
    | none => simp [Event.matches, Event.Matches, found]
    | some actual => simp [Event.matches, Event.Matches, found, ConntrackLifecycle.finding_correct]

def PendingMatches (observation : Observation) (after : BufferedState) : Prop :=
  match observation.pending with
  | none => True
  | some pending => after.queue.pending = pending

def pendingMatches (observation : Observation) (after : BufferedState) : Bool :=
  match observation.pending with
  | none => true
  | some pending => decide (after.queue.pending = pending)

theorem pendingMatches_correct (observation : Observation) (after : BufferedState) :
    pendingMatches observation after = true ↔ PendingMatches observation after := by
  cases found : observation.pending <;> simp [pendingMatches, PendingMatches, found]

def Matches (observation : Observation) (result : BufferedResult) : Prop :=
  observation.event.Matches result ∧ PendingMatches observation result.state

structure Finding where
  observation : Observation
  before : BufferedState
  modelEvent : Protocol.BufferedLifecycle.Event
  result : BufferedResult
  passed : Bool

def finding (observation : Observation) (before : BufferedState)
    (modelEvent : Protocol.BufferedLifecycle.Event) (result : BufferedResult) : Finding :=
  ⟨observation, before, modelEvent, result,
    observation.event.matches result && pendingMatches observation result.state⟩

theorem finding_correct (observation : Observation) (before : BufferedState)
    (modelEvent : Protocol.BufferedLifecycle.Event) (result : BufferedResult) :
    (finding observation before modelEvent result).passed = true ↔ Matches observation result := by
  simp [finding, Matches, Event.matches_correct, pendingMatches_correct]

def Agreement (routing : Import.LinuxRoute.Snapshot) : BufferedState → List Observation → Prop
  | _, [] => True
  | before, observation :: observations =>
    ∃ result, Protocol.BufferedLifecycle.step before (observation.event.toModel routing before) = .ok result ∧
      Matches observation result ∧ Agreement routing result.state observations

inductive ReplayTrace (routing : Import.LinuxRoute.Snapshot) : BufferedState → List Finding → BufferedState → Prop
  | nil (state : BufferedState) : ReplayTrace routing state [] state
  | cons {final : BufferedState} {head : Finding} {tail : List Finding}
      (linked : head.modelEvent = head.observation.event.toModel routing head.before)
      (accepted : Protocol.BufferedLifecycle.step head.before head.modelEvent = .ok head.result)
      (rest : ReplayTrace routing head.result.state tail final) :
      ReplayTrace routing head.before (head :: tail) final

structure Report (routing : Import.LinuxRoute.Snapshot) (initial : BufferedState) (observations : List Observation) where
  final : BufferedState
  findings : List Finding
  covered : findings.map Finding.observation = observations
  trace : ReplayTrace routing initial findings final
  correct : findings.all Finding.passed = true ↔ Agreement routing initial observations

def audit (routing : Import.LinuxRoute.Snapshot) (initial : BufferedState) :
    (observations : List Observation) → Except String (Report routing initial observations)
  | [] => .ok ⟨initial, [], rfl, .nil initial, by simp [Agreement]⟩
  | observation :: observations => do
    let event := observation.event.toModel routing initial
    match accepted : Protocol.BufferedLifecycle.step initial event with
    | .error error => throw s!"/schedule/{observation.index}: {error.describe}"
    | .ok result =>
      let tail ← audit routing result.state observations
      return ⟨tail.final, finding observation initial event result :: tail.findings,
        by simp only [List.map_cons, finding, tail.covered],
        .cons (head := finding observation initial event result) rfl accepted tail.trace, by
          simp only [List.all_cons, Bool.and_eq_true, finding_correct, tail.correct, Agreement]
          simp [accepted, event]⟩

namespace Report

def compliant (report : Report routing initial observations) : Bool := report.findings.all Finding.passed

theorem compliant_iff (report : Report routing initial observations) :
    report.compliant = true ↔ Agreement routing initial observations := report.correct

end Report

structure Input where
  lifecycle : ConntrackLifecycle.Input
  initialPending : List Header
  observations : List Observation
  raw : Lean.Json

def Input.initial (input : Input) : BufferedState := ⟨input.lifecycle.initial, ⟨[], input.initialPending⟩⟩

theorem Input.initial_valid (input : Input) : input.initial.Valid := input.lifecycle.initialValid

private def require (condition : Bool) (message : String) : Except String Unit :=
  if condition then .ok () else .error message

private def headers (json : Lean.Json) : Except String (List Header) := do
  (← json.getArr?).toList.mapM Import.PacketFields.header

private def optionalHeaders (json : Lean.Json) : Except String (Option (List Header)) :=
  match json with
  | .null => .ok none
  | json => some <$> headers json

def Input.fromJson (json : Lean.Json) : Except String Input := do
  Import.PacketFields.fields json ["schema", "lifecycle", "initialPending", "schedule"]
  require ((← (← json.getObjVal? "schema").getNat?) == 1) "Use buffered lifecycle schema 1."
  let lifecycle ← ConntrackLifecycle.Input.fromJson (← json.getObjVal? "lifecycle")
  let initialPending ← headers (← json.getObjVal? "initialPending")
  let values ← (← json.getObjVal? "schedule").getArr?
  let mut remaining := lifecycle.events
  let mut observations := []
  for index in [:values.size] do
    let value := values[index]!
    let kind ← (← value.getObjVal? "type").getStr?
    let event ← match kind with
      | "operation" => do
        Import.PacketFields.fields value ["type", "pending"]
        let source :: rest := remaining | throw s!"/schedule/{index}: No lifecycle operation remains."
        remaining := rest
        pure (Event.operation source)
      | "serve" => do
        Import.PacketFields.fields value ["type", "capacity", "served", "pending"]
        pure (Event.serve (← (← value.getObjVal? "capacity").getNat?) (← headers (← value.getObjVal? "served")))
      | _ => throw s!"/schedule/{index}: Unsupported buffered event: {kind}."
    let pending ← optionalHeaders (← value.getObjVal? "pending")
    observations := observations ++ [⟨index, event, pending, value⟩]
  require remaining.isEmpty "The schedule must consume every lifecycle operation exactly once."
  return ⟨lifecycle, initialPending, observations, json⟩

def Input.parse (text : String) : Except String Input := do
  Input.fromJson (← Import.Json.parse text)

def Input.check (input : Input) : Except String (Report input.lifecycle.routing input.initial input.observations) :=
  audit input.lifecycle.routing input.initial input.observations

private def headersJson (values : List Header) : Lean.Json := Lean.toJson (values.map Import.PacketFields.headerJson)

def Report.assumptions : List String := ConntrackLifecycle.Report.assumptions ++ [
  "The initial pending list and supplied schedule cover the complete modeled FIFO without hidden arrivals or reordering.",
  "Serve events declare FIFO service opportunities; they do not measure a physical rate or elapsed time.",
  "Each serve event removes exactly min(capacity, pending length); queued idling requires zero declared capacity.",
  "Only modeled operation outputs join this queue; a native queue can also contain control traffic and other protocols.",
  "Physical queue identity, ordering, queue placement, and service guarantees need separate correspondence evidence."]

def Report.renderJson (report : Report routing initial observations) : Lean.Json := Lean.Json.mkObj [
  ("compliant", Lean.toJson report.compliant), ("scope", Lean.toJson "buffered-forwarding-replay"),
  ("assumptions", Lean.toJson Report.assumptions),
  ("initialPending", headersJson initial.queue.pending),
  ("pending", headersJson report.final.queue.pending), ("delivered", headersJson report.final.queue.delivered),
  ("findings", Lean.toJson (report.findings.map fun finding => Lean.Json.mkObj [
    ("source", Lean.toJson s!"/schedule/{finding.observation.index}"), ("matched", Lean.toJson finding.passed),
    ("capacity", Lean.toJson finding.observation.event.capacity),
    ("beforePending", headersJson finding.before.queue.pending),
    ("admitted", headersJson finding.result.admitted), ("served", headersJson finding.result.served),
    ("expectedPending", headersJson finding.result.state.queue.pending),
    ("pendingObserved", Lean.toJson finding.observation.pending.isSome),
    ("observedPending", (finding.observation.pending.map headersJson).getD .null),
    ("operation", match finding.observation.event with
      | .serve .. => .null
      | .operation source => Lean.Json.mkObj [
        ("source", Lean.toJson s!"/lifecycle/events/{source.index}"), ("config", Lean.toJson source.event.configID),
        ("expected", (finding.result.operation.bind (·.packet) |>.map
          (ConntrackLifecycle.PacketObservation.renderJson ∘ ConntrackLifecycle.PacketObservation.expected)).getD .null)]),
    ("observedServed", match finding.observation.event with
      | .operation _ => .null
      | .serve _ observed => headersJson observed)]))]

def Report.render (report : Report routing initial observations) : String :=
  (if report.compliant then "BUFFERED REPLAY MATCHES\n" else "BUFFERED REPLAY MISMATCH\n") ++ report.renderJson.pretty

end Netlib.Check.BufferedReplay
