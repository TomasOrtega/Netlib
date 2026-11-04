import Netlib.Protocol.NAT
import Netlib.Compile.Policy
import Netlib.Import.PacketFields

namespace Netlib.Check.NATTrace

open Packet Protocol

/-- Outbound permission comes from the declared policy, not the observation. -/
inductive Event where
  | outbound (packet : Header) (allocation : Endpoint) (expiresAt : Nat)
  | inbound (packet : Header)
  | advance (now : Nat)
  | close (original : Header)
  | flush

namespace Event

def toModel (rules : Packet.ACL) : Event → NAT.Event
  | .outbound packet allocation expiresAt => .outbound packet allocation (rules.allows packet) expiresAt
  | .inbound packet => .inbound packet
  | .advance now => .advance now
  | .close packet => .close packet
  | .flush => .flush

def isPacket : Event → Bool
  | .outbound .. | .inbound .. => true
  | _ => false

end Event

structure Observation where
  index : Nat
  event : Event
  observed : Option Header := none

def Matches (rules : Packet.ACL) (state : NAT.State) (observation : Observation) : Prop :=
  observation.event.isPacket = true →
    observation.observed = (NAT.step state (observation.event.toModel rules)).output

def TraceMatches (rules : Packet.ACL) : NAT.State → List Observation → Prop
  | _, [] => True
  | state, observation :: observations =>
    Matches rules state observation ∧
      TraceMatches rules (NAT.step state (observation.event.toModel rules)).state observations

structure Finding where
  index : Nat
  packet : Bool
  passed : Bool
  expected : Option Header
  observed : Option Header

private def finding (rules : Packet.ACL) (state : NAT.State) (observation : Observation) : Finding :=
  let expected := (NAT.step state (observation.event.toModel rules)).output
  ⟨observation.index, observation.event.isPacket,
    !observation.event.isPacket || decide (observation.observed = expected), expected, observation.observed⟩

private theorem finding_correct (rules : Packet.ACL) (state : NAT.State) (observation : Observation) :
    (finding rules state observation).passed = true ↔ Matches rules state observation := by
  cases packet : observation.event.isPacket <;> simp [finding, Matches, packet]

structure Report (rules : Packet.ACL) (initial : NAT.State) (observations : List Observation) where
  findings : List Finding
  covered : findings.map Finding.index = observations.map Observation.index
  correct : findings.all Finding.passed = true ↔ TraceMatches rules initial observations

def audit (rules : Packet.ACL) (initial : NAT.State) :
    (observations : List Observation) → Report rules initial observations
  | [] => ⟨[], rfl, by simp [TraceMatches]⟩
  | observation :: observations =>
    let head := finding rules initial observation
    let tail := audit rules (NAT.step initial (observation.event.toModel rules)).state observations
    ⟨head :: tail.findings, by simp only [List.map_cons, tail.covered]; rfl, by
      simp only [List.all_cons, Bool.and_eq_true, head, finding_correct, tail.correct, TraceMatches]⟩

theorem matched_outbound_policy (compiled : Compile.ACL.Certified intents) (state : NAT.State)
    (index : Nat) (packet output : Header) (allocation : Endpoint) (expiresAt : Nat)
    (matched : Matches compiled.rules state ⟨index, .outbound packet allocation expiresAt, some output⟩) :
    Compile.ACL.Meaning intents packet := by
  have accepted : (NAT.step state (.outbound packet allocation (compiled.rules.allows packet) expiresAt)).output =
      some output := (matched rfl).symm
  exact (compiled.correct packet).mp (NAT.outbound_authorized _ _ _ _ _ _ accepted).1

def modelEvents (rules : Packet.ACL) (observations : List Observation) : List NAT.Event :=
  observations.map (fun observation => observation.event.toModel rules)

def stateAfter (rules : Packet.ACL) (initial : NAT.State) (observations : List Observation) : NAT.State :=
  NAT.run initial (modelEvents rules observations)

/-- A restored reply has an earlier raw outbound source permitted by the declared intent. -/
theorem trace_reply_policy (compiled : Compile.ACL.Certified intents)
    (observations : List Observation) (packet restored : Header)
    (accepted : NAT.inbound (stateAfter compiled.rules NAT.State.initial observations) packet = some restored) :
    ∃ original allocation expiresAt, (∃ observation ∈ observations,
      observation.event = .outbound original allocation expiresAt) ∧
      Compile.ACL.Meaning intents original ∧ original.reverse = restored := by
  obtain ⟨original, allocation, expiresAt, origin, reverse⟩ :=
    NAT.trace_reply_origin (modelEvents compiled.rules observations) packet restored accepted
  obtain ⟨observation, member, modeled⟩ := List.mem_map.mp origin
  cases event : observation.event with
  | outbound originalPacket selectedAllocation expiry =>
    simp only [event, Event.toModel, NAT.Event.outbound.injEq] at modeled
    rcases modeled with ⟨rfl, rfl, allowed, rfl⟩
    exact ⟨originalPacket, selectedAllocation, expiry, ⟨observation, member, event⟩,
      (compiled.correct originalPacket).mp allowed, reverse⟩
  | inbound => simp [event, Event.toModel] at modeled
  | advance => simp [event, Event.toModel] at modeled
  | close => simp [event, Event.toModel] at modeled
  | flush => simp [event, Event.toModel] at modeled

theorem traceMatches_append (rules : Packet.ACL) (initial : NAT.State)
    (earlier later : List Observation) :
    TraceMatches rules initial (earlier ++ later) ↔
      TraceMatches rules initial earlier ∧ TraceMatches rules (stateAfter rules initial earlier) later := by
  induction earlier generalizing initial with
  | nil => simp [TraceMatches, stateAfter, modelEvents, NAT.run]
  | cons observation observations ih =>
    simpa only [List.cons_append, TraceMatches, stateAfter, modelEvents, List.map_cons,
      NAT.run, List.foldl_cons, and_assoc] using
      and_congr_right (fun _ => ih (NAT.step initial (observation.event.toModel rules)).state)

namespace Report

def compliant (report : Report rules initial observations) : Bool := report.findings.all Finding.passed

theorem compliant_iff (report : Report rules initial observations) :
    report.compliant = true ↔ TraceMatches rules initial observations := report.correct

theorem inbound_policy_origin (compiled : Compile.ACL.Certified intents)
    (earlier later : List Observation) (index : Nat) (packet restored : Header)
    (report : Report compiled.rules NAT.State.initial
      (earlier ++ ⟨index, .inbound packet, some restored⟩ :: later))
    (passed : report.compliant = true) :
    ∃ original allocation expiresAt, (∃ observation ∈ earlier,
      observation.event = .outbound original allocation expiresAt) ∧
      Compile.ACL.Meaning intents original ∧ original.reverse = restored := by
  have matching := (traceMatches_append compiled.rules NAT.State.initial earlier _).mp
    (report.compliant_iff.mp passed)
  have accepted := (matching.2.1 rfl).symm
  exact trace_reply_policy compiled earlier packet restored accepted

def renderJson (report : Report rules initial observations) : Lean.Json :=
  Lean.Json.mkObj [
    ("compliant", Lean.toJson report.compliant),
    ("scope", Lean.toJson "local-source-napt-trace"),
    ("findings", Lean.toJson (report.findings.map fun result => Lean.Json.mkObj [
      ("source", Lean.toJson s!"/events/{result.index}"),
      ("packet", Lean.toJson result.packet), ("matched", Lean.toJson result.passed),
      ("expected", Import.PacketFields.optionalHeaderJson result.expected),
      ("observed", Import.PacketFields.optionalHeaderJson result.observed)]))]

def render (report : Report rules initial observations) : String :=
  String.intercalate "\n" ((if report.compliant then "COMPLIANT" else "NONCOMPLIANT") ::
    "Scope: local source-NAPT trace under the declared policy." ::
    report.findings.map fun result =>
      s!"/events/{result.index}: {if result.passed then "matched" else "violated"}; " ++
      s!"expected {(Import.PacketFields.optionalHeaderJson result.expected).compress}; " ++
      s!"observed {(Import.PacketFields.optionalHeaderJson result.observed).compress}")

end Report

structure Input where
  intents : List Compile.ACL.Intent
  compiled : Compile.ACL.Certified intents
  observations : List Observation

private def event (json : Lean.Json) (index : Nat) (clock : Nat) : Except String (Observation × Nat) := do
  let kind ← (← json.getObjVal? "type").getStr?
  match kind with
  | "outbound" =>
    Import.PacketFields.fields json ["type", "packet", "allocation", "expiresAt", "observed"]
    return (⟨index, .outbound (← Import.PacketFields.header (← json.getObjVal? "packet"))
      (← Import.PacketFields.endpoint (← json.getObjVal? "allocation"))
      (← (← json.getObjVal? "expiresAt").getNat?),
      ← Import.PacketFields.optionalHeader (← json.getObjVal? "observed")⟩, clock)
  | "inbound" =>
    Import.PacketFields.fields json ["type", "packet", "observed"]
    return (⟨index, .inbound (← Import.PacketFields.header (← json.getObjVal? "packet")),
      ← Import.PacketFields.optionalHeader (← json.getObjVal? "observed")⟩, clock)
  | "advance" =>
    Import.PacketFields.fields json ["type", "now"]
    let now ← (← json.getObjVal? "now").getNat?
    if now < clock then throw "The NAT trace clock moved backward."
    return (⟨index, .advance now, none⟩, now)
  | "close" =>
    Import.PacketFields.fields json ["type", "packet"]
    return (⟨index, .close (← Import.PacketFields.header (← json.getObjVal? "packet")), none⟩, clock)
  | "flush" =>
    Import.PacketFields.fields json ["type"]
    return (⟨index, .flush, none⟩, clock)
  | _ => throw s!"Unsupported NAT trace event: {kind}."

def Input.fromJson (json : Lean.Json) (budget : Nat := 100000) : Except String Input := do
  Import.PacketFields.fields json ["schema", "policy", "events"]
  if (← (← json.getObjVal? "schema").getNat?) != 1 then throw "Use NAT trace schema 1."
  let intents ← Compile.Policy.fromJson (← json.getObjVal? "policy")
  let compiled ← (Compile.ACL.compile intents budget).mapError (·.describe)
  let values ← (← json.getObjVal? "events").getArr?
  let mut clock := 0
  let mut observations := []
  for index in [:values.size] do
    let (observation, now) ← (event values[index]! index clock).mapError (s!"/events/{index}: " ++ ·)
    clock := now
    observations := observations ++ [observation]
  if !(observations.any (·.event.isPacket)) then throw "Supply at least one observed packet event."
  return ⟨intents, compiled, observations⟩

def Input.parse (text : String) (budget : Nat := 100000) : Except String Input := do
  Input.fromJson (← Import.Json.parse text) budget

def Input.check (input : Input) : Report input.compiled.rules NAT.State.initial input.observations :=
  audit input.compiled.rules NAT.State.initial input.observations

end Netlib.Check.NATTrace
