import Netlib.Packet.StatefulACL
import Netlib.Protocol.Conntrack
import Netlib.Protocol.NetfilterNAT
import Netlib.Routing.Basic

/-!
# Ordinary tracked forwarding lifecycle

Inputs are valid unfragmented IPv4 TCP/UDP packets after transport-tracker validation.
The tracker must accept the modeled attachment without reopen, replacement, or retry.
Lookup attaches one confirmed record before the NAT and filter stages.
Fresh candidates remain unconfirmed until the final collision check.
Timeout evolution, helpers, related traffic, offload, and native race recovery are outside this model.
-/

namespace Netlib.Protocol.ConntrackLifecycle

open Packet
open StatefulACL (CTState)

def sourceURL : String := "https://raw.githubusercontent.com/torvalds/linux/v6.8/net/netfilter/nf_conntrack_core.c"

inductive Error where
  | invalidState
  | unsupportedTransport
  | invalidZone
  | missingCandidate
  | unexpectedCandidate
  | candidateMismatch
  | incompatibleCandidate
  | confirmationCollision
  deriving Repr, BEq, DecidableEq

def Error.describe : Error → String
  | .invalidState => "The confirmed table is outside the supported ordinary profile."
  | .unsupportedTransport => "Require a valid TCP or UDP packet after transport-tracker validation."
  | .invalidZone => "The lookup zone exceeds 16 bits."
  | .missingCandidate => "A new flow requires an explicit unconfirmed candidate."
  | .unexpectedCandidate => "An existing flow cannot replace its stored binding."
  | .candidateMismatch => "The candidate original tuple or zone does not match the input."
  | .incompatibleCandidate => "The candidate tuple and NAT flags are incompatible."
  | .confirmationCollision => "Ordinary confirmation collided; native clash and race recovery are unsupported."

structure Record where
  entry : NetfilterNAT.Entry
  seenReply : Bool
  deriving Repr, BEq, DecidableEq

structure State where
  records : List Record := []
  deriving Repr, BEq, DecidableEq

namespace State

def initial : State := {}

def model (state : State) : FlowNAT.Snapshot := ⟨state.records.map (·.entry.flow)⟩

def Valid (state : State) : Prop :=
  state.model.Valid ∧ ∀ record ∈ state.records, record.entry.Compatible

def check (state : State) : Bool :=
  state.model.check && state.records.all (·.entry.check)

theorem check_correct (state : State) : state.check = true ↔ state.Valid := by
  simp only [check, Bool.and_eq_true, FlowNAT.Snapshot.check_correct,
    List.all_eq_true, NetfilterNAT.Entry.check_correct, Valid]

def validate (state : State) : Except Error Unit :=
  if state.check then .ok () else .error .invalidState

theorem initial_valid : initial.Valid := by
  apply (check_correct _).mp
  decide

def markRecord (flow : FlowNAT.Entry) (record : Record) : Record :=
  if record.entry.flow = flow then { record with seenReply := true } else record

@[simp] theorem markRecord_entry (flow : FlowNAT.Entry) (record : Record) :
    (markRecord flow record).entry = record.entry := by
  unfold markRecord
  split <;> rfl

def markReply (state : State) (flow : FlowNAT.Entry) : State :=
  ⟨state.records.map (markRecord flow)⟩

theorem markReply_model (state : State) (flow : FlowNAT.Entry) :
    (state.markReply flow).model = state.model := by
  simp [markReply, model, List.map_map, Function.comp_def]

theorem markReply_valid (state : State) (flow : FlowNAT.Entry) (valid : state.Valid) :
    (state.markReply flow).Valid := by
  constructor
  · rw [markReply_model]
    exact valid.1
  · intro record member
    obtain ⟨old, belongs, rfl⟩ := List.mem_map.mp member
    simpa using valid.2 old belongs

end State

def classify (record : Record) : FlowNAT.Direction → CTState
  | .reply => .established
  | .original => if record.seenReply then .established else .new

@[simp] theorem classify_reply (record : Record) : classify record .reply = .established := rfl

@[simp] theorem classify_marked_original (record : Record) :
    classify { record with seenReply := true } .original = .established := rfl

structure Pipeline where
  routes : List (Routing.Entry String)
  forward : StatefulACL.Policy
  forwardDefault : Action := .deny
  late : StatefulACL.Policy := []
  lateDefault : Action := .permit
  deriving Repr

structure Input where
  zone : Nat
  packet : Header
  candidate : Option NetfilterNAT.Entry := none
  deriving Repr, BEq, DecidableEq

structure Attachment where
  entry : NetfilterNAT.Entry
  direction : FlowNAT.Direction
  classification : CTState
  fresh : Bool
  deriving Repr, BEq, DecidableEq

structure Prepared (input : Input) where
  state : State
  valid : state.Valid
  attachment : Attachment
  compatible : attachment.entry.Compatible
  attached : attachment.entry.flow.key attachment.direction = (input.zone, input.packet)

def prepare (state : State) (input : Input) : Except Error (Prepared input) := do
  if valid : state.check = true then
    if input.zone ≥ 65536 then throw .invalidZone
    if !Conntrack.transport input.packet then throw .unsupportedTransport
    match found : state.model.lookup input.zone input.packet with
    | none =>
      let some candidate := input.candidate | throw .missingCandidate
      if compatible : candidate.check = true then
        if matching : candidate.flow.original = input.packet ∧ candidate.flow.originalZone = input.zone then
          return ⟨state, (State.check_correct _).mp valid, ⟨candidate, .original, .new, true⟩,
            (NetfilterNAT.Entry.check_correct _).mp compatible,
            by simp [FlowNAT.Entry.key, FlowNAT.Entry.zone, FlowNAT.Entry.input, matching]⟩
        else throw .candidateMismatch
      else throw .incompatibleCandidate
    | some hit =>
      if input.candidate.isSome then throw .unexpectedCandidate
      match recordFound : state.records.find? (fun record => decide (record.entry.flow = hit.entry)) with
      | none => throw .invalidState
      | some record =>
        have member := List.mem_of_find?_eq_some recordFound
        have same : record.entry.flow = hit.entry := of_decide_eq_true (List.find?_some
          (p := fun record : Record => decide (record.entry.flow = hit.entry)) (a := record) recordFound)
        have compatible := ((State.check_correct _).mp valid).2 record member
        have attached : record.entry.flow.key hit.direction = (input.zone, input.packet) := by
          rw [same]
          exact (FlowNAT.Snapshot.lookup_sound _ _ _ _ found).2
        let classification := classify record hit.direction
        match direction : hit.direction with
        | .original => return ⟨state, (State.check_correct _).mp valid,
            ⟨record.entry, .original, classification, false⟩, compatible, by simpa [direction] using attached⟩
        | .reply => return ⟨state.markReply hit.entry,
            State.markReply_valid _ _ ((State.check_correct _).mp valid),
            ⟨record.entry, .reply, classification, false⟩, compatible, by simpa [direction] using attached⟩
  else throw .invalidState

theorem prepare_model (state : State) (input : Input) (prepared : Prepared input)
    (accepted : prepare state input = .ok prepared) : prepared.state.model = state.model := by
  simp only [prepare] at accepted
  repeat' first | (cases accepted; first | rfl | exact State.markReply_model _ _)
                | (split at accepted <;> try simp [bind, pure, throw, Except.bind] at accepted)

theorem prepare_fresh (state : State) (input : Input) (prepared : Prepared input)
    (accepted : prepare state input = .ok prepared) (fresh : prepared.attachment.fresh = true) :
    prepared.state = state ∧ prepared.attachment.direction = .original ∧
      prepared.attachment.classification = .new ∧ input.candidate = some prepared.attachment.entry := by
  simp only [prepare] at accepted
  repeat' first | (cases accepted; first | exact ⟨rfl, rfl, rfl, by assumption⟩ | cases fresh)
                | (split at accepted <;> try simp [bind, pure, throw, Except.bind] at accepted)

theorem prepare_existing_original (state : State) (input : Input) (prepared : Prepared input)
    (accepted : prepare state input = .ok prepared) (existing : prepared.attachment.fresh = false)
    (original : prepared.attachment.direction = .original) :
    ∃ record ∈ state.records, prepared.attachment.entry = record.entry ∧
      prepared.attachment.classification = (if record.seenReply then .established else .new) ∧
      prepared.state = state := by
  simp only [prepare] at accepted
  repeat' first
    | (cases accepted
       first
       | (simp at existing; done)
       | (simp at original; done)
       | (rename_i record recordFound direction
          refine ⟨record, List.mem_of_find?_eq_some recordFound, rfl, ?_, rfl⟩
          simp [classify, direction]))
    | (split at accepted <;> try simp [bind, pure, throw, Except.bind] at accepted)

theorem prepare_reply (state : State) (input : Input) (prepared : Prepared input)
    (accepted : prepare state input = .ok prepared) (reply : prepared.attachment.direction = .reply) :
    prepared.attachment.classification = .established ∧ prepared.attachment.fresh = false ∧
      prepared.state = state.markReply prepared.attachment.entry.flow := by
  simp only [prepare] at accepted
  repeat' first
    | (cases accepted
       first
       | (simp at reply; done)
       | (rename_i record recordFound direction
          have same : record.entry.flow = _ := of_decide_eq_true (List.find?_some
            (p := fun item : Record => decide (item.entry.flow = _)) (a := record) recordFound)
          exact ⟨by simp [classify, direction], rfl, by simp [same]⟩))
    | (split at accepted <;> try simp [bind, pure, throw, Except.bind] at accepted)

def destinationStage (entry : NetfilterNAT.Entry) (direction : FlowNAT.Direction) : Rewrite :=
  let change := entry.rewrite direction
  { destination := change.destination, destinationPort := change.destinationPort }

def sourceStage (entry : NetfilterNAT.Entry) (direction : FlowNAT.Direction) : Rewrite :=
  let change := entry.rewrite direction
  { source := change.source, sourcePort := change.sourcePort }

theorem stages_compose (entry : NetfilterNAT.Entry) (direction : FlowNAT.Direction) :
    (destinationStage entry direction).comp (sourceStage entry direction) = entry.rewrite direction := by
  simp [destinationStage, sourceStage, Rewrite.comp, NetfilterNAT.Entry.rewrite]

theorem stages_correct (entry : NetfilterNAT.Entry) (compatible : entry.Compatible) (direction : FlowNAT.Direction) :
    (sourceStage entry direction).apply ((destinationStage entry direction).apply (entry.flow.input direction)) =
      entry.flow.output direction := by
  rw [← Rewrite.comp_apply, stages_compose]
  exact entry.rewrite_correct compatible direction

inductive Disposition where
  | forwarded
  | routeDrop
  | forwardDrop
  | lateDrop
  deriving Repr, BEq, DecidableEq

structure Outcome where
  state : State
  valid : state.Valid
  output : Option Header
  attachment : Attachment
  afterDestination : Header
  afterSource : Option Header
  nextHop : Option String
  disposition : Disposition

private def dropped (prepared : Prepared input) (header : Header) (wire : Option Header)
    (nextHop : Option String) (disposition : Disposition) : Outcome :=
  ⟨prepared.state, prepared.valid, none, prepared.attachment, header, wire, nextHop, disposition⟩

def process (pipeline : Pipeline) (prepared : Prepared input) : Except Error Outcome := do
  let attachment := prepared.attachment
  let afterDestination := (destinationStage attachment.entry attachment.direction).apply input.packet
  let hop := Routing.nextHop pipeline.routes afterDestination.destination
  match hop with
  | none => return dropped prepared afterDestination none none .routeDrop
  | some nextHop =>
    if StatefulACL.Policy.evaluate pipeline.forwardDefault pipeline.forward attachment.classification afterDestination = .deny then
      return dropped prepared afterDestination none (some nextHop) .forwardDrop
    let wire := (sourceStage attachment.entry attachment.direction).apply afterDestination
    if StatefulACL.Policy.evaluate pipeline.lateDefault pipeline.late attachment.classification wire = .deny then
      return dropped prepared afterDestination (some wire) (some nextHop) .lateDrop
    if attachment.fresh then
      let confirmed : State := ⟨prepared.state.records ++ [⟨attachment.entry, false⟩]⟩
      if valid : confirmed.check = true then
        return ⟨confirmed, (State.check_correct _).mp valid, some wire, attachment,
          afterDestination, some wire, some nextHop, .forwarded⟩
      else throw .confirmationCollision
    else
      return ⟨prepared.state, prepared.valid, some wire, attachment, afterDestination,
        some wire, some nextHop, .forwarded⟩

def step (pipeline : Pipeline) (state : State) (input : Input) : Except Error Outcome := do
  let prepared ← prepare state input
  process pipeline prepared

theorem step_valid (pipeline : Pipeline) (state : State) (input : Input) (outcome : Outcome)
    (_accepted : step pipeline state input = .ok outcome) : outcome.state.Valid := outcome.valid

theorem process_attachment (pipeline : Pipeline) (prepared : Prepared input) (outcome : Outcome)
    (accepted : process pipeline prepared = .ok outcome) : outcome.attachment = prepared.attachment := by
  simp only [process] at accepted
  split at accepted
  · cases accepted
    rfl
  · split at accepted
    · cases accepted
      rfl
    · split at accepted
      · cases accepted
        rfl
      · split at accepted
        · split at accepted
          · cases accepted
            rfl
          · cases accepted
        · cases accepted
          rfl

theorem process_destination (pipeline : Pipeline) (prepared : Prepared input) (outcome : Outcome)
    (accepted : process pipeline prepared = .ok outcome) :
    outcome.afterDestination =
      (destinationStage prepared.attachment.entry prepared.attachment.direction).apply input.packet := by
  simp only [process] at accepted
  split at accepted
  · cases accepted
    rfl
  · split at accepted
    · cases accepted
      rfl
    · split at accepted
      · cases accepted
        rfl
      · split at accepted
        · split at accepted
          · cases accepted
            rfl
          · cases accepted
        · cases accepted
          rfl

theorem process_state (pipeline : Pipeline) (prepared : Prepared input) (outcome : Outcome)
    (accepted : process pipeline prepared = .ok outcome) :
    outcome.state = prepared.state ∨
      (prepared.attachment.fresh = true ∧ outcome.disposition = .forwarded ∧
        outcome.state.records = prepared.state.records ++ [⟨prepared.attachment.entry, false⟩]) := by
  simp only [process] at accepted
  split at accepted
  · cases accepted
    exact .inl rfl
  · split at accepted
    · cases accepted
      exact .inl rfl
    · split at accepted
      · cases accepted
        exact .inl rfl
      · split at accepted
        · split at accepted
          · cases accepted
            exact .inr ⟨by assumption, rfl, rfl⟩
          · cases accepted
        · cases accepted
          exact .inl rfl

theorem process_drop_state (pipeline : Pipeline) (prepared : Prepared input) (outcome : Outcome)
    (accepted : process pipeline prepared = .ok outcome) (dropped : outcome.disposition ≠ .forwarded) :
    outcome.state = prepared.state := by
  rcases process_state pipeline prepared outcome accepted with same | ⟨_, forwarded, _⟩
  · exact same
  · exact False.elim (dropped forwarded)

theorem process_existing_state (pipeline : Pipeline) (prepared : Prepared input) (outcome : Outcome)
    (accepted : process pipeline prepared = .ok outcome) (existing : prepared.attachment.fresh = false) :
    outcome.state = prepared.state := by
  rcases process_state pipeline prepared outcome accepted with same | ⟨fresh, _, _⟩
  · exact same
  · simp [existing] at fresh

theorem process_output (pipeline : Pipeline) (prepared : Prepared input) (outcome : Outcome) (packet : Header)
    (accepted : process pipeline prepared = .ok outcome) (forwarded : outcome.output = some packet) :
    packet = prepared.attachment.entry.flow.output prepared.attachment.direction := by
  have attached : prepared.attachment.entry.flow.input prepared.attachment.direction = input.packet :=
    congrArg Prod.snd prepared.attached
  have rewritten := stages_correct prepared.attachment.entry prepared.compatible prepared.attachment.direction
  rw [attached] at rewritten
  simp only [process] at accepted
  split at accepted
  · cases accepted
    cases forwarded
  · split at accepted
    · cases accepted
      cases forwarded
    · split at accepted
      · cases accepted
        cases forwarded
      · split at accepted
        · split at accepted
          · cases accepted
            exact (Option.some.inj forwarded).symm.trans rewritten
          · cases accepted
        · cases accepted
          exact (Option.some.inj forwarded).symm.trans rewritten

private theorem action_permit (action : Action) (allowed : action ≠ .deny) : action = .permit := by
  cases action <;> simp_all

theorem process_filters (pipeline : Pipeline) (prepared : Prepared input) (outcome : Outcome) (packet : Header)
    (accepted : process pipeline prepared = .ok outcome) (forwarded : outcome.output = some packet) :
    outcome.disposition = .forwarded ∧
      StatefulACL.Policy.evaluate pipeline.forwardDefault pipeline.forward
        prepared.attachment.classification outcome.afterDestination = .permit ∧
      StatefulACL.Policy.evaluate pipeline.lateDefault pipeline.late
        prepared.attachment.classification packet = .permit ∧
      Routing.nextHop pipeline.routes outcome.afterDestination.destination = outcome.nextHop ∧
      outcome.nextHop.isSome = true := by
  simp only [process] at accepted
  split at accepted
  · cases accepted
    cases forwarded
  · split at accepted
    · cases accepted
      cases forwarded
    · split at accepted
      · cases accepted
        cases forwarded
      · split at accepted
        · split at accepted
          · cases accepted
            cases Option.some.inj forwarded
            exact ⟨rfl, action_permit _ (by assumption), action_permit _ (by assumption), by assumption, rfl⟩
          · cases accepted
        · cases accepted
          cases Option.some.inj forwarded
          exact ⟨rfl, action_permit _ (by assumption), action_permit _ (by assumption), by assumption, rfl⟩

theorem process_forwarded_iff (pipeline : Pipeline) (prepared : Prepared input) (outcome : Outcome)
    (accepted : process pipeline prepared = .ok outcome) :
    outcome.output.isSome = true ↔ outcome.disposition = .forwarded := by
  simp only [process] at accepted
  repeat' first | (cases accepted; simp [dropped]) | (split at accepted <;> try simp [throw] at accepted)

theorem step_prepared (pipeline : Pipeline) (state : State) (input : Input) (outcome : Outcome)
    (accepted : step pipeline state input = .ok outcome) :
    ∃ prepared, prepare state input = .ok prepared ∧ process pipeline prepared = .ok outcome := by
  cases found : prepare state input with
  | error error => simp [step, found, bind, Except.bind] at accepted
  | ok prepared => exact ⟨prepared, rfl, by simpa [step, found, bind, Except.bind] using accepted⟩

theorem step_output (pipeline : Pipeline) (state : State) (input : Input) (outcome : Outcome) (packet : Header)
    (accepted : step pipeline state input = .ok outcome) (forwarded : outcome.output = some packet) :
    packet = outcome.attachment.entry.flow.output outcome.attachment.direction := by
  obtain ⟨prepared, _, processed⟩ := step_prepared pipeline state input outcome accepted
  rw [process_attachment pipeline prepared outcome processed]
  exact process_output pipeline prepared outcome packet processed forwarded

theorem step_filters (pipeline : Pipeline) (state : State) (input : Input) (outcome : Outcome) (packet : Header)
    (accepted : step pipeline state input = .ok outcome) (forwarded : outcome.output = some packet) :
    outcome.disposition = .forwarded ∧
      StatefulACL.Policy.evaluate pipeline.forwardDefault pipeline.forward
        outcome.attachment.classification outcome.afterDestination = .permit ∧
      StatefulACL.Policy.evaluate pipeline.lateDefault pipeline.late
        outcome.attachment.classification packet = .permit ∧
      Routing.nextHop pipeline.routes outcome.afterDestination.destination = outcome.nextHop ∧
      outcome.nextHop.isSome = true := by
  obtain ⟨prepared, _, processed⟩ := step_prepared pipeline state input outcome accepted
  rw [process_attachment pipeline prepared outcome processed]
  exact process_filters pipeline prepared outcome packet processed forwarded

theorem step_forwarded_iff (pipeline : Pipeline) (state : State) (input : Input) (outcome : Outcome)
    (accepted : step pipeline state input = .ok outcome) :
    outcome.output.isSome = true ↔ outcome.disposition = .forwarded := by
  obtain ⟨prepared, _, processed⟩ := step_prepared pipeline state input outcome accepted
  exact process_forwarded_iff pipeline prepared outcome processed

theorem step_fresh_drop (pipeline : Pipeline) (state : State) (input : Input) (outcome : Outcome)
    (accepted : step pipeline state input = .ok outcome) (fresh : outcome.attachment.fresh = true)
    (dropped : outcome.disposition ≠ .forwarded) : outcome.state = state := by
  obtain ⟨prepared, attached, processed⟩ := step_prepared pipeline state input outcome accepted
  rw [process_attachment pipeline prepared outcome processed] at fresh
  exact (process_drop_state pipeline prepared outcome processed dropped).trans
    (prepare_fresh state input prepared attached fresh).1

theorem step_reply_state (pipeline : Pipeline) (state : State) (input : Input) (outcome : Outcome)
    (accepted : step pipeline state input = .ok outcome) (reply : outcome.attachment.direction = .reply) :
    outcome.attachment.classification = .established ∧
      outcome.state = state.markReply outcome.attachment.entry.flow := by
  obtain ⟨prepared, attached, processed⟩ := step_prepared pipeline state input outcome accepted
  have same := process_attachment pipeline prepared outcome processed
  rw [same] at reply ⊢
  obtain ⟨classification, existing, marked⟩ := prepare_reply state input prepared attached reply
  exact ⟨classification, (process_existing_state pipeline prepared outcome processed existing).trans marked⟩

theorem step_existing_original (pipeline : Pipeline) (state : State) (input : Input) (outcome : Outcome)
    (accepted : step pipeline state input = .ok outcome) (existing : outcome.attachment.fresh = false)
    (original : outcome.attachment.direction = .original) :
    outcome.state = state ∧ ∃ record ∈ state.records, outcome.attachment.entry = record.entry ∧
      outcome.attachment.classification = (if record.seenReply then .established else .new) := by
  obtain ⟨prepared, attached, processed⟩ := step_prepared pipeline state input outcome accepted
  have same := process_attachment pipeline prepared outcome processed
  rw [same] at existing original ⊢
  obtain ⟨record, member, entry, classification, unchanged⟩ :=
    prepare_existing_original state input prepared attached existing original
  exact ⟨(process_existing_state pipeline prepared outcome processed existing).trans unchanged,
    record, member, entry, classification⟩

structure Call where
  pipeline : Pipeline
  input : Input

def run : State → List Call → Except Error (State × List Outcome)
  | state, [] => .ok (state, [])
  | state, call :: calls => do
    let outcome ← step call.pipeline state call.input
    let (final, outcomes) ← run outcome.state calls
    return (final, outcome :: outcomes)

inductive Trace : State → List Call → List Outcome → State → Prop
  | nil (state : State) : Trace state [] [] state
  | cons {state final : State} {call : Call} {calls : List Call} {outcome : Outcome} {outcomes : List Outcome}
      (accepted : step call.pipeline state call.input = .ok outcome)
      (rest : Trace outcome.state calls outcomes final) :
      Trace state (call :: calls) (outcome :: outcomes) final

theorem run_trace (state final : State) (calls : List Call) (outcomes : List Outcome)
    (accepted : run state calls = .ok (final, outcomes)) : Trace state calls outcomes final := by
  induction calls generalizing state outcomes with
  | nil =>
    simp [run] at accepted
    rcases accepted with ⟨rfl, rfl⟩
    exact .nil _
  | cons call calls ih =>
    cases found : step call.pipeline state call.input with
    | error error => simp [run, found, bind, Except.bind] at accepted
    | ok outcome =>
      cases remaining : run outcome.state calls with
      | error error => simp [run, found, remaining, bind, Except.bind] at accepted
      | ok result =>
        rcases result with ⟨next, rest⟩
        simp [run, found, remaining, bind, Except.bind, pure] at accepted
        rcases accepted with ⟨rfl, rfl⟩
        exact .cons found (ih _ _ remaining)

theorem Trace.valid {state final : State} {calls : List Call} {outcomes : List Outcome}
    (trace : Trace state calls outcomes final) (initial : state.Valid) :
    final.Valid ∧ ∀ outcome ∈ outcomes, outcome.state.Valid := by
  induction trace with
  | nil => exact ⟨initial, by simp⟩
  | cons accepted rest ih =>
    obtain ⟨finalValid, each⟩ := ih (step_valid _ _ _ _ accepted)
    refine ⟨finalValid, ?_⟩
    intro outcome member
    rcases List.mem_cons.mp member with rfl | member
    · exact step_valid _ _ _ _ accepted
    · exact each _ member

theorem run_valid (state final : State) (calls : List Call) (outcomes : List Outcome)
    (accepted : run state calls = .ok (final, outcomes)) (initial : state.Valid) :
    final.Valid ∧ ∀ outcome ∈ outcomes, outcome.state.Valid :=
  (run_trace state final calls outcomes accepted).valid initial

def establishedPermit : StatefulACL.Rule := ⟨{}, some [.established], .permit⟩

theorem established_first_permits (following : StatefulACL.Policy) (fallback : Action) (packet : Header) :
    StatefulACL.Policy.evaluate fallback (establishedPermit :: following) .established packet = .permit := by
  apply StatefulACL.Policy.evaluate_cons_accepts
  simp [establishedPermit, StatefulACL.Rule.accepts, StatefulACL.Rule.stateAccepts]

end Netlib.Protocol.ConntrackLifecycle
