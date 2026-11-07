import Netlib.Check.FederatedCohortReplay
import Netlib.Check.FederatedCohortSafety
import Netlib.Check.FederatedPacketReplayEvidence

/-!
# Source evidence in the original cohort report

Projected reports retain every global slot. Their send and receipt witnesses
resolve back to stored cohort steps with the original raw actions.
-/

namespace Netlib.Federation.Cohort.Replay

variable {input : Input} {size : Nat} {context : Context input size}
variable {headers : Vector Packet.Header size} {actions : List InFlight.Action}

def Step.project (step : Step context headers) (index : Fin size) :
    InFlight.Replay.Step (context.packets.get index) (headers.get index) :=
  let outcome := step.advanced.outcome.packet index
  let success := step.advanced.facts.locals index
  let facts := InFlight.Execution.rawAdvance_facts _ _ _ _ outcome success
  ⟨step.before.packet index, projectAction context step.action index,
    ⟨outcome, success, facts.observations, facts.tick, facts.keyStep, facts.candidateEq⟩⟩

@[simp] theorem Step.project_before (step : Step context headers) (index : Fin size) :
    (step.project index).before = step.before.packet index := rfl

@[simp] theorem Step.project_action (step : Step context headers) (index : Fin size) :
    (step.project index).action = projectAction context step.action index := rfl

@[simp] theorem Step.project_after (step : Step context headers) (index : Fin size) :
    (step.project index).after = step.after.packet index := rfl

@[simp] theorem Step.project_event (step : Step context headers) (index : Fin size) :
    (step.project index).event = step.event.packet context index := rfl

theorem Chained.project {before after : State input size} {steps : List (Step context headers)}
    (chain : Chained before steps after) (index : Fin size) :
    InFlight.Replay.Chained (before.packet index) (steps.map (fun step => step.project index)) (after.packet index) := by
  induction steps generalizing before with
  | nil => exact congrArg (fun state => state.packet index) chain
  | cons step rest ih => exact ⟨congrArg (fun state => state.packet index) chain.1, ih chain.2⟩

def Report.project (report : Report context headers actions) (index : Fin size) :
    InFlight.Replay.Report (context.packets.get index) (headers.get index)
      (actions.map (fun action => projectAction context action index)) where
  steps := report.steps.map (fun step => step.project index)
  final := report.final.packet index
  chained := by simpa only [initialState_packet] using report.chained.project index
  covered := by
    simpa only [List.map_map, Function.comp_def, Step.project_action] using congrArg
      (List.map (fun action => projectAction context action index)) report.covered

theorem stateAt_project (before : State input size) (steps : List (Step context headers)) (index : Fin size) (cut : Nat) :
    InFlight.Replay.stateAt (before.packet index) (steps.map (fun step => step.project index)) cut =
      (stateAt before steps cut).packet index := by
  induction steps generalizing before cut with
  | nil => rfl
  | cons step rest ih => cases cut with
    | zero => rfl
    | succ cut => exact ih step.after cut

@[simp] theorem Report.project_state (report : Report context headers actions) (index : Fin size) (cut : Nat) :
    (report.project index).prefix.state cut = (report.prefix.state cut).packet index := by
  change InFlight.Replay.stateAt (InFlight.initialState _) _ cut = _
  rw [← initialState_packet]
  exact stateAt_project _ _ _ _

@[simp] theorem Report.project_length (report : Report context headers actions) (index : Fin size) :
    (report.project index).steps.length = report.steps.length := List.length_map _

theorem Report.project_events (report : Report context headers actions) (index : Fin size) :
    (report.project index).steps.map InFlight.Replay.Step.event =
      Safety.packetEvents context index (report.steps.map Step.event) := by
  simp [Report.project, Safety.packetEvents, List.map_map, Function.comp_def]

theorem Report.project_source (report : Report context headers actions) (index : Fin size) (slot : Nat)
    (projected : InFlight.Replay.Step (context.packets.get index) (headers.get index))
    (found : (report.project index).steps[slot]? = some projected) :
    ∃ source, report.steps[slot]? = some source ∧ source.project index = projected := by
  change (report.steps.map (fun step => step.project index))[slot]? = some projected at found
  rw [List.getElem?_map] at found
  cases selected : report.steps[slot]? with
  | none => simp [selected] at found
  | some source =>
    simp only [selected, Option.map_some, Option.some.injEq] at found
    exact ⟨source, rfl, found⟩

theorem Chained.take_trace {before after : State input size} {steps : List (Step context headers)}
    (chain : Chained before steps after) (cut : Nat) (within : cut ≤ steps.length) :
    (Execution.system context headers).Trace before ((steps.take cut).map Step.event) (stateAt before steps cut) := by
  induction steps generalizing before cut with
  | nil =>
    have zero : cut = 0 := by simpa using within
    subst cut
    exact .nil before
  | cons step rest ih =>
    obtain ⟨same, tail⟩ := chain
    cases cut with
    | zero => exact .nil before
    | succ cut =>
      have edge := step.checked
      rw [same] at edge
      exact .cons edge (ih tail cut (by simpa only [List.length_cons, Nat.succ_le_succ_iff] using within))

theorem Report.prefix_trace (report : Report context headers actions) (cut : Nat) (within : cut ≤ report.steps.length) :
    (Execution.system context headers).Trace (initialState context)
      ((report.steps.take cut).map Step.event) (report.prefix.state cut) := report.chained.take_trace cut within

theorem Report.clock (report : Report context headers actions) (cut : Nat) (within : cut ≤ report.steps.length) :
    (report.prefix.state cut).nextIndex = cut := by
  have clock := Execution.initial_trace_index context headers (report.prefix_trace cut within)
  simpa only [List.length_map, List.length_take, Nat.min_eq_left within] using clock

theorem Report.step_clock (report : Report context headers actions) (slot : Nat) (step : Step context headers)
    (found : report.steps[slot]? = some step) : step.before.nextIndex = slot := by
  have clock := report.clock slot (Nat.le_of_lt (List.getElem?_eq_some_iff.mp found).1)
  rw [(report.prefix_before slot step found).2] at clock
  exact clock

structure SendOrigin (report : Report context headers actions) (index : Fin size) (stamp : InFlight.Stamp input) where
  source : Step context headers
  found : report.steps[stamp.sendIndex]? = some source
  projected : InFlight.Replay.SendOrigin (report.project index) stamp
  sourceEq : source.project index = projected.source
  action : source.action = .send projected.observation stamp.target

theorem Report.lift_send (report : Report context headers actions) (index : Fin size) (stamp : InFlight.Stamp input)
    (projected : InFlight.Replay.SendOrigin (report.project index) stamp) : Nonempty (SendOrigin report index stamp) := by
  obtain ⟨source, found, same⟩ := report.project_source index stamp.sendIndex projected.source projected.found
  have action : projectAction context source.action index = .send projected.observation stamp.target := by
    rw [← Step.project_action, same]; exact projected.action
  have nonidle : projectAction context source.action index ≠ .idle := by rw [action]; simp
  have raw := Safety.projectAction_eq_of_ne_idle context source.action index nonidle
  exact ⟨⟨source, found, projected, same, raw.symm.trans action⟩⟩

theorem SendOrigin.clock {report : Report context headers actions} {index : Fin size} {stamp : InFlight.Stamp input}
    (value : SendOrigin report index stamp) : value.source.before.nextIndex = stamp.sendIndex :=
  report.step_clock _ _ value.found

theorem SendOrigin.held {report : Report context headers actions} {index : Fin size} {stamp : InFlight.Stamp input}
    (value : SendOrigin report index stamp) : (value.source.before.packet index).phase = .held stamp.source := by
  rw [← Step.project_before, value.sourceEq]; exact value.projected.held

theorem SendOrigin.current {report : Report context headers actions} {index : Fin size} {stamp : InFlight.Stamp input}
    (value : SendOrigin report index stamp) : stamp.current = value.source.before.current := by
  have current := value.projected.current
  rw [← value.sourceEq] at current
  exact current

theorem SendOrigin.sent {report : Report context headers actions} {index : Fin size} {stamp : InFlight.Stamp input}
    (value : SendOrigin report index stamp) : value.source.event.effects.get index = .sent stamp := by
  have sent := value.projected.sent
  rw [← value.sourceEq] at sent
  exact sent

theorem SendOrigin.packetID {report : Report context headers actions} {index : Fin size} {stamp : InFlight.Stamp input}
    (value : SendOrigin report index stamp) : stamp.packetID = (context.packets.get index).profile.packetID :=
  value.projected.packetID

theorem SendOrigin.headerEq {report : Report context headers actions} {index : Fin size} {stamp : InFlight.Stamp input}
    (value : SendOrigin report index stamp) : stamp.header = headers.get index := value.projected.headerEq

theorem SendOrigin.observationEq {report : Report context headers actions} {index : Fin size} {stamp : InFlight.Stamp input}
    (value : SendOrigin report index stamp) :
    value.projected.observation = (context.packets.get index).observation (headers.get index) stamp.source :=
  value.projected.observationEq

theorem SendOrigin.after {report : Report context headers actions} {index : Fin size} {stamp : InFlight.Stamp input}
    (value : SendOrigin report index stamp) : (value.source.after.packet index).phase = .flight stamp := by
  rw [← Step.project_after, value.sourceEq]; exact value.projected.after

theorem SendOrigin.raw_action {report : Report context headers actions} {index : Fin size} {stamp : InFlight.Stamp input}
    (value : SendOrigin report index stamp) : actions[stamp.sendIndex]? = some (.send value.projected.observation stamp.target) := by
  calc
    actions[stamp.sendIndex]? = (report.steps.map Step.action)[stamp.sendIndex]? :=
      congrArg (fun entries : List InFlight.Action => entries[stamp.sendIndex]?) report.covered.symm
    _ = some (.send value.projected.observation stamp.target) := by
      rw [List.getElem?_map, value.found, Option.map_some]
      exact congrArg some value.action

theorem SendOrigin.native_source (deployment : Deployment.Checked input)
    {report : Report context headers actions} {index : Fin size} {stamp : InFlight.Stamp input}
    (value : SendOrigin report index stamp) :
    Nonempty (Provenance.Origin input.left.contract input.right.contract
      (input.left.revisionAt stamp.current.1) (input.right.revisionAt stamp.current.2)
      (context.packets.get index).first (context.packets.get index).second input.intent (headers.get index)
      stamp.source stamp.target) := value.projected.native_source deployment

theorem Report.flight_source (report : Report context headers actions) (index : Fin size)
    (cut : Nat) (within : cut ≤ report.steps.length) (stamp : InFlight.Stamp input)
    (flight : ((report.prefix.state cut).packet index).phase = .flight stamp) :
    Nonempty (SendOrigin report index stamp) ∧ stamp.sendIndex < cut := by
  obtain ⟨⟨projected⟩, earlier⟩ := (report.project index).flight_source cut (by simpa using within) stamp
    (by rw [report.project_state]; exact flight)
  exact ⟨report.lift_send index stamp projected, earlier⟩

theorem Report.arrival_source (report : Report context headers actions) (slot : Nat) (step : Step context headers)
    (found : report.steps[slot]? = some step) (observation : InFlight.Observation) (sendIndex : Nat)
    (action : step.action = .arrive observation sendIndex) :
    ∃ index stamp, (step.before.packet index).phase = .flight stamp ∧ step.event.effects.get index = .arrived stamp ∧
      sendIndex = stamp.sendIndex ∧ Nonempty (SendOrigin report index stamp) ∧ stamp.sendIndex < slot := by
  cases selected : packetIndex context observation.packetID with
  | none =>
    obtain ⟨move, classified, _⟩ := step.advanced.facts.keyStep
    rw [action] at classified
    simp only [actionMove, selected] at classified
    cases classified
  | some index =>
    have projectedAction : projectAction context step.action index = step.action := by
      simp [projectAction, action, actionMove, selected]
    have projectedFound : (report.project index).steps[slot]? = some (step.project index) := by
      simp only [Report.project, List.getElem?_map, found, Option.map_some]
    obtain ⟨stamp, flight, arrived, sameIndex, ⟨origin⟩, earlier⟩ :=
      (report.project index).arrival_source slot (step.project index) projectedFound
        (by rw [Step.project_action, projectedAction]; exact action)
    exact ⟨index, stamp, flight, arrived, sameIndex, report.lift_send index stamp origin, earlier⟩

structure ReceiptOrigin (report : Report context headers actions) (index : Fin size) (receipt : Nat) where
  source : Step context headers
  found : report.steps[receipt]? = some source
  projected : InFlight.Replay.ReceiptOrigin (report.project index) receipt
  sourceEq : source.project index = projected.source
  action : source.action = .receive projected.observation

theorem Report.lift_receipt (report : Report context headers actions) (index : Fin size) (receipt : Nat)
    (projected : InFlight.Replay.ReceiptOrigin (report.project index) receipt) : Nonempty (ReceiptOrigin report index receipt) := by
  obtain ⟨source, found, same⟩ := report.project_source index receipt projected.source projected.found
  have action : projectAction context source.action index = .receive projected.observation := by
    rw [← Step.project_action, same]; exact projected.source.received_action projected.received
  have nonidle : projectAction context source.action index ≠ .idle := by rw [action]; simp
  have raw := Safety.projectAction_eq_of_ne_idle context source.action index nonidle
  exact ⟨⟨source, found, projected, same, raw.symm.trans action⟩⟩

theorem ReceiptOrigin.clock {report : Report context headers actions} {index : Fin size} {receipt : Nat}
    (value : ReceiptOrigin report index receipt) : value.source.before.nextIndex = receipt := report.step_clock _ _ value.found

theorem ReceiptOrigin.received {report : Report context headers actions} {index : Fin size} {receipt : Nat}
    (value : ReceiptOrigin report index receipt) : value.source.event.effects.get index =
      .received value.projected.observation value.projected.current receipt := by
  have received := value.projected.received
  rw [← value.sourceEq] at received
  exact received

theorem ReceiptOrigin.raw_action {report : Report context headers actions} {index : Fin size} {receipt : Nat}
    (value : ReceiptOrigin report index receipt) : actions[receipt]? = some (.receive value.projected.observation) := by
  calc
    actions[receipt]? = (report.steps.map Step.action)[receipt]? :=
      congrArg (fun entries : List InFlight.Action => entries[receipt]?) report.covered.symm
    _ = some (.receive value.projected.observation) := by
      rw [List.getElem?_map, value.found, Option.map_some]
      exact congrArg some value.action

theorem ReceiptOrigin.observationEq {report : Report context headers actions} {index : Fin size} {receipt : Nat}
    (value : ReceiptOrigin report index receipt) : ∃ node,
      value.projected.observation = (context.packets.get index).observation (headers.get index) node := by
  have observed := value.projected.source.advanced.observations
  rw [value.projected.source.received_action value.projected.received] at observed
  cases phase : value.projected.source.before.phase with
  | flight stamp => simp [InFlight.Execution.observationsMatch, phase] at observed
  | delivered clock => simp [InFlight.Execution.observationsMatch, phase] at observed
  | held node => exact ⟨node, by simpa only [InFlight.Execution.observationsMatch, phase, decide_eq_true_eq] using observed⟩

theorem ReceiptOrigin.packetID {report : Report context headers actions} {index : Fin size} {receipt : Nat}
    (value : ReceiptOrigin report index receipt) : value.projected.observation.packetID = (context.packets.get index).profile.packetID := by
  obtain ⟨node, same⟩ := value.observationEq
  rw [same]; rfl

theorem ReceiptOrigin.headerEq {report : Report context headers actions} {index : Fin size} {receipt : Nat}
    (value : ReceiptOrigin report index receipt) : value.projected.observation.header = headers.get index := by
  obtain ⟨node, same⟩ := value.observationEq
  rw [same]; rfl

theorem Report.delivered_source (report : Report context headers actions) (index : Fin size)
    (cut : Nat) (within : cut ≤ report.steps.length) (receipt : Nat)
    (delivered : ((report.prefix.state cut).packet index).phase = .delivered receipt) :
    Nonempty (ReceiptOrigin report index receipt) ∧ receipt < cut := by
  obtain ⟨⟨projected⟩, earlier⟩ := (report.project index).delivered_source cut (by simpa using within) receipt
    (by rw [report.project_state]; exact delivered)
  exact ⟨report.lift_receipt index receipt projected, earlier⟩

end Netlib.Federation.Cohort.Replay
