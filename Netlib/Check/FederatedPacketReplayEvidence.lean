import Netlib.Check.FederatedPacketReplay
import Netlib.Check.FederatedPacketHistory

/-!
# Exact source rows in packet reports

Historical send and receipt indices select actual stored replay steps.
An arrival retains its earlier sender revision and complete send stamp.
-/

namespace Netlib.Federation.InFlight.Replay

variable {input : Input} {context : Context input} {header : Packet.Header} {actions : List Action}

theorem Chained.take_trace {before after : State input} {steps : List (Step context header)}
    (chain : Chained before steps after) (cut : Nat) (within : cut ≤ steps.length) :
    (Execution.system context header).Trace before ((steps.take cut).map Step.event) (stateAt before steps cut) := by
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

theorem Report.prefix_trace (report : Report context header actions) (cut : Nat) (within : cut ≤ report.steps.length) :
    (Execution.system context header).Trace (initialState context)
      ((report.steps.take cut).map Step.event) (report.prefix.state cut) :=
  report.chained.take_trace cut within

theorem Report.clock (report : Report context header actions) (cut : Nat) (within : cut ≤ report.steps.length) :
    (report.prefix.state cut).nextIndex = cut := by
  have clock := History.trace_clock (report.prefix_trace cut within)
  simpa only [initialState, List.length_map, List.length_take, Nat.min_eq_left within, Nat.zero_add] using clock

theorem Report.step_clock (report : Report context header actions) (index : Nat)
    (step : Step context header) (found : report.steps[index]? = some step) : step.before.nextIndex = index := by
  have within := (List.getElem?_eq_some_iff.mp found).1
  have clock := report.clock index (Nat.le_of_lt within)
  rw [(report.prefix_before index step found).2] at clock
  exact clock

theorem Report.event_source (report : Report context header actions) (index : Nat) (event : Event input)
    (found : (report.steps.map Step.event)[index]? = some event) :
    ∃ step, report.steps[index]? = some step ∧ step.event = event := by
  rw [List.getElem?_map] at found
  cases selected : report.steps[index]? with
  | none => simp [selected] at found
  | some step =>
    simp only [selected, Option.map_some, Option.some.injEq] at found
    exact ⟨step, rfl, found⟩

structure SendOrigin (report : Report context header actions) (stamp : Stamp input) where
  source : Step context header
  found : report.steps[stamp.sendIndex]? = some source
  sent : source.event.effect = .sent stamp
  clock : source.before.nextIndex = stamp.sendIndex
  observation : Observation
  action : source.action = .send observation stamp.target
  observationEq : observation = context.observation header stamp.source
  held : source.before.phase = .held stamp.source
  current : stamp.current = source.before.current
  packetID : stamp.packetID = context.profile.packetID
  headerEq : stamp.header = header
  after : source.after.phase = .flight stamp

theorem Report.send_origin (report : Report context header actions) (stamp : Stamp input)
    (source : Step context header) (found : report.steps[stamp.sendIndex]? = some source)
    (sent : source.event.effect = .sent stamp) : Nonempty (SendOrigin report stamp) := by
  obtain ⟨observation, action, held, current, packetID, headerEq, _, after⟩ := History.step_sent source.checked sent
  have actionEq : source.action = .send observation stamp.target := action
  have observed := source.advanced.observations
  rw [actionEq] at observed
  have observationEq : observation = context.observation header stamp.source := by
    simpa only [Execution.observationsMatch, held, decide_eq_true_eq] using observed
  exact ⟨⟨source, found, sent, report.step_clock _ source found, observation, actionEq,
    observationEq, held, current, packetID, headerEq, after⟩⟩

theorem Report.flight_source (report : Report context header actions) (cut : Nat) (within : cut ≤ report.steps.length)
    (stamp : Stamp input) (flight : (report.prefix.state cut).phase = .flight stamp) :
    Nonempty (SendOrigin report stamp) ∧ stamp.sendIndex < cut := by
  obtain ⟨event, found, sent, earlier⟩ := History.trace_flight_origin (report.prefix_trace cut within) flight
  have indexLt : stamp.sendIndex < cut := by
    simpa only [List.length_map, List.length_take, Nat.min_eq_left within] using earlier
  rw [List.getElem?_map, List.getElem?_take_of_lt indexLt] at found
  have whole : (report.steps.map Step.event)[stamp.sendIndex]? = some event := by
    simpa only [List.getElem?_map] using found
  obtain ⟨source, sourceFound, same⟩ := report.event_source stamp.sendIndex event whole
  exact ⟨report.send_origin stamp source sourceFound (same ▸ sent), indexLt⟩

variable {report : Report context header actions} {stamp : Stamp input}

theorem SendOrigin.native (value : SendOrigin report stamp) :
    Control.nativeEdge context header stamp.current stamp.source stamp.target = true ∧
      Control.known input stamp.current stamp.source = true ∧ Control.known input stamp.current stamp.target = true := by
  have selected := Execution.step_key context header value.source.checked
  change Execution.KeyStep context header value.source.before value.source.action value.source.after at selected
  simp only [Execution.KeyStep, value.action, Action.move?, Control.step, State.key, value.held, Phase.key] at selected
  split at selected
  · rename_i permitted
    rw [← value.current] at permitted
    simpa only [Bool.and_eq_true, and_assoc] using permitted
  · cases selected

theorem SendOrigin.native_source (deployment : Deployment.Checked input) (value : SendOrigin report stamp) :
    Nonempty (Provenance.Origin input.left.contract input.right.contract
      (input.left.revisionAt stamp.current.1) (input.right.revisionAt stamp.current.2)
      context.first context.second input.intent header stamp.source stamp.target) :=
  Provenance.edge_origin deployment.compatible _ _ context.first context.second header stamp.source stamp.target
    ((Control.nativeEdge_iff context header stamp.current stamp.source stamp.target).mp value.native.1)

theorem SendOrigin.raw_action (value : SendOrigin report stamp) :
    actions[stamp.sendIndex]? = some (.send value.observation stamp.target) := by
  calc
    actions[stamp.sendIndex]? = (report.steps.map Step.action)[stamp.sendIndex]? :=
      congrArg (fun entries : List Action => entries[stamp.sendIndex]?) report.covered.symm
    _ = some (.send value.observation stamp.target) := by
      rw [List.getElem?_map, value.found, Option.map_some]
      exact congrArg some value.action

theorem Report.arrival_source (report : Report context header actions) (index : Nat) (step : Step context header)
    (found : report.steps[index]? = some step) (action : step.action = .arrive observation sendIndex) :
    ∃ stamp, step.before.phase = .flight stamp ∧ step.event.effect = .arrived stamp ∧ sendIndex = stamp.sendIndex ∧
      Nonempty (SendOrigin report stamp) ∧ stamp.sendIndex < index := by
  obtain ⟨stamp, flight, arrived, _, _, _, sameIndex, _⟩ := History.step_arrive step.checked action
  have before := (report.prefix_before index step found).2
  have within := Nat.le_of_lt (List.getElem?_eq_some_iff.mp found).1
  have origins := report.flight_source index within stamp (by rw [before]; exact flight)
  exact ⟨stamp, flight, arrived, sameIndex, origins.1, origins.2⟩

structure ReceiptOrigin (report : Report context header actions) (index : Nat) where
  source : Step context header
  found : report.steps[index]? = some source
  observation : Observation
  current : Cursors input
  received : source.event.effect = .received observation current index
  clock : source.before.nextIndex = index

theorem Step.received_action (step : Step context header)
    (received : step.event.effect = .received observation current index) : step.action = .receive observation := by
  have resultEq : (Execution.candidate context header step.before step.action step.after.current).effect =
      .received observation current index :=
    (congrArg Outcome.effect step.advanced.candidateEq).trans received
  cases before : step.before with
  | mk cursor phase next =>
    cases action : step.action <;> cases phase <;> simp! [Execution.candidate, before, action] at resultEq
    simp_all

theorem ReceiptOrigin.raw_action (value : ReceiptOrigin report index) :
    actions[index]? = some (.receive value.observation) := by
  calc
    actions[index]? = (report.steps.map Step.action)[index]? :=
      congrArg (fun entries : List Action => entries[index]?) report.covered.symm
    _ = some (.receive value.observation) := by
      rw [List.getElem?_map, value.found, Option.map_some]
      exact congrArg some (value.source.received_action value.received)

theorem Report.delivered_source (report : Report context header actions) (cut : Nat) (within : cut ≤ report.steps.length)
    (index : Nat) (delivered : (report.prefix.state cut).phase = .delivered index) :
    Nonempty (ReceiptOrigin report index) ∧ index < cut := by
  obtain ⟨event, observation, current, found, received, earlier⟩ :=
    History.trace_delivery_origin (report.prefix_trace cut within) delivered
  have indexLt : index < cut := by
    simpa only [List.length_map, List.length_take, Nat.min_eq_left within] using earlier
  rw [List.getElem?_map, List.getElem?_take_of_lt indexLt] at found
  have whole : (report.steps.map Step.event)[index]? = some event := by
    simpa only [List.getElem?_map] using found
  obtain ⟨source, sourceFound, same⟩ := report.event_source index event whole
  exact ⟨⟨⟨source, sourceFound, observation, current, same ▸ received, report.step_clock index source sourceFound⟩⟩, indexLt⟩

end Netlib.Federation.InFlight.Replay
