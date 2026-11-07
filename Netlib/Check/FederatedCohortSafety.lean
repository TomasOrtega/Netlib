import Netlib.Check.FederatedCohortComponents
import Netlib.Check.FederatedCohortProjection
import Netlib.Check.FederatedPacketSafety
import Netlib.Check.FederatedPacketHistory

/-!
# Common histories in the actual shared execution

Packet projections retain every global slot. Historical held states and
source stamps therefore refer to the same shared clock and event list.
-/

namespace Netlib.Federation.Cohort

variable {input : Input} {size : Nat}

def Component.validated {context : Context input size} {index : Fin size} (value : Component context index) :
    InFlight.Context.Validated value.certificate.deployment (context.packets.get index) :=
  value.contextEq ▸ value.certificate.valid

namespace Safety

def packetEvents (context : Context input size) (index : Fin size) (events : List (Event input size)) :
    List (InFlight.Event input) := events.map (fun event => event.packet context index)

theorem packet_trace (context : Context input size) (headers : Vector Packet.Header size)
    {events : List (Event input size)} {after : State input size}
    (trace : (Execution.system context headers).Trace (initialState context) events after) (index : Fin size) :
    (InFlight.Execution.system (context.packets.get index) (headers.get index)).Trace
      (InFlight.initialState (context.packets.get index)) (packetEvents context index events) (after.packet index) := by
  simpa only [initialState_packet, packetEvents] using Execution.project_trace context headers trace index

private theorem single_step_unique {context : InFlight.Context input} {header : Packet.Header}
    {before first second : InFlight.State input} {event : InFlight.Event input}
    (left : (InFlight.Execution.system context header).step before event first)
    (right : (InFlight.Execution.system context header).step before event second) : first = second := by
  obtain ⟨a, aSuccess, aState, _⟩ := left
  obtain ⟨b, bSuccess, bState, _⟩ := right
  have same : a = b := Except.ok.inj (aSuccess.symm.trans bSuccess)
  exact aState.symm.trans (same ▸ bState)

private theorem single_trace_unique {context : InFlight.Context input} {header : Packet.Header}
    {before first second : InFlight.State input} {events : List (InFlight.Event input)}
    (left : (InFlight.Execution.system context header).Trace before events first)
    (right : (InFlight.Execution.system context header).Trace before events second) : first = second := by
  induction left generalizing second with
  | nil => cases right; rfl
  | cons step _ ih =>
    cases right with
    | cons other tail =>
      have same := single_step_unique step other
      subst same
      exact ih tail

theorem lift_prefix (context : Context input size) (headers : Vector Packet.Header size) (index : Fin size)
    {events : List (Event input size)} {after : State input size}
    (trace : (Execution.system context headers).Trace (initialState context) events after)
    {prior later : List (InFlight.Event input)} {state : InFlight.State input}
    (splitEvents : packetEvents context index events = prior ++ later)
    (first : (InFlight.Execution.system (context.packets.get index) (headers.get index)).Trace
      (InFlight.initialState (context.packets.get index)) prior state) :
    ∃ middle, (Execution.system context headers).Trace (initialState context) (events.take prior.length) middle ∧
      (Execution.system context headers).Trace middle (events.drop prior.length) after ∧
      middle.packet index = state ∧ middle.nextIndex = prior.length := by
  have mapped : packetEvents context index (events.take prior.length) = prior := by
    change (events.take prior.length).map (fun event => event.packet context index) = prior
    rw [List.map_take, ← packetEvents, splitEvents]
    simp
  have whole : events.take prior.length ++ events.drop prior.length = events := List.take_append_drop _ _
  obtain ⟨middle, initialTrace, suffix⟩ := (whole.symm ▸ trace).split
  have projected := packet_trace context headers initialTrace index
  rw [mapped] at projected
  have same := single_trace_unique projected first
  have enough : prior.length ≤ events.length := by
    have lengths := congrArg List.length splitEvents
    simp only [packetEvents, List.length_map, List.length_append] at lengths
    omega
  refine ⟨middle, initialTrace, suffix, same, ?_⟩
  simpa only [List.length_take, Nat.min_eq_left enough] using Execution.initial_trace_index context headers initialTrace

def HeldWithin (context : Context input size) (headers : Vector Packet.Header size) (index : Fin size)
    (events : List (Event input size)) (after : State input size) (reference : PublicRef) : Prop :=
  ∃ prior later state node, events = prior ++ later ∧
    (Execution.system context headers).Trace (initialState context) prior state ∧
    (Execution.system context headers).Trace state later after ∧
    (state.packet index).phase = .held node ∧
    InFlight.Control.project input state.current node = reference ∧ state.nextIndex = prior.length

theorem lift_held (context : Context input size) (headers : Vector Packet.Header size) (index : Fin size)
    {events : List (Event input size)} {after : State input size}
    (trace : (Execution.system context headers).Trace (initialState context) events after) {reference : PublicRef}
    (held : InFlight.Safety.HeldWithin (context.packets.get index) (headers.get index)
      (packetEvents context index events) (after.packet index) reference) :
    HeldWithin context headers index events after reference := by
  obtain ⟨prior, later, state, node, same, first, _, phase, visible⟩ := held
  obtain ⟨middle, initialTrace, suffix, projected, clock⟩ := lift_prefix context headers index trace same first
  refine ⟨events.take prior.length, events.drop prior.length, middle, node,
    (List.take_append_drop _ _).symm, initialTrace, suffix, ?_, ?_, ?_⟩
  · rw [projected]; exact phase
  · have current := congrArg InFlight.State.current projected
    change middle.current = state.current at current
    rw [current]; exact visible
  · have length := congrArg List.length same
    simp only [packetEvents, List.length_map, List.length_append] at length
    simp only [List.length_take, clock]
    omega

structure CommonHistory (context : Context input size) (headers : Vector Packet.Header size) (index : Fin size)
    (events : List (Event input size)) (after : State input size) : Prop where
  projected : InFlight.Safety.CommonHistory (context.packets.get index) (headers.get index)
    (packetEvents context index events) (after.packet index)
  held : ∀ reference ∈ InFlight.Safety.publicHistory (context.packets.get index) (packetEvents context index events),
    HeldWithin context headers index events after reference

theorem common_history {context : Context input size} (family : Family context)
    (headers : Vector Packet.Header size) (accepted : Accepted context headers)
    {events : List (Event input size)} {after : State input size}
    (trace : (Execution.system context headers).Trace (initialState context) events after) (index : Fin size) :
    CommonHistory context headers index events after := by
  have history := InFlight.Safety.common_history (family.component index).validated (headers.get index)
    (accepted index) (packet_trace context headers trace index)
  exact ⟨history, fun reference member => lift_held context headers index trace (history.held reference member)⟩

theorem prefix_history {context : Context input size} (family : Family context)
    (headers : Vector Packet.Header size) (accepted : Accepted context headers)
    {prior later : List (Event input size)} {after : State input size}
    (trace : (Execution.system context headers).Trace (initialState context) (prior ++ later) after) :
    ∃ middle, (Execution.system context headers).Trace (initialState context) prior middle ∧
      (Execution.system context headers).Trace middle later after ∧
      ∀ index, CommonHistory context headers index prior middle := by
  obtain ⟨middle, first, rest⟩ := trace.split
  exact ⟨middle, first, rest, fun index => common_history family headers accepted first index⟩

theorem CommonHistory.reachable {context : Context input size} {headers : Vector Packet.Header size} {index : Fin size}
    {events : List (Event input size)} {after : State input size} (history : CommonHistory context headers index events after) :
    (InFlight.Safety.upper (context.packets.get index)).Reachable (context.packets.get index).query.source
      (InFlight.Safety.publicPosition (context.packets.get index) (after.packet index)) := history.projected.reachable

theorem isolate {context : Context input size} (family : Family context)
    (headers : Vector Packet.Header size) (accepted : Accepted context headers)
    {events : List (Event input size)} {after : State input size}
    (trace : (Execution.system context headers).Trace (initialState context) events after) (index : Fin size)
    (query : Query) (member : query ∈ input.intent.queries) (kind : query.kind = .isolate)
    (sameCase : query.caseID = (context.packets.get index).query.caseID)
    (sameSource : query.source = (context.packets.get index).query.source) :
    InFlight.Safety.publicPosition (context.packets.get index) (after.packet index) ≠ query.target :=
  InFlight.Safety.isolate (family.component index).validated (headers.get index) (accepted index)
    (packet_trace context headers trace index) query member kind sameCase sameSource

structure PEPVisit (context : Context input size) (headers : Vector Packet.Header size) (index : Fin size)
    (events : List (Event input size)) (after : State input size) (query : Query) (side : Side) where
  prior : List (Event input size)
  later : List (Event input size)
  state : State input size
  node : InFlight.Node
  eventsEq : events = prior ++ later
  first : (Execution.system context headers).Trace (initialState context) prior state
  rest : (Execution.system context headers).Trace state later after
  held : (state.packet index).phase = .held node
  known : InFlight.Control.known input state.current node = true
  gateway : InFlight.Control.project input state.current node ∈ query.gateways
  enforcement : Composition.EnforcementOn side (input.left.revisionAt state.current.1)
    (input.right.revisionAt state.current.2) node
  clock : state.nextIndex = prior.length

theorem mediated_on {context : Context input size} (family : Family context)
    (headers : Vector Packet.Header size) (accepted : Accepted context headers)
    {events : List (Event input size)} {after : State input size}
    (trace : (Execution.system context headers).Trace (initialState context) events after) (index : Fin size)
    (query : Query) (member : query ∈ input.intent.queries) (kind : query.kind = .mediated)
    (sameCase : query.caseID = (context.packets.get index).query.caseID)
    (sameSource : query.source = (context.packets.get index).query.source)
    (reached : InFlight.Safety.publicPosition (context.packets.get index) (after.packet index) = query.target)
    (side : Side) (checkedSide : query.gateways.all (fun gateway => decide (gateway.side = side)) = true) :
    Nonempty (PEPVisit context headers index events after query side) := by
  obtain ⟨visit⟩ := InFlight.Safety.mediated_on (family.component index).validated (headers.get index)
    (accepted index) (packet_trace context headers trace index) query member kind sameCase sameSource reached side checkedSide
  obtain ⟨middle, initialTrace, suffix, projected, clock⟩ := lift_prefix context headers index trace visit.eventsEq visit.first
  have current := congrArg InFlight.State.current projected
  change middle.current = visit.state.current at current
  refine ⟨⟨events.take visit.prior.length, events.drop visit.prior.length, middle, visit.node,
    (List.take_append_drop _ _).symm, initialTrace, suffix, ?_, ?_, ?_, ?_, ?_⟩⟩
  · rw [projected]; exact visit.held
  · rw [current]; exact visit.known
  · rw [current]; exact visit.gateway
  · rw [current]; exact visit.enforcement
  · have lengths := congrArg List.length visit.eventsEq
    simp only [packetEvents, List.length_map, List.length_append] at lengths
    simp only [List.length_take, clock]
    omega

theorem event_at (context : Context input size) (headers : Vector Packet.Header size)
    {before after : State input size} {events : List (Event input size)}
    (trace : (Execution.system context headers).Trace before events after)
    (slot : Nat) (event : Event input size) (found : events[slot]? = some event) :
    ∃ source target, (Execution.system context headers).Trace before (events.take slot) source ∧
      (Execution.system context headers).step source event target ∧
      (Execution.system context headers).Trace target (events.drop (slot + 1)) after := by
  induction trace generalizing slot with
  | nil => simp at found
  | @cons before middle after first rest step tail ih =>
    cases slot with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at found
      subst event
      exact ⟨before, middle, .nil _, step, tail⟩
    | succ slot =>
      simp only [List.getElem?_cons_succ] at found
      obtain ⟨source, target, earlier, current, later⟩ := ih slot found
      exact ⟨source, target, .cons step earlier, current, later⟩

theorem projected_event_at (context : Context input size) (index : Fin size)
    (events : List (Event input size)) (slot : Nat) (projected : InFlight.Event input)
    (found : (packetEvents context index events)[slot]? = some projected) :
    ∃ event, events[slot]? = some event ∧ event.packet context index = projected := by
  cases selected : events[slot]? with
  | none => simp [packetEvents, List.getElem?_map, selected] at found
  | some event =>
    simp only [packetEvents, List.getElem?_map, selected, Option.map_some, Option.some.injEq] at found
    exact ⟨event, rfl, found⟩

theorem projectAction_eq_of_ne_idle (context : Context input size) (action : InFlight.Action) (index : Fin size)
    (nonidle : projectAction context action index ≠ .idle) : projectAction context action index = action := by
  cases selected : actionMove context action with
  | error reason => simp [projectAction, selected] at nonidle
  | ok move =>
    cases move with
    | none => simp [projectAction, selected] at nonidle
    | some move =>
      cases move with
      | packet actor operation =>
        by_cases same : actor = index
        · simp [projectAction, selected, same]
        · simp [projectAction, selected, same] at nonidle
      | updateLeft => simp [projectAction, selected]
      | updateRight => simp [projectAction, selected]
      | updateBoth => simp [projectAction, selected]

theorem flight_origin (context : Context input size) (headers : Vector Packet.Header size)
    {events : List (Event input size)} {after : State input size}
    (trace : (Execution.system context headers).Trace (initialState context) events after)
    (index : Fin size) (stamp : InFlight.Stamp input) (flight : (after.packet index).phase = .flight stamp) :
    ∃ event source target observation, events[stamp.sendIndex]? = some event ∧
      (Execution.system context headers).Trace (initialState context) (events.take stamp.sendIndex) source ∧
      (Execution.system context headers).step source event target ∧
      event.action = .send observation stamp.target ∧ event.effects.get index = .sent stamp ∧
      (source.packet index).phase = .held stamp.source ∧ stamp.current = source.current ∧
      stamp.packetID = (context.packets.get index).profile.packetID ∧ stamp.header = headers.get index ∧
      source.nextIndex = stamp.sendIndex ∧ stamp.sendIndex < events.length := by
  obtain ⟨projected, found, sent, within⟩ := InFlight.History.trace_flight_origin (packet_trace context headers trace index) flight
  obtain ⟨event, actual, same⟩ := projected_event_at context index events stamp.sendIndex projected found
  obtain ⟨source, target, first, step, _⟩ := event_at context headers trace stamp.sendIndex event actual
  have effect : (event.packet context index).effect = .sent stamp := same ▸ sent
  obtain ⟨observation, action, held, current, packetID, header, clock, _⟩ :=
    InFlight.History.step_sent (Execution.project_step context headers step index) effect
  have nonidle : projectAction context event.action index ≠ .idle := by
    change (event.packet context index).action ≠ .idle
    rw [action]
    simp
  have projectedAction := projectAction_eq_of_ne_idle context event.action index nonidle
  refine ⟨event, source, target, observation, actual, first, step, ?_, effect, held, current, packetID, header, clock.symm, ?_⟩
  · exact projectedAction.symm.trans action
  · simpa only [packetEvents, List.length_map] using within

theorem arrival_origin (context : Context input size) (headers : Vector Packet.Header size)
    {events : List (Event input size)} {before after : State input size} {event : Event input size}
    (trace : (Execution.system context headers).Trace (initialState context) events before)
    (step : (Execution.system context headers).step before event after)
    (index : Fin size) (stamp : InFlight.Stamp input) (arrived : event.effects.get index = .arrived stamp) :
    ∃ sent source target observation, events[stamp.sendIndex]? = some sent ∧
      (Execution.system context headers).Trace (initialState context) (events.take stamp.sendIndex) source ∧
      (Execution.system context headers).step source sent target ∧
      sent.action = .send observation stamp.target ∧ sent.effects.get index = .sent stamp ∧
      (source.packet index).phase = .held stamp.source ∧ stamp.current = source.current ∧
      stamp.packetID = (context.packets.get index).profile.packetID ∧ stamp.header = headers.get index ∧
      source.nextIndex = stamp.sendIndex ∧ stamp.sendIndex < events.length := by
  have flight := (InFlight.History.step_arrived (Execution.project_step context headers step index) arrived).1
  exact flight_origin context headers trace index stamp flight

private theorem received_facts {context : InFlight.Context input} {header : Packet.Header}
    {before after : InFlight.State input} {event : InFlight.Event input}
    (step : (InFlight.Execution.system context header).step before event after)
    {observation : InFlight.Observation} {current : InFlight.Cursors input} {receipt : Nat}
    (received : event.effect = .received observation current receipt) :
    event.action = .receive observation ∧ observation.packetID = context.profile.packetID ∧
      observation.header = header ∧ current = before.current ∧ receipt = before.nextIndex := by
  obtain ⟨outcome, facts, _, effectEq⟩ := InFlight.Execution.step_facts context header step
  have resultEq := congrArg InFlight.Outcome.effect facts.candidateEq
  rw [effectEq, received] at resultEq
  have observed := facts.observations
  rcases before with ⟨cursor, phase, clock⟩
  cases action : event.action <;> cases phase <;> simp! [InFlight.Execution.candidate, action] at resultEq
  cases resultEq
  simp only [action, InFlight.Execution.observationsMatch, decide_eq_true_eq] at observed
  rw [observed]
  cases observation
  simp_all [InFlight.Context.observation]

theorem delivery_origin (context : Context input size) (headers : Vector Packet.Header size)
    {events : List (Event input size)} {after : State input size}
    (trace : (Execution.system context headers).Trace (initialState context) events after)
    (index : Fin size) (receipt : Nat) (delivered : (after.packet index).phase = .delivered receipt) :
    ∃ event observation current, events[receipt]? = some event ∧
      event.effects.get index = .received observation current receipt ∧
      event.action = .receive observation ∧ observation.packetID = (context.packets.get index).profile.packetID ∧
      observation.header = headers.get index ∧
      receipt < events.length := by
  obtain ⟨projected, observation, current, found, received, within⟩ :=
    InFlight.History.trace_delivery_origin (packet_trace context headers trace index) delivered
  obtain ⟨event, actual, same⟩ := projected_event_at context index events receipt projected found
  have effect : (event.packet context index).effect = .received observation current receipt := same ▸ received
  obtain ⟨source, target, _, step, _⟩ := event_at context headers trace receipt event actual
  have facts := received_facts (Execution.project_step context headers step index) effect
  have nonidle : projectAction context event.action index ≠ .idle := by
    change (event.packet context index).action ≠ .idle
    rw [facts.1]
    simp
  have projectedAction := projectAction_eq_of_ne_idle context event.action index nonidle
  exact ⟨event, observation, current, actual, effect, projectedAction.symm.trans facts.1, facts.2.1, facts.2.2.1,
    by simpa only [packetEvents, List.length_map] using within⟩

theorem flight_identity_unique (context : Context input size) (unique : context.Unique)
    (headers : Vector Packet.Header size) {events : List (Event input size)} {after : State input size}
    (trace : (Execution.system context headers).Trace (initialState context) events after)
    (first second : Fin size) (a b : InFlight.Stamp input)
    (firstFlight : (after.packet first).phase = .flight a) (secondFlight : (after.packet second).phase = .flight b)
    (sameID : a.packetID = b.packetID) : first = second := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, aID, _, _, _⟩ := flight_origin context headers trace first a firstFlight
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, bID, _, _, _⟩ := flight_origin context headers trace second b secondFlight
  exact unique.packetID_injective first second (aID.symm.trans (sameID.trans bID))

private theorem single_delivered_stays {context : InFlight.Context input} {header : Packet.Header}
    {before after : InFlight.State input} {event : InFlight.Event input} {receipt : Nat}
    (delivered : before.phase = .delivered receipt)
    (step : (InFlight.Execution.system context header).step before event after) : after.phase = .delivered receipt := by
  obtain ⟨outcome, facts, stateEq, _⟩ := InFlight.Execution.step_facts context header step
  have observed := facts.observations
  have phaseEq := congrArg (fun value : InFlight.Outcome input => value.after.phase) facts.candidateEq
  rw [stateEq] at phaseEq
  cases action : event.action <;> simp_all! [InFlight.Execution.observationsMatch, InFlight.Execution.candidate]

theorem delivered_stays (context : Context input size) (headers : Vector Packet.Header size)
    {before after : State input size} {events : List (Event input size)} (index : Fin size) (receipt : Nat)
    (delivered : (before.packet index).phase = .delivered receipt)
    (trace : (Execution.system context headers).Trace before events after) :
    (after.packet index).phase = .delivered receipt := by
  induction trace with
  | nil => exact delivered
  | cons step _ ih => exact ih (single_delivered_stays delivered (Execution.project_step context headers step index))

end Safety
end Netlib.Federation.Cohort
