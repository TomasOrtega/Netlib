import Netlib.Check.FederatedPacketExecution

/-!
# Actual packet event origins

Every retained stamp points to its exact earlier send in the same trace.
Receipt indices likewise identify the actual receiving event.
-/

namespace Netlib.Federation.InFlight.History

variable {input : Input} {context : Context input} {header : Packet.Header}

theorem trace_clock {before after : State input} {events : List (Event input)}
    (trace : (Execution.system context header).Trace before events after) :
    after.nextIndex = before.nextIndex + events.length := by
  induction trace with
  | nil => simp
  | cons step _ ih =>
    have tick := Execution.step_tick context header step
    simp only [List.length_cons]
    omega

theorem step_flight {before after : State input} {event : Event input} {stamp : Stamp input}
    (step : (Execution.system context header).step before event after)
    (flight : after.phase = .flight stamp) :
    before.phase = .flight stamp ∨ (event.effect = .sent stamp ∧ stamp.sendIndex = before.nextIndex) := by
  obtain ⟨outcome, facts, stateEq, effectEq⟩ := Execution.step_facts context header step
  have phaseEq := congrArg (fun value : Outcome input => value.after.phase) facts.candidateEq
  have resultEq := congrArg Outcome.effect facts.candidateEq
  rw [stateEq, flight] at phaseEq
  rw [effectEq] at resultEq
  rcases before with ⟨current, phase, index⟩
  cases action : event.action <;> cases phase <;>
    simp_all! [Execution.candidate]
  exact (congrArg Stamp.sendIndex phaseEq).symm

theorem step_delivered {before after : State input} {event : Event input} {index : Nat}
    (step : (Execution.system context header).step before event after)
    (delivered : after.phase = .delivered index) :
    before.phase = .delivered index ∨
      (∃ observation, event.effect = .received observation before.current index ∧ index = before.nextIndex) := by
  obtain ⟨outcome, facts, stateEq, effectEq⟩ := Execution.step_facts context header step
  have phaseEq := congrArg (fun value : Outcome input => value.after.phase) facts.candidateEq
  have resultEq := congrArg Outcome.effect facts.candidateEq
  rw [stateEq, delivered] at phaseEq
  rw [effectEq] at resultEq
  rcases before with ⟨current, phase, next⟩
  cases action : event.action <;> cases phase <;>
    simp_all! [Execution.candidate]
  exact ⟨_, resultEq.symm⟩

theorem step_arrive {before after : State input} {event : Event input}
    (step : (Execution.system context header).step before event after)
    (action : event.action = .arrive observation index) :
    ∃ stamp, before.phase = .flight stamp ∧ event.effect = .arrived stamp ∧
      observation = context.observation header stamp.target ∧ stamp.packetID = context.profile.packetID ∧
      stamp.header = header ∧ index = stamp.sendIndex ∧ after.phase = .held stamp.target := by
  obtain ⟨outcome, facts, stateEq, effectEq⟩ := Execution.step_facts context header step
  have observed := facts.observations
  rw [action] at observed
  cases phase : before.phase with
  | held node => simp [Execution.observationsMatch, phase] at observed
  | delivered received => simp [Execution.observationsMatch, phase] at observed
  | flight stamp =>
    have agrees : observation = context.observation header stamp.target ∧
        stamp.packetID = context.profile.packetID ∧ stamp.header = header ∧ index = stamp.sendIndex := by
      simpa only [Execution.observationsMatch, phase, decide_eq_true_eq] using observed
    have candidateEq := facts.candidateEq
    rw [action, Execution.candidate_arrive context header before observation index stamp outcome.after.current phase] at candidateEq
    have phaseEq := congrArg (fun value : Outcome input => value.after.phase) candidateEq
    have resultEq := congrArg Outcome.effect candidateEq
    rw [stateEq] at phaseEq
    rw [effectEq] at resultEq
    exact ⟨stamp, rfl, resultEq.symm, agrees.1, agrees.2.1, agrees.2.2.1, agrees.2.2.2, phaseEq.symm⟩

theorem step_arrived {before after : State input} {event : Event input} {stamp : Stamp input}
    (step : (Execution.system context header).step before event after)
    (arrived : event.effect = .arrived stamp) :
    before.phase = .flight stamp ∧ ∃ observation index, event.action = .arrive observation index := by
  obtain ⟨outcome, facts, stateEq, effectEq⟩ := Execution.step_facts context header step
  have resultEq := congrArg Outcome.effect facts.candidateEq
  rw [effectEq, arrived] at resultEq
  rcases before with ⟨current, phase, next⟩
  cases action : event.action <;> cases phase <;> simp_all! [Execution.candidate]

theorem step_sent {before after : State input} {event : Event input} {stamp : Stamp input}
    (step : (Execution.system context header).step before event after)
    (sent : event.effect = .sent stamp) :
    ∃ observation, event.action = .send observation stamp.target ∧ before.phase = .held stamp.source ∧
      stamp.current = before.current ∧ stamp.packetID = context.profile.packetID ∧ stamp.header = header ∧
      stamp.sendIndex = before.nextIndex ∧ after.phase = .flight stamp := by
  obtain ⟨outcome, facts, stateEq, effectEq⟩ := Execution.step_facts context header step
  have resultEq := congrArg Outcome.effect facts.candidateEq
  rw [effectEq, sent] at resultEq
  rcases before with ⟨current, phase, next⟩
  cases action : event.action <;> cases phase <;> simp! [Execution.candidate, action] at resultEq
  cases resultEq
  have phaseEq := congrArg (fun value : Outcome input => value.after.phase) facts.candidateEq
  simp! [Execution.candidate, action] at phaseEq
  rw [stateEq] at phaseEq
  simp_all

def FlightOrigin (events : List (Event input)) (state : State input) : Prop :=
  ∀ stamp, state.phase = .flight stamp →
    ∃ event, events[stamp.sendIndex]? = some event ∧ event.effect = .sent stamp ∧ stamp.sendIndex < events.length

def DeliveryOrigin (events : List (Event input)) (state : State input) : Prop :=
  ∀ index, state.phase = .delivered index →
    ∃ event observation current,
      events[index]? = some event ∧ event.effect = .received observation current index ∧ index < events.length

theorem flight_append {before after : State input} {event : Event input} {events : List (Event input)}
    (clock : before.nextIndex = events.length) (origin : FlightOrigin events before)
    (step : (Execution.system context header).step before event after) : FlightOrigin (events ++ [event]) after := by
  intro stamp flight
  rcases step_flight step flight with preserved | ⟨sent, indexEq⟩
  · obtain ⟨source, found, same, within⟩ := origin stamp preserved
    refine ⟨source, ?_, same, by simp only [List.length_append, List.length_singleton]; omega⟩
    rw [List.getElem?_append_left within]
    exact found
  · refine ⟨event, ?_, sent, ?_⟩
    · rw [indexEq, clock]
      simp
    · simp only [List.length_append, List.length_singleton]
      omega

theorem delivery_append {before after : State input} {event : Event input} {events : List (Event input)}
    (clock : before.nextIndex = events.length) (origin : DeliveryOrigin events before)
    (step : (Execution.system context header).step before event after) : DeliveryOrigin (events ++ [event]) after := by
  intro index delivered
  rcases step_delivered step delivered with preserved | ⟨observation, received, indexEq⟩
  · obtain ⟨source, observation, current, found, same, within⟩ := origin index preserved
    refine ⟨source, observation, current, ?_, same, by simp only [List.length_append, List.length_singleton]; omega⟩
    rw [List.getElem?_append_left within]
    exact found
  · refine ⟨event, observation, before.current, ?_, received, ?_⟩
    · rw [indexEq, clock]
      simp
    · simp only [List.length_append, List.length_singleton]
      omega

theorem trace_origins {before after : State input} {events history : List (Event input)}
    (trace : (Execution.system context header).Trace before events after)
    (clock : before.nextIndex = history.length)
    (flight : FlightOrigin history before) (delivered : DeliveryOrigin history before) :
    FlightOrigin (history ++ events) after ∧ DeliveryOrigin (history ++ events) after := by
  induction trace generalizing history with
  | nil => simpa using And.intro flight delivered
  | @cons before middle after event events step tail ih =>
    have nextClock : middle.nextIndex = (history ++ [event]).length := by
      rw [Execution.step_tick context header step, clock]
      simp
    have origins := ih nextClock (flight_append clock flight step) (delivery_append clock delivered step)
    simpa only [List.append_assoc, List.singleton_append] using origins

theorem trace_flight_origin {after : State input} {events : List (Event input)} {stamp : Stamp input}
    (trace : (Execution.system context header).Trace (initialState context) events after)
    (flight : after.phase = .flight stamp) :
    ∃ event, events[stamp.sendIndex]? = some event ∧ event.effect = .sent stamp ∧ stamp.sendIndex < events.length := by
  have origins := trace_origins (history := []) trace rfl
    (by intro stamp impossible; cases impossible) (by intro index impossible; cases impossible)
  simpa using origins.1 stamp flight

theorem trace_delivery_origin {after : State input} {events : List (Event input)} {index : Nat}
    (trace : (Execution.system context header).Trace (initialState context) events after)
    (delivered : after.phase = .delivered index) :
    ∃ event observation current,
      events[index]? = some event ∧ event.effect = .received observation current index ∧ index < events.length := by
  have origins := trace_origins (history := []) trace rfl
    (by intro stamp impossible; cases impossible) (by intro index impossible; cases impossible)
  simpa using origins.2 index delivered

theorem trace_arrival_origin {before after : State input} {events : List (Event input)} {event : Event input}
    (trace : (Execution.system context header).Trace (initialState context) events before)
    (step : (Execution.system context header).step before event after)
    (action : event.action = .arrive observation index) :
    ∃ stamp sent, before.phase = .flight stamp ∧ event.effect = .arrived stamp ∧
      index = stamp.sendIndex ∧ events[index]? = some sent ∧ sent.effect = .sent stamp ∧ index < events.length := by
  obtain ⟨stamp, flight, arrived, _, _, _, indexEq, _⟩ := step_arrive step action
  obtain ⟨sent, found, same, within⟩ := trace_flight_origin trace flight
  exact ⟨stamp, sent, flight, arrived, indexEq, indexEq ▸ found, same, indexEq ▸ within⟩

theorem arrival_origin_whole {before after : State input} {history suffix : List (Event input)} {event : Event input}
    (trace : (Execution.system context header).Trace (initialState context) history before)
    (step : (Execution.system context header).step before event after)
    (action : event.action = .arrive observation index) :
    ∃ stamp sent, before.phase = .flight stamp ∧ event.effect = .arrived stamp ∧ index = stamp.sendIndex ∧
      (history ++ event :: suffix)[index]? = some sent ∧ sent.effect = .sent stamp ∧ index < history.length := by
  obtain ⟨stamp, sent, flight, arrived, indexEq, found, same, within⟩ := trace_arrival_origin trace step action
  refine ⟨stamp, sent, flight, arrived, indexEq, ?_, same, within⟩
  rw [List.getElem?_append_left within]
  exact found

end Netlib.Federation.InFlight.History
