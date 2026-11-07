import Netlib.Check.FederatedCohortControl
import Netlib.Check.FederatedPacketExecution

/-!
# Literal cohort actions and component executions

Each shared slot advances every packet clock. Unselected packets take the
literal idle action, and every component result is checked by its executor.
-/

namespace Netlib.Federation.Cohort

variable {input : Input} {size : Nat}

def Outcome.packet (outcome : Outcome input size) (index : Fin size) : InFlight.Outcome input :=
  ⟨outcome.after.packet index, outcome.effects.get index⟩

namespace Execution

def candidate (context : Context input size) (headers : Vector Packet.Header size)
    (before : State input size) (action : InFlight.Action) (next : Key input size) : Outcome input size :=
  let parts := Vector.ofFn fun index => InFlight.Execution.candidate
    (context.packets.get index) (headers.get index) (before.packet index)
    (projectAction context action index) next.current
  ⟨⟨next.current, parts.map (fun part => part.after.phase), next.queues, before.nextIndex + 1⟩,
    parts.map (fun part => part.effect)⟩

@[simp] theorem candidate_tick (context : Context input size) (headers : Vector Packet.Header size)
    (before : State input size) (action : InFlight.Action) (next : Key input size) :
    (candidate context headers before action next).after.nextIndex = before.nextIndex + 1 := rfl

@[simp] theorem candidate_current (context : Context input size) (headers : Vector Packet.Header size)
    (before : State input size) (action : InFlight.Action) (next : Key input size) :
    (candidate context headers before action next).after.current = next.current := rfl

@[simp] theorem candidate_packet (context : Context input size) (headers : Vector Packet.Header size)
    (before : State input size) (action : InFlight.Action) (next : Key input size) (index : Fin size) :
    (candidate context headers before action next).packet index =
      InFlight.Execution.candidate (context.packets.get index) (headers.get index) (before.packet index)
        (projectAction context action index) next.current := by
  simp [candidate, Outcome.packet, State.packet, Vector.get, Fin.cast, InFlight.Execution.candidate]

def localAdvances (context : Context input size) (headers : Vector Packet.Header size)
    (before : State input size) (action : InFlight.Action) (outcome : Outcome input size) : Bool :=
  (List.finRange size).all fun index => match InFlight.Execution.rawAdvance
    (context.packets.get index) (headers.get index) (before.packet index)
    (projectAction context action index) with
    | .error _ => false
    | .ok actual => decide (actual = outcome.packet index)

theorem localAdvances_iff (context : Context input size) (headers : Vector Packet.Header size)
    (before : State input size) (action : InFlight.Action) (outcome : Outcome input size) :
    localAdvances context headers before action outcome = true ↔ ∀ index,
      InFlight.Execution.rawAdvance (context.packets.get index) (headers.get index) (before.packet index)
        (projectAction context action index) = .ok (outcome.packet index) := by
  simp only [localAdvances, List.all_eq_true, List.mem_finRange, forall_const]
  apply forall_congr'
  intro index
  cases InFlight.Execution.rawAdvance (context.packets.get index) (headers.get index)
    (before.packet index) (projectAction context action index) <;> simp

def KeyTransition (context : Context input size) (headers : Vector Packet.Header size)
    (before : Key input size) (action : InFlight.Action) (after : Key input size) : Prop :=
  ∃ move, actionMove context action = .ok move ∧ match move with
    | none => after = before
    | some selected => Control.step context headers before selected = some after

def KeyStep (context : Context input size) (headers : Vector Packet.Header size)
    (before : State input size) (action : InFlight.Action) (after : State input size) : Prop :=
  KeyTransition context headers before.key action after.key

structure Selected (context : Context input size) (headers : Vector Packet.Header size)
    (before : State input size) (action : InFlight.Action) where
  key : Key input size
  beforeGood : Control.good context before.key = true
  afterGood : Control.good context key = true
  keyStep : KeyTransition context headers before.key action key

def select (context : Context input size) (headers : Vector Packet.Header size)
    (before : State input size) (action : InFlight.Action) : Except String (Selected context headers before action) :=
  if good : Control.good context before.key = true then
    match classified : actionMove context action with
    | .error reason => .error reason
    | .ok none => .ok ⟨before.key, good, good, ⟨none, classified, rfl⟩⟩
    | .ok (some move) =>
      match selected : Control.step context headers before.key move with
      | none => .error "The cohort move is not currently enabled."
      | some key => .ok ⟨key, good, (Control.step_facts context headers before.key key move selected).afterGood,
          ⟨some move, classified, selected⟩⟩
  else .error "The cohort queues, reservations, or occupied nodes are invalid."

def rawAdvance (context : Context input size) (headers : Vector Packet.Header size)
    (before : State input size) (action : InFlight.Action) : Except String (Outcome input size) :=
  match select context headers before action with
  | .error reason => .error reason
  | .ok selected =>
    let outcome := candidate context headers before action selected.key
    if outcome.after.key = selected.key ∧ localAdvances context headers before action outcome = true then .ok outcome
    else .error "The concrete cohort action differs from its component executions."

structure Facts (context : Context input size) (headers : Vector Packet.Header size)
    (before : State input size) (action : InFlight.Action) (outcome : Outcome input size) : Prop where
  tick : outcome.after.nextIndex = before.nextIndex + 1
  beforeGood : Control.good context before.key = true
  afterGood : Control.good context outcome.after.key = true
  keyStep : KeyStep context headers before action outcome.after
  locals : ∀ index, InFlight.Execution.rawAdvance (context.packets.get index) (headers.get index)
    (before.packet index) (projectAction context action index) = .ok (outcome.packet index)
  candidateEq : candidate context headers before action outcome.after.key = outcome

theorem rawAdvance_facts (context : Context input size) (headers : Vector Packet.Header size)
    (before : State input size) (action : InFlight.Action) (outcome : Outcome input size)
    (success : rawAdvance context headers before action = .ok outcome) :
    Facts context headers before action outcome := by
  unfold rawAdvance at success
  cases chosen : select context headers before action with
  | error reason => simp only [chosen] at success; cases success
  | ok selected =>
    simp only [chosen] at success
    split at success
    · rename_i matched
      cases success
      refine ⟨rfl, selected.beforeGood, ?_, ?_, ?_, ?_⟩
      · rw [matched.1]; exact selected.afterGood
      · unfold KeyStep
        rw [matched.1]
        exact selected.keyStep
      · exact (localAdvances_iff _ _ _ _ _).mp matched.2
      · simp only [candidate, State.key]
    · cases success

structure Advanced (context : Context input size) (headers : Vector Packet.Header size)
    (before : State input size) (action : InFlight.Action) where
  outcome : Outcome input size
  success : rawAdvance context headers before action = .ok outcome
  facts : Facts context headers before action outcome

def advance (context : Context input size) (headers : Vector Packet.Header size)
    (before : State input size) (action : InFlight.Action) : Except String (Advanced context headers before action) :=
  match success : rawAdvance context headers before action with
  | .error reason => .error reason
  | .ok outcome => .ok ⟨outcome, success, rawAdvance_facts context headers before action outcome success⟩

theorem advance_of_raw (context : Context input size) (headers : Vector Packet.Header size)
    (before : State input size) (action : InFlight.Action) (outcome : Outcome input size)
    (success : rawAdvance context headers before action = .ok outcome) :
    ∃ value, advance context headers before action = .ok value ∧ value.outcome = outcome := by
  unfold advance
  split
  · rename_i reason failed
    rw [failed] at success
    cases success
  · rename_i actual selected
    have same : actual = outcome := Except.ok.inj (selected.symm.trans success)
    subst actual
    exact ⟨_, rfl, rfl⟩

def Advanced.event {context : Context input size} {headers : Vector Packet.Header size}
    {before : State input size} {action : InFlight.Action} (value : Advanced context headers before action) : Event input size :=
  ⟨action, value.outcome.effects⟩

def system (context : Context input size) (headers : Vector Packet.Header size) :
    Protocol.Transition (State input size) (Event input size) where
  step before event after := ∃ outcome, rawAdvance context headers before event.action = .ok outcome ∧
    outcome.after = after ∧ outcome.effects = event.effects

theorem Advanced.step {context : Context input size} {headers : Vector Packet.Header size}
    {before : State input size} {action : InFlight.Action} (value : Advanced context headers before action) :
    (system context headers).step before value.event value.outcome.after :=
  ⟨value.outcome, value.success, rfl, rfl⟩

theorem step_facts (context : Context input size) (headers : Vector Packet.Header size)
    {before after : State input size} {event : Event input size}
    (step : (system context headers).step before event after) :
    ∃ outcome, Facts context headers before event.action outcome ∧ outcome.after = after ∧ outcome.effects = event.effects := by
  obtain ⟨outcome, success, stateEq, effectEq⟩ := step
  exact ⟨outcome, rawAdvance_facts context headers before event.action outcome success, stateEq, effectEq⟩

theorem step_tick (context : Context input size) (headers : Vector Packet.Header size)
    {before after : State input size} {event : Event input size}
    (step : (system context headers).step before event after) : after.nextIndex = before.nextIndex + 1 := by
  obtain ⟨outcome, facts, rfl, _⟩ := step_facts context headers step
  exact facts.tick

theorem project_step (context : Context input size) (headers : Vector Packet.Header size)
    {before after : State input size} {event : Event input size}
    (step : (system context headers).step before event after) (index : Fin size) :
    (InFlight.Execution.system (context.packets.get index) (headers.get index)).step
      (before.packet index) (event.packet context index) (after.packet index) := by
  obtain ⟨outcome, facts, rfl, effects⟩ := step_facts context headers step
  refine ⟨outcome.packet index, facts.locals index, rfl, ?_⟩
  exact congrArg (fun values => values.get index) effects

def packetRefinement (context : Context input size) (headers : Vector Packet.Header size) (index : Fin size) :
    Protocol.TraceRefinement (system context headers)
      (InFlight.Execution.system (context.packets.get index) (headers.get index)) where
  project state := state.packet index
  labels event := [event.packet context index]
  simulate _ _ after step := .cons (project_step context headers step index) (.nil (after.packet index))

theorem project_trace (context : Context input size) (headers : Vector Packet.Header size)
    {before after : State input size} {events : List (Event input size)}
    (trace : (system context headers).Trace before events after) (index : Fin size) :
    (InFlight.Execution.system (context.packets.get index) (headers.get index)).Trace
      (before.packet index) (events.map (fun event => event.packet context index)) (after.packet index) := by
  induction trace with
  | nil => exact .nil _
  | cons edge _ ih => exact .cons (project_step context headers edge index) ih

theorem trace_tick (context : Context input size) (headers : Vector Packet.Header size)
    {before after : State input size} {events : List (Event input size)}
    (trace : (system context headers).Trace before events after) :
    after.nextIndex = before.nextIndex + events.length := by
  induction trace with
  | nil => simp
  | cons edge _ ih =>
    rw [ih, step_tick context headers edge]
    simp [Nat.add_assoc, Nat.add_comm]

end Execution
end Netlib.Federation.Cohort
