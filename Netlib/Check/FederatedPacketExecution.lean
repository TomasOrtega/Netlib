import Netlib.Model.FederatedPacketExecution
import Netlib.Check.FederatedPacketControl

/-!
# Actual packet actions and source-stamped effects

Observations must match the current packet. Only a successful send constructs
a flight stamp; arrival consumes that exact stamp without a new policy check.
-/

namespace Netlib.Federation.InFlight.Execution

variable {input : Input}

def observationsMatch (context : Context input) (header : Packet.Header) (before : State input) : Action → Bool
  | .idle => true
  | .send observation _ => match before.phase with
    | .held source => decide (observation = context.observation header source)
    | _ => false
  | .arrive observation sendIndex => match before.phase with
    | .flight stamp => decide (observation = context.observation header stamp.target ∧
        stamp.packetID = context.profile.packetID ∧ stamp.header = header ∧ sendIndex = stamp.sendIndex)
    | _ => false
  | .receive observation => match before.phase with
    | .held node => decide (observation = context.observation header node)
    | _ => false
  | .updateLeft _ | .updateRight _ | .updateBoth _ _ => true

private def phaseEffect (context : Context input) (header : Packet.Header) (before : State input)
    (action : Action) (current : Cursors input) : Phase input × Effect input :=
  match action, before.phase with
  | .send _ target, .held source =>
    let stamp : Stamp input := ⟨before.current, source, target, context.profile.packetID, header, before.nextIndex⟩
    (.flight stamp, .sent stamp)
  | .arrive _ _, .flight stamp => (.held stamp.target, .arrived stamp)
  | .receive observation, .held _ =>
    (.delivered before.nextIndex, .received observation before.current before.nextIndex)
  | .updateLeft index, _ => (before.phase, .updated (.updateLeft index) before.current current)
  | .updateRight index, _ => (before.phase, .updated (.updateRight index) before.current current)
  | .updateBoth first second, _ => (before.phase, .updated (.updateBoth first second) before.current current)
  | _, _ => (before.phase, .idle)

def candidate (context : Context input) (header : Packet.Header) (before : State input)
    (action : Action) (current : Cursors input) : Outcome input :=
  let parts := phaseEffect context header before action current
  ⟨⟨current, parts.1, before.nextIndex + 1⟩, parts.2⟩

@[simp] theorem candidate_tick (context : Context input) (header : Packet.Header) (before : State input)
    (action : Action) (current : Cursors input) :
    (candidate context header before action current).after.nextIndex = before.nextIndex + 1 := rfl

@[simp] theorem candidate_current (context : Context input) (header : Packet.Header) (before : State input)
    (action : Action) (current : Cursors input) :
    (candidate context header before action current).after.current = current := rfl

theorem candidate_idle (context : Context input) (header : Packet.Header) (before : State input)
    (current : Cursors input) : candidate context header before .idle current =
    ⟨⟨current, before.phase, before.nextIndex + 1⟩, .idle⟩ := rfl

theorem candidate_send (context : Context input) (header : Packet.Header) (before : State input)
    (observation : Observation) (source target : Node) (current : Cursors input) (held : before.phase = .held source) :
    candidate context header before (.send observation target) current =
      let stamp : Stamp input := ⟨before.current, source, target, context.profile.packetID, header, before.nextIndex⟩
      ⟨⟨current, .flight stamp, before.nextIndex + 1⟩, .sent stamp⟩ := by
  simp only [candidate, phaseEffect, held]

theorem candidate_arrive (context : Context input) (header : Packet.Header) (before : State input)
    (observation : Observation) (index : Nat) (stamp : Stamp input) (current : Cursors input)
    (flight : before.phase = .flight stamp) :
    candidate context header before (.arrive observation index) current =
      ⟨⟨current, .held stamp.target, before.nextIndex + 1⟩, .arrived stamp⟩ := by
  simp only [candidate, phaseEffect, flight]

theorem candidate_receive (context : Context input) (header : Packet.Header) (before : State input)
    (observation : Observation) (node : Node) (current : Cursors input) (held : before.phase = .held node) :
    candidate context header before (.receive observation) current =
      ⟨⟨current, .delivered before.nextIndex, before.nextIndex + 1⟩,
        .received observation before.current before.nextIndex⟩ := by
  simp only [candidate, phaseEffect, held]

theorem candidate_updateLeft (context : Context input) (header : Packet.Header) (before : State input)
    (index : Nat) (current : Cursors input) : candidate context header before (.updateLeft index) current =
      ⟨⟨current, before.phase, before.nextIndex + 1⟩, .updated (.updateLeft index) before.current current⟩ := rfl

theorem candidate_updateRight (context : Context input) (header : Packet.Header) (before : State input)
    (index : Nat) (current : Cursors input) : candidate context header before (.updateRight index) current =
      ⟨⟨current, before.phase, before.nextIndex + 1⟩, .updated (.updateRight index) before.current current⟩ := rfl

theorem candidate_updateBoth (context : Context input) (header : Packet.Header) (before : State input)
    (first second : Nat) (current : Cursors input) : candidate context header before (.updateBoth first second) current =
      ⟨⟨current, before.phase, before.nextIndex + 1⟩, .updated (.updateBoth first second) before.current current⟩ := rfl

def KeyStep (context : Context input) (header : Packet.Header) (before : State input)
    (action : Action) (after : State input) : Prop :=
  match action.move? with
  | none => after.key = before.key
  | some move => Control.step context header before.key move = some after.key

def rawAdvance (context : Context input) (header : Packet.Header) (before : State input)
    (action : Action) : Except String (Outcome input) :=
  if observationsMatch context header before action then
    match action.move? with
    | none =>
      let outcome := candidate context header before action before.current
      if outcome.after.key = before.key then .ok outcome
      else .error "The idle packet action changes its control key."
    | some move =>
      match Control.step context header before.key move with
      | none => .error "The packet move is not currently enabled."
      | some next =>
        let outcome := candidate context header before action next.current
        if outcome.after.key = next then .ok outcome
        else .error "The concrete packet phase differs from its control successor."
  else .error "The packet observation or phase does not match the current packet."

structure Facts (context : Context input) (header : Packet.Header) (before : State input)
    (action : Action) (outcome : Outcome input) : Prop where
  observations : observationsMatch context header before action = true
  tick : outcome.after.nextIndex = before.nextIndex + 1
  keyStep : KeyStep context header before action outcome.after
  candidateEq : candidate context header before action outcome.after.current = outcome

theorem rawAdvance_facts (context : Context input) (header : Packet.Header) (before : State input)
    (action : Action) (outcome : Outcome input) (success : rawAdvance context header before action = .ok outcome) :
    Facts context header before action outcome := by
  unfold rawAdvance at success
  split at success
  · rename_i observed
    cases move : action.move? with
    | none =>
      simp only [move] at success
      split at success
      · rename_i matched
        cases success
        exact ⟨observed, rfl, by simpa only [KeyStep, move] using matched, rfl⟩
      · cases success
    | some selected =>
      simp only [move] at success
      cases next : Control.step context header before.key selected with
      | none => simp only [next] at success; cases success
      | some key =>
        simp only [next] at success
        split at success
        · rename_i matched
          cases success
          refine ⟨observed, rfl, ?_, rfl⟩
          simp only [KeyStep, move]
          rw [matched]
          exact next
        · cases success
  · cases success

structure Advanced (context : Context input) (header : Packet.Header) (before : State input) (action : Action) where
  outcome : Outcome input
  success : rawAdvance context header before action = .ok outcome
  observations : observationsMatch context header before action = true
  tick : outcome.after.nextIndex = before.nextIndex + 1
  keyStep : KeyStep context header before action outcome.after
  candidateEq : candidate context header before action outcome.after.current = outcome

def advance (context : Context input) (header : Packet.Header) (before : State input)
    (action : Action) : Except String (Advanced context header before action) :=
  match success : rawAdvance context header before action with
  | .error reason => .error reason
  | .ok outcome =>
    let facts := rawAdvance_facts context header before action outcome success
    .ok ⟨outcome, success, facts.observations, facts.tick, facts.keyStep, facts.candidateEq⟩

theorem advance_of_raw (context : Context input) (header : Packet.Header) (before : State input)
    (action : Action) (outcome : Outcome input) (success : rawAdvance context header before action = .ok outcome) :
    ∃ value, advance context header before action = .ok value ∧ value.outcome = outcome := by
  unfold advance
  split
  · rename_i reason failed
    rw [failed] at success
    cases success
  · rename_i actual selected
    have same : actual = outcome := Except.ok.inj (selected.symm.trans success)
    subst actual
    exact ⟨_, rfl, rfl⟩

def Advanced.event {context : Context input} {header : Packet.Header} {before : State input} {action : Action}
    (value : Advanced context header before action) : Event input := ⟨action, value.outcome.effect⟩

def system (context : Context input) (header : Packet.Header) : Protocol.Transition (State input) (Event input) where
  step before event after := ∃ outcome, rawAdvance context header before event.action = .ok outcome ∧
    outcome.after = after ∧ outcome.effect = event.effect

theorem Advanced.step {context : Context input} {header : Packet.Header} {before : State input} {action : Action}
    (value : Advanced context header before action) :
    (system context header).step before value.event value.outcome.after :=
  ⟨value.outcome, value.success, rfl, rfl⟩

theorem step_facts (context : Context input) (header : Packet.Header)
    {before after : State input} {event : Event input} (step : (system context header).step before event after) :
    ∃ outcome, Facts context header before event.action outcome ∧ outcome.after = after ∧ outcome.effect = event.effect := by
  obtain ⟨outcome, success, stateEq, effectEq⟩ := step
  exact ⟨outcome, rawAdvance_facts context header before event.action outcome success, stateEq, effectEq⟩

theorem step_tick (context : Context input) (header : Packet.Header)
    {before after : State input} {event : Event input} (step : (system context header).step before event after) :
    after.nextIndex = before.nextIndex + 1 := by
  obtain ⟨outcome, facts, rfl, _⟩ := step_facts context header step
  exact facts.tick

theorem step_key (context : Context input) (header : Packet.Header)
    {before after : State input} {event : Event input} (step : (system context header).step before event after) :
    KeyStep context header before event.action after := by
  obtain ⟨outcome, facts, rfl, _⟩ := step_facts context header step
  exact facts.keyStep

end Netlib.Federation.InFlight.Execution
