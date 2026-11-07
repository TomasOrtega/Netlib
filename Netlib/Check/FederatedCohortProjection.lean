import Netlib.Check.FederatedCohortExecution
import Netlib.Check.FederatedPacketInvariant

/-!
# Exact packet identities and complete concrete cohort fibers
-/

namespace Netlib.Federation.Cohort

variable {input : Input} {size : Nat}

theorem Context.Unique.packetID_injective {context : Context input size} (unique : context.Unique)
    (first second : Fin size)
    (same : (context.packets.get first).profile.packetID = (context.packets.get second).profile.packetID) :
    first = second := by
  change context.packets[first.val].profile.packetID = context.packets[second.val].profile.packetID at same
  apply Fin.ext
  apply unique.eq_of_getElem_eq
    (by simpa only [List.length_map, Vector.length_toList] using first.isLt)
    (by simpa only [List.length_map, Vector.length_toList] using second.isLt)
  simpa only [List.getElem_map, Vector.getElem_toList] using same

theorem packetIndex_self {context : Context input size} (unique : context.Unique) (index : Fin size) :
    packetIndex context (context.packets.get index).profile.packetID = some index := by
  cases found : packetIndex context (context.packets.get index).profile.packetID with
  | none =>
    have absent := List.find?_eq_none.mp found index (List.mem_finRange index)
    exact False.elim (absent (decide_eq_true rfl))
  | some selected =>
    have matched := of_decide_eq_true (List.find?_some
      (p := fun selected : Fin size => decide ((context.packets.get selected).profile.packetID =
        (context.packets.get index).profile.packetID)) found)
    have same := unique.packetID_injective selected index matched
    simp only [same]

theorem actionMove_canonical {context : Context input size} (unique : context.Unique)
    (headers : Vector Packet.Header size) (state : State input size) (move : Move size) :
    actionMove context (canonicalAction context headers state move) = .ok (some move) := by
  cases move with
  | packet index move =>
    cases move <;> cases phase : (state.packet index).phase <;>
      simp [canonicalAction, PacketMove.local, InFlight.canonicalAction, phase, actionMove,
        InFlight.Context.observation, packetIndex_self unique index]
  | updateLeft => rfl
  | updateRight => rfl
  | updateBoth => rfl

theorem project_canonical {context : Context input size} (unique : context.Unique)
    (headers : Vector Packet.Header size) (state : State input size) (move : Move size) (index : Fin size) :
    projectAction context (canonicalAction context headers state move) index =
      match move.local index with
      | none => .idle
      | some operation => InFlight.canonicalAction (context.packets.get index) (headers.get index) (state.packet index) operation := by
  unfold projectAction
  rw [actionMove_canonical unique]
  cases move with
  | packet selected action =>
    by_cases same : selected = index
    · subst selected; simp [Move.local, canonicalAction]
    · simp [same, Move.local]
  | updateLeft => rfl
  | updateRight => rfl
  | updateBoth => rfl

def State.Valid (state : State input size) (context : Context input size) (headers : Vector Packet.Header size) : Prop :=
  Control.good context state.key = true ∧ ∀ index,
    (state.packet index).Valid (context.packets.get index) (headers.get index)

namespace Execution

theorem step_valid (context : Context input size) (headers : Vector Packet.Header size)
    {before after : State input size} {event : Event input size} (valid : before.Valid context headers)
    (step : (system context headers).step before event after) : after.Valid context headers := by
  obtain ⟨outcome, facts, rfl, _⟩ := step_facts context headers step
  refine ⟨facts.afterGood, fun index => ?_⟩
  exact InFlight.Execution.step_valid _ _ (valid.2 index) (project_step context headers step index)

theorem invariant (context : Context input size) (headers : Vector Packet.Header size) :
    (system context headers).Invariant (fun state => state.Valid context headers) :=
  fun _ _ _ valid step => step_valid context headers valid step

theorem trace_valid (context : Context input size) (headers : Vector Packet.Header size)
    {before after : State input size} {events : List (Event input size)}
    (valid : before.Valid context headers) (trace : (system context headers).Trace before events after) :
    after.Valid context headers := (invariant context headers).trace valid trace

theorem initial_trace_index (context : Context input size) (headers : Vector Packet.Header size)
    {after : State input size} {events : List (Event input size)}
    (trace : (system context headers).Trace (initialState context) events after) : after.nextIndex = events.length := by
  simpa only [initialState, Nat.zero_add] using trace_tick context headers trace

theorem canonical_component (context : Context input size) (unique : context.Unique)
    (headers : Vector Packet.Header size) (before : State input size) (valid : before.Valid context headers)
    (move : Move size) (after : Key input size)
    (selected : Control.step context headers before.key move = some after) (index : Fin size) :
    let action := canonicalAction context headers before move
    let part := InFlight.Execution.candidate (context.packets.get index) (headers.get index)
      (before.packet index) (projectAction context action index) after.current
    part.after.key = after.packet index ∧
      InFlight.Execution.rawAdvance (context.packets.get index) (headers.get index) (before.packet index)
        (projectAction context action index) = .ok part := by
  dsimp only
  rw [project_canonical unique]
  have localStep := (Control.step_facts context headers before.key after move selected).localSteps index
  cases localEq : move.local index with
  | none =>
    simp only [localEq] at localStep ⊢
    have same : after.current = before.current := congrArg InFlight.Key.current localStep
    refine ⟨?_, ?_⟩
    · rw [InFlight.Execution.candidate_idle, same]
      simpa [State.key, Key.packet, State.packet, InFlight.State.key, Vector.get, Fin.cast] using localStep.symm
    · simp [InFlight.Execution.rawAdvance, InFlight.Execution.observationsMatch, InFlight.Action.move?,
        InFlight.Execution.candidate_idle, InFlight.State.key, State.packet, same]
  | some operation =>
    simp only [localEq] at localStep ⊢
    rw [← State.packet_key] at localStep
    exact ⟨InFlight.Execution.canonical_key _ _ _ _ _ localStep,
      InFlight.Execution.canonical_raw _ _ _ (valid.2 index) _ _ localStep⟩

theorem canonical_key (context : Context input size) (unique : context.Unique)
    (headers : Vector Packet.Header size) (before : State input size) (valid : before.Valid context headers)
    (move : Move size) (after : Key input size)
    (selected : Control.step context headers before.key move = some after) :
    (candidate context headers before (canonicalAction context headers before move) after).after.key = after := by
  have phases : (candidate context headers before (canonicalAction context headers before move) after).after.key.phases =
      after.phases := by
    apply Vector.ext
    intro position within
    have same := (canonical_component context unique headers before valid move after selected ⟨position, within⟩).1
    have phase := congrArg InFlight.Key.phase same
    simpa [candidate, State.key, Key.packet, InFlight.Execution.candidate, InFlight.State.key,
      Vector.get, Fin.cast] using phase
  cases after
  exact congrArg (fun values => Key.mk _ values _) phases

theorem select_of_selected (context : Context input size) (headers : Vector Packet.Header size)
    (before : State input size) (good : Control.good context before.key = true)
    (action : InFlight.Action) (move : Move size) (after : Key input size)
    (classified : actionMove context action = .ok (some move))
    (selected : Control.step context headers before.key move = some after) :
    ∃ value, select context headers before action = .ok value ∧ value.key = after := by
  unfold select
  split
  · split
    · rename_i reason failed
      rw [classified] at failed
      cases failed
    · rename_i failed
      rw [classified] at failed
      cases failed
    · rename_i actual same
      have equal : actual = move := Option.some.inj (Except.ok.inj (same.symm.trans classified))
      subst actual
      split
      · rename_i failed
        rw [selected] at failed
        cases failed
      · rename_i key chosen
        have equal : key = after := Option.some.inj (chosen.symm.trans selected)
        subst key
        exact ⟨_, rfl, rfl⟩
  · contradiction

theorem canonical_raw (context : Context input size) (unique : context.Unique)
    (headers : Vector Packet.Header size) (before : State input size) (valid : before.Valid context headers)
    (move : Move size) (after : Key input size)
    (selected : Control.step context headers before.key move = some after) :
    rawAdvance context headers before (canonicalAction context headers before move) =
      .ok (candidate context headers before (canonicalAction context headers before move) after) := by
  have matched := canonical_key context unique headers before valid move after selected
  have locals : localAdvances context headers before (canonicalAction context headers before move)
      (candidate context headers before (canonicalAction context headers before move) after) = true := by
    apply (localAdvances_iff _ _ _ _ _).mpr
    intro index
    rw [candidate_packet]
    exact (canonical_component context unique headers before valid move after selected index).2
  have classified := actionMove_canonical unique headers before move
  obtain ⟨value, success, same⟩ := select_of_selected context headers before valid.1 _ move after classified selected
  unfold rawAdvance
  rw [success]
  simp only [same, matched, locals, and_self, ↓reduceIte]

theorem canonical_lift (context : Context input size) (unique : context.Unique)
    (headers : Vector Packet.Header size) (before : State input size) (valid : before.Valid context headers)
    (move : Move size) (after : Key input size)
    (selected : Control.step context headers before.key move = some after) :
    ∃ value : Advanced context headers before (canonicalAction context headers before move),
      advance context headers before (canonicalAction context headers before move) = .ok value ∧
        value.outcome.after.key = after := by
  obtain ⟨value, succeeded, same⟩ := advance_of_raw context headers before _ _
    (canonical_raw context unique headers before valid move after selected)
  exact ⟨value, succeeded, by rw [same]; exact canonical_key context unique headers before valid move after selected⟩

theorem idle_raw (context : Context input size) (headers : Vector Packet.Header size)
    (before : State input size) (good : Control.good context before.key = true) :
    rawAdvance context headers before .idle = .ok (candidate context headers before .idle before.key) := by
  have matched : (candidate context headers before .idle before.key).after.key = before.key := by
    have phases : (candidate context headers before .idle before.key).after.key.phases = before.key.phases := by
      apply Vector.ext
      intro position within
      simp [candidate, projectAction, actionMove, InFlight.Execution.candidate_idle, State.key, State.packet,
        Vector.get, Fin.cast]
    cases before
    exact congrArg (fun values => Key.mk _ values _) phases
  have locals : localAdvances context headers before .idle (candidate context headers before .idle before.key) = true := by
    apply (localAdvances_iff _ _ _ _ _).mpr
    intro index
    rw [candidate_packet]
    simp [projectAction, actionMove, InFlight.Execution.rawAdvance, InFlight.Execution.observationsMatch,
      InFlight.Action.move?, InFlight.Execution.candidate_idle, State.packet, State.key, InFlight.State.key]
  unfold rawAdvance select
  simp only [good, ↓reduceDIte, actionMove, matched, locals, and_self, ↓reduceIte]

end Execution
end Netlib.Federation.Cohort
