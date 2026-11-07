import Netlib.Check.FederatedPacketExecution
import Netlib.Check.FederatedPacketContext

/-!
# Packet invariants and complete concrete fibers

An in-flight stamp keeps its old native decision and source index. Current
updates preserve the pending receiver and its original public projection.
-/

namespace Netlib.Federation.InFlight

variable {input : Input}

structure Stamp.Valid (stamp : Stamp input) (context : Context input) (header : Packet.Header)
    (current : Cursors input) (nextIndex : Nat) : Prop where
  packetID : stamp.packetID = context.profile.packetID
  headerEq : stamp.header = header
  native : Control.nativeEdge context header stamp.current stamp.source stamp.target = true
  sourceKnown : Control.known input stamp.current stamp.source = true
  targetKnown : Control.known input stamp.current stamp.target = true
  past : stamp.sendIndex < nextIndex
  receiverKnown : Control.known input current stamp.target = true
  projection : Control.project input current stamp.target = Control.project input stamp.current stamp.target

def State.Valid (state : State input) (context : Context input) (header : Packet.Header) : Prop :=
  match state.phase with
  | .held node => Control.known input state.current node = true
  | .flight stamp => stamp.Valid context header state.current state.nextIndex
  | .delivered index => index < state.nextIndex

theorem State.Valid.key {state : State input} {context : Context input} {header : Packet.Header}
    (valid : state.Valid context header) : Control.Valid state.key := by
  intro node location
  change Control.known input state.current node = true
  cases phase : state.phase with
  | held source =>
    simp only [State.key, phase, Phase.key, Control.occupied] at location
    have same : source = node := Option.some.inj location
    simpa only [State.Valid, phase, same] using valid
  | flight stamp =>
    simp only [State.key, phase, Phase.key, Control.occupied] at location
    have same : stamp.target = node := Option.some.inj location
    have flight : stamp.Valid context header state.current state.nextIndex := by simpa only [State.Valid, phase] using valid
    simpa only [same] using flight.receiverKnown
  | delivered index => simp [State.key, phase, Phase.key, Control.occupied] at location

theorem initial_valid {deployment : Deployment.Checked input} {context : Context input}
    (checked : Context.Validated deployment context) (header : Packet.Header) :
    (initialState context).Valid context header := by
  have present := checked.sourceNode_known (Plan.jointInitial input.left input.right)
  cases node : context.sourceNode with
  | inl source =>
    have member : source ∈ (input.left.revisionAt input.left.initialCursor).snapshot.intent.ids := by
      simpa only [node, Composition.Known, Plan.jointInitial] using present
    simpa only [initialState, State.Valid, Control.known, node, Plan.jointInitial] using decide_eq_true member
  | inr source =>
    have member : source ∈ (input.right.revisionAt input.right.initialCursor).snapshot.intent.ids := by
      simpa only [node, Composition.Known, Plan.jointInitial] using present
    simpa only [initialState, State.Valid, Control.known, node, Plan.jointInitial] using decide_eq_true member

theorem State.Valid.tick {state : State input} {context : Context input} {header : Packet.Header}
    (valid : state.Valid context header) :
    (⟨state.current, state.phase, state.nextIndex + 1⟩ : State input).Valid context header := by
  cases phase : state.phase with
  | held node => simpa only [State.Valid, phase] using valid
  | flight stamp =>
    have flight : stamp.Valid context header state.current state.nextIndex := by simpa only [State.Valid, phase] using valid
    exact ⟨flight.packetID, flight.headerEq, flight.native, flight.sourceKnown, flight.targetKnown,
      by change stamp.sendIndex < state.nextIndex + 1; have := flight.past; omega,
      flight.receiverKnown, flight.projection⟩
  | delivered index =>
    have earlier : index < state.nextIndex := by simpa only [State.Valid, phase] using valid
    change index < state.nextIndex + 1
    omega

theorem State.Valid.relocate {state : State input} {context : Context input} {header : Packet.Header}
    (valid : state.Valid context header) (current : Cursors input)
    (coherent : Control.coherent input state.current current state.phase.key = true) :
    (⟨current, state.phase, state.nextIndex + 1⟩ : State input).Valid context header := by
  cases phase : state.phase with
  | held node =>
    have checked := Control.coherent_spec state.current current (.held node) node rfl
      (by simpa only [phase, Phase.key] using coherent)
    exact checked.2.1
  | flight stamp =>
    have flight : stamp.Valid context header state.current state.nextIndex := by simpa only [State.Valid, phase] using valid
    have checked := Control.coherent_spec state.current current (.flight stamp.target) stamp.target rfl
      (by simpa only [phase, Phase.key] using coherent)
    exact ⟨flight.packetID, flight.headerEq, flight.native, flight.sourceKnown, flight.targetKnown,
      by change stamp.sendIndex < state.nextIndex + 1; have := flight.past; omega,
      checked.2.1, checked.2.2.symm.trans flight.projection⟩
  | delivered index =>
    have earlier : index < state.nextIndex := by simpa only [State.Valid, phase] using valid
    change index < state.nextIndex + 1
    omega
namespace Execution

def nextPhase : KeyPhase → Move → Option KeyPhase
  | .held _, .send target => some (.flight target)
  | .flight receiver, .arrive => some (.held receiver)
  | .held _, .receive => some .delivered
  | phase, .updateLeft _ | phase, .updateRight _ | phase, .updateBoth _ _ => some phase
  | _, _ => none

def updating : Move → Bool
  | .updateLeft _ | .updateRight _ | .updateBoth _ _ => true
  | _ => false

theorem control_frame (context : Context input) (header : Packet.Header) (before after : Key input) (move : Move)
    (selected : Control.step context header before move = some after) :
    nextPhase before.phase move = some after.phase ∧
      (updating move = false → after.current = before.current) ∧
      (updating move = true → Control.coherent input before.current after.current before.phase = true) := by
  cases move with
  | send target =>
    cases phase : before.phase with
    | held source =>
      simp only [Control.step, phase] at selected
      split at selected
      · cases selected
        simp [nextPhase, updating]
      · cases selected
    | flight receiver => simp [Control.step, phase] at selected
    | delivered => simp [Control.step, phase] at selected
  | arrive =>
    cases phase : before.phase with
    | held source => simp [Control.step, phase] at selected
    | flight receiver =>
      simp only [Control.step, phase] at selected
      split at selected
      · cases selected
        simp [nextPhase, updating]
      · cases selected
    | delivered => simp [Control.step, phase] at selected
  | receive =>
    cases phase : before.phase with
    | held source =>
      simp only [Control.step, phase] at selected
      split at selected
      · cases selected
        simp [nextPhase, updating]
      · cases selected
    | flight receiver => simp [Control.step, phase] at selected
    | delivered => simp [Control.step, phase] at selected
  | updateLeft index =>
    cases next : Control.nextCursor input.left before.current.1 index with
    | none => simp [Control.step, next] at selected
    | some cursor =>
      simp only [Control.step, next] at selected
      change (if Control.coherent input before.current (cursor, before.current.2) before.phase &&
        Control.fenceClear context.profile.leftFences index .left before.phase then
        some ⟨(cursor, before.current.2), before.phase⟩ else none) = some after at selected
      split at selected
      · rename_i checks
        cases selected
        have coherent := ((Bool.and_eq_true _ _).mp checks).1
        simpa [nextPhase, updating] using coherent
      · cases selected
  | updateRight index =>
    cases next : Control.nextCursor input.right before.current.2 index with
    | none => simp [Control.step, next] at selected
    | some cursor =>
      simp only [Control.step, next] at selected
      change (if Control.coherent input before.current (before.current.1, cursor) before.phase &&
        Control.fenceClear context.profile.rightFences index .right before.phase then
        some ⟨(before.current.1, cursor), before.phase⟩ else none) = some after at selected
      split at selected
      · rename_i checks
        cases selected
        have coherent := ((Bool.and_eq_true _ _).mp checks).1
        simpa [nextPhase, updating] using coherent
      · cases selected
  | updateBoth left right =>
    cases first : Control.nextCursor input.left before.current.1 left with
    | none => simp [Control.step, first] at selected
    | some nextLeft =>
      cases second : Control.nextCursor input.right before.current.2 right with
      | none => simp [Control.step, first, second] at selected
      | some nextRight =>
        simp only [Control.step, first, second] at selected
        change (if Control.coherent input before.current (nextLeft, nextRight) before.phase &&
          Control.fenceClear context.profile.leftFences left .left before.phase &&
          Control.fenceClear context.profile.rightFences right .right before.phase then
          some ⟨(nextLeft, nextRight), before.phase⟩ else none) = some after at selected
        split at selected
        · rename_i checks
          cases selected
          have coherent := ((Bool.and_eq_true _ _).mp (((Bool.and_eq_true _ _).mp checks).1)).1
          simpa [nextPhase, updating] using coherent
        · cases selected

theorem candidate_phase (context : Context input) (header : Packet.Header) (before : State input)
    (move : Move) (current : Cursors input) (phase : KeyPhase)
    (selected : nextPhase before.phase.key move = some phase) :
    (candidate context header before (canonicalAction context header before move) current).after.phase.key = phase := by
  rcases before with ⟨cursor, sourcePhase, index⟩
  cases move <;> cases sourcePhase <;> simp only [Phase.key, nextPhase] at selected <;> cases selected <;> rfl

theorem canonical_key (context : Context input) (header : Packet.Header) (before : State input)
    (move : Move) (after : Key input) (selected : Control.step context header before.key move = some after) :
    (candidate context header before (canonicalAction context header before move) after.current).after.key = after := by
  have phase := candidate_phase context header before move after.current after.phase
    (control_frame context header before.key after move selected).1
  exact congrArg (fun next => (⟨after.current, next⟩ : Key input)) phase

theorem canonical_observations (context : Context input) (header : Packet.Header) (before : State input)
    (valid : before.Valid context header) (move : Move) (after : Key input)
    (selected : Control.step context header before.key move = some after) :
    observationsMatch context header before (canonicalAction context header before move) = true := by
  have phases := (control_frame context header before.key after move selected).1
  rcases before with ⟨current, phase, index⟩
  cases phase with
  | held node =>
    cases move <;> simp_all [canonicalAction, observationsMatch, State.key, Phase.key, nextPhase]
  | flight stamp =>
    have flight : stamp.Valid context header current index := valid
    cases move <;> simp_all [canonicalAction, observationsMatch, State.key, Phase.key, nextPhase,
      flight.packetID, flight.headerEq]
  | delivered receipt =>
    cases move <;> simp_all [canonicalAction, observationsMatch, State.key, Phase.key, nextPhase]

theorem canonical_raw (context : Context input) (header : Packet.Header) (before : State input)
    (valid : before.Valid context header) (move : Move) (after : Key input)
    (selected : Control.step context header before.key move = some after) :
    rawAdvance context header before (canonicalAction context header before move) =
      .ok (candidate context header before (canonicalAction context header before move) after.current) := by
  have observed := canonical_observations context header before valid move after selected
  have matched := canonical_key context header before move after selected
  simp only [rawAdvance, observed, canonicalAction_move, selected, matched, ↓reduceIte]

theorem canonical_lift (context : Context input) (header : Packet.Header) (before : State input)
    (valid : before.Valid context header) (move : Move) (after : Key input)
    (selected : Control.step context header before.key move = some after) :
    ∃ value : Advanced context header before (canonicalAction context header before move),
      advance context header before (canonicalAction context header before move) = .ok value ∧
        value.outcome.after.key = after := by
  obtain ⟨value, succeeded, same⟩ := advance_of_raw context header before _ _
    (canonical_raw context header before valid move after selected)
  exact ⟨value, succeeded, by rw [same]; exact canonical_key context header before move after selected⟩

theorem candidate_valid (context : Context input) (header : Packet.Header) (before : State input)
    (valid : before.Valid context header) (action : Action) (current : Cursors input)
    (observed : observationsMatch context header before action = true)
    (keyStep : KeyStep context header before action (candidate context header before action current).after) :
    (candidate context header before action current).after.Valid context header := by
  cases action with
  | idle =>
    rw [candidate_idle] at keyStep ⊢
    have same : current = before.current := congrArg Key.current keyStep
    simpa only [same] using valid.tick
  | send observation target =>
    cases phase : before.phase with
    | held source =>
      rw [candidate_send context header before observation source target current phase] at keyStep ⊢
      simp only [KeyStep, Action.move?, Control.step, State.key, phase, Phase.key] at keyStep
      split at keyStep
      · rename_i accepted
        have same : before.current = current := congrArg Key.current (Option.some.inj keyStep)
        subst current
        have checks := (Bool.and_eq_true _ _).mp accepted
        have first := (Bool.and_eq_true _ _).mp checks.1
        exact ⟨rfl, rfl, first.1, first.2, checks.2, Nat.lt_succ_self _, checks.2, rfl⟩
      · cases keyStep
    | flight stamp => simp [observationsMatch, phase] at observed
    | delivered index => simp [observationsMatch, phase] at observed
  | arrive observation index =>
    cases phase : before.phase with
    | held node => simp [observationsMatch, phase] at observed
    | flight stamp =>
      have flight : stamp.Valid context header before.current before.nextIndex := by simpa only [State.Valid, phase] using valid
      rw [candidate_arrive context header before observation index stamp current phase] at keyStep ⊢
      have same : current = before.current :=
        (control_frame context header before.key _ .arrive keyStep).2.1 rfl
      change Control.known input current stamp.target = true
      rw [same]
      exact flight.receiverKnown
    | delivered receipt => simp [observationsMatch, phase] at observed
  | receive observation =>
    cases phase : before.phase with
    | held node =>
      rw [candidate_receive context header before observation node current phase]
      exact Nat.lt_succ_self _
    | flight stamp => simp [observationsMatch, phase] at observed
    | delivered index => simp [observationsMatch, phase] at observed
  | updateLeft index =>
    have coherent := (control_frame context header before.key _ (.updateLeft index) keyStep).2.2 rfl
    rw [candidate_updateLeft]
    exact valid.relocate current coherent
  | updateRight index =>
    have coherent := (control_frame context header before.key _ (.updateRight index) keyStep).2.2 rfl
    rw [candidate_updateRight]
    exact valid.relocate current coherent
  | updateBoth first second =>
    have coherent := (control_frame context header before.key _ (.updateBoth first second) keyStep).2.2 rfl
    rw [candidate_updateBoth]
    exact valid.relocate current coherent

theorem facts_valid (context : Context input) (header : Packet.Header) (before : State input)
    (valid : before.Valid context header) (action : Action) (outcome : Outcome input)
    (facts : Facts context header before action outcome) : outcome.after.Valid context header := by
  have checked := candidate_valid context header before valid action outcome.after.current facts.observations
    (by rw [facts.candidateEq]; exact facts.keyStep)
  rw [facts.candidateEq] at checked
  exact checked

theorem step_valid (context : Context input) (header : Packet.Header)
    {before after : State input} {event : Event input} (valid : before.Valid context header)
    (step : (system context header).step before event after) : after.Valid context header := by
  obtain ⟨outcome, facts, rfl, _⟩ := step_facts context header step
  exact facts_valid context header before valid event.action outcome facts

theorem invariant (context : Context input) (header : Packet.Header) :
    (system context header).Invariant (fun state => state.Valid context header) :=
  fun _ _ _ valid step => step_valid context header valid step

theorem trace_valid {deployment : Deployment.Checked input} {context : Context input}
    (checked : Context.Validated deployment context) (header : Packet.Header)
    {events : List (Event input)} {after : State input}
    (trace : (system context header).Trace (initialState context) events after) : after.Valid context header :=
  (invariant context header).trace (initial_valid checked header) trace

theorem trace_tick (context : Context input) (header : Packet.Header)
    {before after : State input} {events : List (Event input)}
    (trace : (system context header).Trace before events after) :
    after.nextIndex = before.nextIndex + events.length := by
  induction trace with
  | nil => simp
  | cons edge _ ih =>
    have first := step_tick context header edge
    simp only [List.length_cons]
    omega

theorem initial_trace_index (context : Context input) (header : Packet.Header)
    {after : State input} {events : List (Event input)}
    (trace : (system context header).Trace (initialState context) events after) : after.nextIndex = events.length := by
  simpa only [initialState, Nat.zero_add] using trace_tick context header trace

end Execution
end Netlib.Federation.InFlight
