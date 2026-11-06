import Netlib.Check.CampusTCPTwoProgressProgress
import Netlib.Check.CampusTCPTwoProgressClockAge

namespace Netlib.Check.CampusTCPTwoProgressSuffixAge

open Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPRoundPhaseBase (Move)
open CampusTCPTwoProgressStart
open CampusTCPTwoProgressSetup (config)

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current next : Cut input complete} {sender : Actor} {gateway : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {native : NativeEnv cut gateway initial.gatewayState.session.entry} {quantum allowance : Nat}
variable {monitor : CampusTCPTwoProgressMonitor.Monitor}

private theorem parsed_ok (value : Except String α) (output : α) (computed : parsed value = .ok output) :
    value = .ok output := by cases value <;> simp_all [parsed, Except.mapError]

private theorem cursor_event (before : Cursor seed) (event : T.Event) (stamp : Nat) (applied : Applied before)
    (computed : before.apply event stamp = .ok applied) : applied.step.event = event := by
  unfold Cursor.apply at computed
  split at computed
  · cases computed; rfl
  · cases computed

private theorem application_event (before : State input) (actor : Actor) (event : T.Event) (effect : Effect input)
    (computed : applyApplication input before actor event = .ok effect) :
    ∀ selected operation, effect.application = some (selected, operation) → selected = actor ∧ operation.event = event := by
  unfold applyApplication at computed
  split at computed
  · cases computed; intro selected operation recorded; cases recorded
  · cases actor
    all_goals
      simp only [parsed, Except.mapError, bind, Except.bind, pure, Except.pure] at computed
      split at computed
      · cases computed
      · rename_i applied accepted
        have eventEq := cursor_event _ event before.time applied (parsed_ok _ _ accepted)
        repeat' first
          | (solve | cases computed; intro selected operation recorded; cases recorded; exact ⟨rfl, eventEq⟩)
          | (cases computed)
          | (split at computed)
          | (dsimp only [bind, Except.bind, pure, Except.pure, parsed, Except.mapError] at computed)

private theorem startup_none (before : State input) (event : TCPHandshake.Event) (effect : Effect input)
    (computed : startup input before event = .ok effect) : effect.application = none := by
  unfold startup at computed
  repeat' first
    | (solve | cases computed; rfl)
    | (cases computed)
    | (split at computed)
    | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)

private theorem enable_ack_event (before : State input) (actor : Actor) (effect : Effect input)
    (computed : enableAck input before actor = .ok effect) :
    ∀ selected operation, effect.application = some (selected, operation) → selected = actor ∧ operation.event = .enableAck := by
  unfold enableAck at computed
  split at computed
  · exact application_event _ _ _ _ computed
  · cases actor <;> dsimp only at computed
    all_goals split at computed
    all_goals first | exact application_event _ _ _ _ computed | cases computed

private theorem process_clock_origin (before : State input) (event : CampusTCPModel.Event) (effect : Effect input)
    (computed : processCore input before event = .ok effect) (actor : Actor) (operation : T.Step)
    (recorded : effect.application = some (actor, operation)) (millis : Nat) (clock : operation.event = .advanceClock millis) :
    event = .advanceClock actor millis := by
  cases event with
  | advanceClock selected stamp =>
    obtain ⟨sameActor, sameEvent⟩ := application_event _ _ _ _ computed actor operation recorded
    have sameTime := ApplicationTrace.Event.advanceClock.inj (sameEvent.symm.trans clock)
    subst selected stamp
    rfl
  | write selected bytes | send selected count policy | read selected count | emitAck selected policy
    | enableRecovery selected | timeout selected policy | dispatchAck selected policy =>
    have sameEvent := (application_event _ _ _ _ computed actor operation recorded).2
    have impossible := sameEvent.symm.trans clock
    cases impossible
  | enableAck selected =>
    have sameEvent := (enable_ack_event _ _ _ computed actor operation recorded).2
    have impossible := sameEvent.symm.trans clock
    cases impossible
  | «open» remote policy => rw [startup_none _ _ _ computed] at recorded; cases recorded
  | deliver index bytes policy =>
    simp only [processCore] at computed
    repeat' first
      | (solve | cases computed; dsimp only at recorded; rw [startup_none _ _ _ (by assumption)] at recorded; cases recorded)
      | (solve |
          cases computed
          dsimp only at recorded
          have sameEvent := (application_event _ _ _ _ (by assumption) actor operation recorded).2
          have impossible := sameEvent.symm.trans clock
          cases impossible)
      | (cases computed)
      | (split at computed)
      | (dsimp only [CampusTCPModel.get, parsed, Except.mapError, bind, Except.bind, pure, Except.pure,
          throw, throwThe, MonadExceptOf.throw] at computed)
  | authentication index | install id | stage id | installGuard id | installAt gateway id | stageAt gateway id
    | installGuardAt gateway id | assign index ingress | serve id observed | copyPacket id | dropPacket id
    | pause | stageCheckpoint | installCheckpoint ns | switchRoute actor gateway | fencePrimary | resume =>
    simp only [processCore, installConfiguration, stageAttachment, installIngress, transferControl] at computed
    repeat' first
      | (solve | cases computed; cases recorded)
      | (cases computed)
      | (split at computed)
      | (dsimp only [CampusTCPModel.get, parsed, Except.mapError, bind, Except.bind, pure, Except.pure,
          throw, throwThe, MonadExceptOf.throw] at computed)

theorem Step.clock_origin (actual : Step input) (actor : Actor) (operation : T.Step)
    (recorded : actual.result.application = some (actor, operation)) (millis : Nat)
    (clock : operation.event = .advanceClock millis) : actual.event = .advanceClock actor millis := by
  obtain ⟨effect, custody, computed, result⟩ := actual.processed
  exact process_clock_origin actual.before actual.event effect computed actor operation
    (by simpa only [result] using recorded) millis clock

private theorem chain_cons (chain : T.Chain before (head :: tail) after) :
    before = head.before ∧ T.Chain head.result.state tail after := by
  cases chain with
  | cons first rest => exact ⟨rfl, rest⟩

private theorem chain_tail (prior : T.Chain seed earlier before)
    (whole : T.Chain seed (earlier ++ later) after) : T.Chain before later after := by
  induction earlier generalizing seed with
  | nil => cases prior; exact whole
  | cons head tail ih =>
    exact ih (chain_cons prior).2 (chain_cons whole).2

theorem Move.application_chain (move : Move current actual) (actor : Actor) :
    T.Chain (endpoint current.endpoints actor)
      (CampusTCPRecoveryRoundOrigins.localSteps actual.result.application actor) (endpoint move.after.endpoints actor) := by
  have history := CampusTCPRecoveryRoundOrigins.Step.application_history actual actor
  rw [move.beforeEq, current.connection, ← move.final, move.after.connection] at history
  change applicationSteps move.after.endpoints actor = applicationSteps current.endpoints actor ++
    CampusTCPRecoveryRoundOrigins.localSteps actual.result.application actor at history
  have whole := CampusTCPGapProgressStart.endpoint_chain move.after actor
  rw [history] at whole
  exact chain_tail (CampusTCPGapProgressStart.endpoint_chain current actor) whole

theorem Move.local_clock_bound (move : Move current actual) (cfg : CampusTCPTwoProgressMonitor.Config)
    (allowed : CampusTCPTwoProgressMonitor.Allowed cfg current.report.final monitor actual.event)
    (actor : Actor) (operation : T.Step)
    (member : operation ∈ CampusTCPRecoveryRoundOrigins.localSteps actual.result.application actor) :
    CampusTCPTwoProgressClockAge.ClockBound cfg.quantum operation := by
  have recorded := (CampusTCPRecoveryRoundOrigins.mem_localSteps _ _ _).mp member
  have chain := Move.application_chain move actor
  simp only [recorded, CampusTCPRecoveryRoundOrigins.localSteps, ite_true] at chain
  have localBefore := (chain_cons chain).1.symm
  intro millis event
  have selected := Step.clock_origin actual actor operation recorded millis event
  rw [localBefore]
  obtain ⟨_, _, _, upper, _⟩ := CampusTCPGapProgressClock.clock_allowed_fields cfg.toConfig current actor millis
    (CampusTCPTwoProgressClock.allowed_guard cfg current monitor actor millis (by rw [← selected]; exact allowed))
  exact upper

private theorem local_length (application : Option (Actor × T.Step)) (actor : Actor) :
    (CampusTCPRecoveryRoundOrigins.localSteps application actor).length ≤ 1 := by
  cases application with
  | none => exact Nat.zero_le _
  | some pair =>
    obtain ⟨selected, operation⟩ := pair
    by_cases same : selected = actor <;> simp [CampusTCPRecoveryRoundOrigins.localSteps, same]

theorem Move.actor_now_le (move : Move current actual) (cfg : CampusTCPTwoProgressMonitor.Config)
    (allowed : CampusTCPTwoProgressMonitor.Allowed cfg current.report.final monitor actual.event) (actor : Actor) :
    (endpoint move.after.endpoints actor).now ≤ (endpoint current.endpoints actor).now + cfg.quantum := by
  have upper := CampusTCPTwoProgressClockAge.Chain.now_le_length (Move.application_chain move actor)
    (fun operation member => Move.local_clock_bound move cfg allowed actor operation member)
  have count := Nat.mul_le_mul_right cfg.quantum (local_length actual.result.application actor)
  simp only [Nat.one_mul] at count
  exact Nat.le_trans upper (Nat.add_le_add_left count _)

def nowAt (state : State input) (actor : Actor) : Nat :=
  match state.connection with
  | .startup .. => 0
  | .application _ endpoints => (endpoint endpoints actor).now

theorem nowAt_cut (current : Cut input complete) (actor : Actor) :
    nowAt current.report.final actor = (endpoint current.endpoints actor).now := by
  simp only [nowAt, current.connection]

theorem Move.nowAt_le (move : Move current actual) (cfg : CampusTCPTwoProgressMonitor.Config)
    (allowed : CampusTCPTwoProgressMonitor.Allowed cfg current.report.final monitor actual.event) (actor : Actor) :
    nowAt move.after.report.final actor ≤ nowAt current.report.final actor + cfg.quantum := by
  rw [nowAt_cut, nowAt_cut]
  exact Move.actor_now_le move cfg allowed actor

variable {suffix remaining : List CampusTCPModel.Event} {steps : List (Step input)} {final : State input}

theorem Trace.application_projection (trace : Trace input before events recorded after unread) (actor : Actor) :
    CampusTCPRoundPhaseHistory.connectionSteps after.connection actor =
      CampusTCPRoundPhaseHistory.connectionSteps before.connection actor ++
        recorded.flatMap (fun actual => CampusTCPRecoveryRoundOrigins.localSteps actual.result.application actor) := by
  induction trace with
  | done state => simp only [List.flatMap_nil, List.append_nil]
  | stop head blocked rest =>
    rw [CampusTCPRecoveryRoundOrigins.Step.application_history head]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  | next head supported rest ih =>
    rw [ih, CampusTCPRecoveryRoundOrigins.Step.application_history head]
    simp only [List.flatMap_cons, List.append_assoc]

theorem local_count_le (recorded : List (Step input)) (actor : Actor) :
    (recorded.flatMap (fun actual => CampusTCPRecoveryRoundOrigins.localSteps actual.result.application actor)).length ≤ recorded.length := by
  induction recorded with
  | nil => exact Nat.le_refl _
  | cons head tail ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    have bound := local_length head.result.application actor
    omega

theorem trace_application_projection (trace : Trace input cut.report.final suffix steps final remaining)
    (slot : Nat) (within : slot ≤ steps.length) (actor : Actor) :
    CampusTCPRoundPhaseHistory.connectionSteps (CampusTCPSchedule.stateAt cut.report.final steps slot).connection actor =
      applicationSteps cut.endpoints actor ++ (steps.take slot).flatMap
        (fun actual => CampusTCPRecoveryRoundOrigins.localSteps actual.result.application actor) := by
  have projection := Trace.application_projection (CampusTCPSchedule.Trace.take trace slot within) actor
  rw [cut.connection] at projection
  exact projection

theorem trace_local_count_le (_trace : Trace input cut.report.final suffix steps final remaining)
    (slot : Nat) (within : slot ≤ steps.length) (actor : Actor) :
    ((steps.take slot).flatMap (fun actual => CampusTCPRecoveryRoundOrigins.localSteps actual.result.application actor)).length ≤ slot := by
  have bound := local_count_le (steps.take slot) actor
  rw [List.length_take, Nat.min_eq_left within] at bound
  exact bound

theorem trace_clock_count_le (trace : Trace input cut.report.final suffix steps final remaining)
    (slot : Nat) (within : slot ≤ steps.length) (actor : Actor) :
    CampusTCPTwoProgressClockAge.clockCount ((steps.take slot).flatMap
      (fun actual => CampusTCPRecoveryRoundOrigins.localSteps actual.result.application actor)) ≤ slot :=
  Nat.le_trans List.countP_le_length (trace_local_count_le trace slot within actor)

theorem trace_now_le (trace : Trace input cut.report.final suffix steps final remaining)
    (actions : CampusTCPTwoProgressProgress.Actions initial native quantum allowance steps) (budget : allowance ≤ 2)
    (slot : Nat) (within : slot ≤ steps.length) (actor : Actor) :
    nowAt (CampusTCPSchedule.stateAt cut.report.final steps slot) actor ≤
      (endpoint cut.endpoints actor).now + slot * quantum := by
  induction slot with
  | zero => simp only [CampusTCPSchedule.stateAt_zero, nowAt_cut, Nat.zero_mul, Nat.add_zero, Nat.le_refl]
  | succ slot ih =>
    have earlier : slot ≤ steps.length := by omega
    have live : slot < steps.length := by omega
    obtain ⟨current, same, ⟨evidence⟩⟩ := CampusTCPTwoProgressProgress.trace_invariant trace actions budget slot earlier
    obtain ⟨actual, _, before, event, after⟩ := CampusTCPSchedule.Trace.at trace slot live
    have allowed : CampusTCPTwoProgressMonitor.Allowed (config initial native quantum allowance) current.report.final
        (CampusTCPTwoProgressMonitor.monitorAt (config initial native quantum allowance) .initial steps slot) actual.event := by
      rw [same, event]
      exact actions slot live
    obtain ⟨move, _⟩ := evidence.step budget actual (before.trans same.symm) allowed
    have tick := Move.nowAt_le move (config initial native quantum allowance) allowed actor
    rw [move.final, after, same] at tick
    change nowAt (CampusTCPSchedule.stateAt cut.report.final steps (slot + 1)) actor ≤
      nowAt (CampusTCPSchedule.stateAt cut.report.final steps slot) actor + quantum at tick
    have prior := ih earlier
    simp only [Nat.add_mul, Nat.one_mul]
    omega

theorem trace_cut_now (trace : Trace input cut.report.final suffix steps final remaining)
    (actions : CampusTCPTwoProgressProgress.Actions initial native quantum allowance steps) (budget : allowance ≤ 2)
    (slot : Nat) (within : slot ≤ steps.length) :
    ∃ current : Cut input complete,
      current.report.final = CampusTCPSchedule.stateAt cut.report.final steps slot ∧
      Nonempty (CampusTCPTwoProgressEvidence.Evidence initial native quantum allowance current
        (CampusTCPTwoProgressMonitor.monitorAt (config initial native quantum allowance) .initial steps slot)) ∧
      ∀ actor, (endpoint current.endpoints actor).now ≤ (endpoint cut.endpoints actor).now + slot * quantum := by
  obtain ⟨current, same, evidence⟩ := CampusTCPTwoProgressProgress.trace_invariant trace actions budget slot within
  change current.report.final = CampusTCPSchedule.stateAt cut.report.final steps slot at same
  refine ⟨current, same, evidence, ?_⟩
  intro actor
  have upper := trace_now_le trace actions budget slot within actor
  rw [← same, nowAt_cut] at upper
  exact upper

def OriginalAges (initial : TwoWriteInitial cut sender gateway lower upper) (now span : Nat) :
    CampusTCPTwoProgressSender.Stage initial → Prop
  | .written => True
  | .lower first => now - first.operation.before.now ≤ span
  | .both first second _ | .tail first second _ | .retired first second =>
    now - first.operation.before.now ≤ span ∧ now - second.operation.before.now ≤ span

theorem trace_core_ages (trace : Trace input cut.report.final suffix steps final remaining)
    (actions : CampusTCPTwoProgressProgress.Actions initial native quantum allowance steps) (budget : allowance ≤ 2)
    (slot : Nat) (within : slot ≤ steps.length) (current : Cut input complete)
    (same : current.report.final = CampusTCPSchedule.stateAt cut.report.final steps slot)
    {sent : CampusTCPTwoProgressSender.Stage initial} {received : CampusTCPTwoProgressReceiver.Stage}
    {selectedMonitor : CampusTCPTwoProgressMonitor.Monitor}
    (core : CampusTCPTwoProgressPhaseBase.Core initial native quantum allowance current selectedMonitor sent received) :
    OriginalAges initial (endpoint current.endpoints sender).now (slot * quantum) sent := by
  have upper := trace_now_le trace actions budget slot within sender
  rw [← same, nowAt_cut] at upper
  have times := core.originalTimes
  cases sent <;> simp only [OriginalAges, CampusTCPTwoProgressPhaseBase.OriginalTimes] at * <;> omega

theorem trace_both_ages (trace : Trace input cut.report.final suffix steps final remaining)
    (actions : CampusTCPTwoProgressProgress.Actions initial native quantum allowance steps) (budget : allowance ≤ 2)
    (slot : Nat) (within : slot ≤ steps.length) (current : Cut input complete)
    (same : current.report.final = CampusTCPSchedule.stateAt cut.report.final steps slot)
    {first : CampusTCPTwoProgressSender.Original initial .lower} {second : CampusTCPTwoProgressSender.Original initial .upper}
    {head : Recovery.Outstanding} {received : CampusTCPTwoProgressReceiver.Stage}
    {selectedMonitor : CampusTCPTwoProgressMonitor.Monitor}
    (core : CampusTCPTwoProgressPhaseBase.Core initial native quantum allowance current selectedMonitor (.both first second head) received) :
    (endpoint current.endpoints sender).now - first.operation.before.now ≤ slot * quantum ∧
      (endpoint current.endpoints sender).now - second.operation.before.now ≤ slot * quantum :=
  trace_core_ages trace actions budget slot within current same core

end Netlib.Check.CampusTCPTwoProgressSuffixAge
