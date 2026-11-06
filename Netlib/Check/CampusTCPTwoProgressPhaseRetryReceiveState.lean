import Netlib.Check.CampusTCPTwoProgressPhaseReceiveState

namespace Netlib.Check.CampusTCPTwoProgressPhaseReceiveState

open Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart CampusTCPTwoProgressPhaseBase CampusTCPTwoProgressPhaseState
open CampusTCPTwoProgressPaths
open CampusTCPTwoProgressSetup (config)

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current : Cut input complete} {sender : Actor} {gateway : Gateway} {lower upper chunk : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {native : NativeEnv cut gateway initial.gatewayState.session.entry} {quantum allowance : Nat}
variable {monitor : M.Monitor} {sent : S.Stage initial} {beforeStage afterStage : R.Stage}
variable {core : Core initial native quantum allowance current monitor sent beforeStage}
variable {part : S.Part} {head : Recovery.Outstanding} {rest : List Recovery.Outstanding}

private theorem head_part (first : CampusTCPTwoProgressRetry.HeadRange sent part head rest)
    (second : CampusTCPTwoProgressRetry.HeadRange sent other otherHead otherRest) : other = part := by
  cases first <;> cases second <;> rfl

private def retry_finish (active : Active core) (path : DataLink initial current part monitor.retry)
    (source : CampusTCPTwoProgressReadWriter.SelectedOutput initial current path.served.ticket.value.produced)
    (selected : CampusTCPTwoProgressRetry.HeadRange sent part head rest) (mode : monitor.mode = .recovery)
    (value : D.Delivered core path afterStage chunk) (arrival : D.Arrival beforeStage part afterStage)
    (covered : part.offset lower + (part.bytes lower upper).length ≤ (afterStage.bytes lower upper).length)
    (observed : CampusTCPTwoProgressMonitor.observe (config initial native quantum allowance) monitor value.value.delivery.step =
      O.receiptUpdate monitor .retry current.report.final.receipts.length value.value.delivery.localStep.stamp chunk) :
    Active value.next := by
  have lowerEq := congrArg CampusTCPTwoProgressMonitor.Monitor.lower observed
  change (CampusTCPTwoProgressMonitor.observe (config initial native quantum allowance) monitor value.value.delivery.step).lower = monitor.lower at lowerEq
  have upperEq := congrArg CampusTCPTwoProgressMonitor.Monitor.upper observed
  change (CampusTCPTwoProgressMonitor.observe (config initial native quantum allowance) monitor value.value.delivery.step).upper = monitor.upper at upperEq
  have retryEq := congrArg CampusTCPTwoProgressMonitor.Monitor.retry observed
  have ackEq := congrArg CampusTCPTwoProgressMonitor.Monitor.ack observed
  have strict := head_coverage_strict selected covered
  refine {
    mode := ?_, preparing := active.preparing, nonempty := active.nonempty
    recoveryHead := by
      intro _ _ role currentHead currentRest current
      have oldWaiting : monitor.waiting = false := by
        cases waiting : monitor.waiting with
        | false => rfl
        | true =>
          have done := (active.waiting waiting).2
          have impossible := path.phase.symm.trans done
          cases impossible
      exact active.recoveryHead mode oldWaiting role currentHead currentRest current
    lowerLane := ?_, upperLane := ?_, retry := ?_, ack := ?_
    originals := ?_, recovery := ?_, serial := ?_, ackNonempty := ?_, waiting := ?_, runnable := ?_, originalOpen := ?_
    debt := ?_, upperMissing := ?_, zeroAck := ?_, sources := active.sources.data path source value.value }
  · rw [observed]
    exact .inr mode
  · rw [lowerEq]
    exact .done (active.recovery mode).1
  · rw [upperEq]
    exact .done (active.recovery mode).2
  · rw [retryEq]
    exact .done rfl
  · unfold AckState
    rw [ackEq]
    exact .pending rfl (receive_pending_queue value)
  · intro wrong
    rw [observed] at wrong
    have impossible : CampusTCPTwoProgressMonitor.Mode.recovery = .originals := mode.symm.trans wrong
    cases impossible
  · intro _
    rw [observed]
    exact active.recovery mode
  · intro _
    rw [observed]
    rfl
  · intro _ empty
    rw [empty, CampusTCPTwoProgressReceiver.Stage.bytes] at strict
    exact Nat.not_lt_zero _ strict
  · intro waiting
    rw [observed] at waiting
    cases waiting
  · intro _ _ none
    rw [observed] at none
    cases none
  · intro _ none
    rw [observed] at none
    cases none
  · intro role currentHead currentRest current
    have same := head_part selected current
    subst role
    exact ⟨.ack _ (by rw [ackEq]; rfl) covered⟩
  · intro noRetirement absent done
    cases part with
    | lower =>
      have beforeAbsent : ¬Arrived beforeStage .upper := by
        intro arrived
        cases arrival <;> simp_all [Arrived]
      obtain ⟨position, cause⟩ := active.upperMissing noRetirement beforeAbsent (active.recovery mode).2
      exact ⟨position, by rw [value.book]; exact cause⟩
    | upper =>
      have positive := List.length_pos_iff.mpr initial.upperNonempty
      cases afterStage <;> simp_all [Arrived, CampusTCPTwoProgressReceiver.Stage.bytes,
        CampusTCPTwoProgressSender.Part.offset, CampusTCPTwoProgressSender.Part.bytes, List.length_append]
      all_goals omega
  · intro _ _ equal
    exact False.elim (Nat.ne_of_lt strict equal)

private structure RetryLink (core : Core initial native quantum allowance current monitor sent beforeStage) where
  part : S.Part
  head : Recovery.Outstanding
  rest : List Recovery.Outstanding
  selected : CampusTCPTwoProgressRetry.HeadRange sent part head rest
  path : DataLink initial current part monitor.retry
  source : CampusTCPTwoProgressReadWriter.SelectedOutput initial current path.served.ticket.value.produced
  covered : (CampusTCPTwoProgressPathsReady.rangeAt core.live.gatewayState part).isSome = true

private def retry_link (active : Active core) (phase : monitor.retry.phase = .dataLink) : RetryLink core := by
  cases active.retry with
  | done done => rw [done] at phase; cases phase
  | active role head rest selected work =>
    cases work with
    | ingress path source => rw [path.phase] at phase; cases phase
    | ticket path source => rw [path.phase] at phase; cases phase
    | link path source covered => exact ⟨role, head, rest, selected, path, source, covered⟩

private theorem retry_mode (active : Active core) (phase : monitor.retry.phase = .dataLink) : monitor.mode = .recovery := by
  rcases active.mode with original | recovery
  · have done := (active.originals original).1
    rw [done] at phase
    cases phase
  · exact recovery

private theorem retry_ack (active : Active core) (phase : monitor.retry.phase = .dataLink) : monitor.ack = none := by
  cases ack : monitor.ack with
  | none => rfl
  | some lane =>
    have done := active.serial (by rw [ack]; rfl)
    rw [done] at phase
    cases phase

private theorem retry_waiting (active : Active core) (phase : monitor.retry.phase = .dataLink) : monitor.waiting = false := by
  cases waiting : monitor.waiting with
  | false => rfl
  | true =>
    have done := (active.waiting waiting).2
    rw [done] at phase
    cases phase

private theorem retry_allowed (_active : Active core) (path : DataLink initial current part monitor.retry)
    (mode : monitor.mode = .recovery) (ack : monitor.ack = none) (waiting : monitor.waiting = false) :
    CampusTCPTwoProgressMonitor.Allowed (config initial native quantum allowance) current.report.final monitor
      (.deliver path.index path.emission.bytes true) := by
  let cfg := config initial native quantum allowance
  have serves := CampusTCPTwoProgressPhaseObserve.laneDemand_serves cfg current.report.final monitor monitor.retry _ (path.action cfg)
  obtain ⟨demand, chosen, served⟩ := (CampusTCPTwoProgressMonitorFacts.servesOption_iff _ _).mp serves
  apply (CampusTCPTwoProgressMonitorFacts.allowed_iff cfg current.report.final monitor _).mpr
  refine ⟨by rw [mode]; decide, .inl ⟨.single demand, ?_, served⟩, rfl⟩
  simp only [CampusTCPTwoProgressMonitor.nextDemand, mode, ack, waiting, Bool.false_eq_true, ite_false,
    chosen, Option.map_some]

private theorem upper_before (core : Core initial native quantum allowance current monitor (.tail first second head) beforeStage) :
    beforeStage = .lowerReleased ∨ beforeStage = .allReleased := by
  have bounded := core.retired
  change lower.length ≤ (beforeStage.bytes lower upper).length at bounded
  have positive := List.length_pos_iff.mpr initial.lowerNonempty
  cases beforeStage <;> simp_all [CampusTCPTwoProgressReceiver.Stage.bytes]

theorem retry_at (active : Active core) (phase : monitor.retry.phase = .dataLink) :
    ∃ part, Nonempty (Received core part .retry) := by
  obtain ⟨part, head, rest, selected, path, source, covered⟩ := retry_link active phase
  have mode := retry_mode active phase
  have ack := retry_ack active phase
  have waiting := retry_waiting active phase
  have allowed := retry_allowed active path mode ack waiting
  cases selected with
  | lower first second head =>
    cases beforeStage with
    | empty =>
      obtain ⟨value⟩ := CampusTCPTwoProgressPhaseReceive.lower_at core path covered
      have observed := CampusTCPTwoProgressPhaseObserveReceive.receipt_retry value mode ack waiting allowed
      exact ⟨.lower, ⟨⟨path, .lowerReleased, lower, value, observed,
        retry_finish active path source (.lower first second head) mode value .lower
          (by change 0 + lower.length ≤ lower.length; omega) observed⟩⟩⟩
    | upperHeld =>
      obtain ⟨value⟩ := CampusTCPTwoProgressPhaseReceive.gap_at core path covered
      have observed := CampusTCPTwoProgressPhaseObserveReceive.receipt_retry value mode ack waiting allowed
      exact ⟨.lower, ⟨⟨path, .allReleased, lower ++ upper, value, observed,
        retry_finish active path source (.lower first second head) mode value .gap
          (by simp only [CampusTCPTwoProgressSender.Part.offset, CampusTCPTwoProgressSender.Part.bytes,
            CampusTCPTwoProgressReceiver.Stage.bytes, List.length_append]; omega) observed⟩⟩⟩
    | lowerReleased =>
      obtain ⟨value⟩ := CampusTCPTwoProgressPhaseReceive.old_lower_at core path covered
      have observed := CampusTCPTwoProgressPhaseObserveReceive.receipt_retry value mode ack waiting allowed
      exact ⟨.lower, ⟨⟨path, .lowerReleased, [], value, observed,
        retry_finish active path source (.lower first second head) mode value (.old _ _)
          (by change 0 + lower.length ≤ lower.length; omega) observed⟩⟩⟩
    | allReleased =>
      obtain ⟨value⟩ := CampusTCPTwoProgressPhaseReceive.old_lower_all_at core path covered
      have observed := CampusTCPTwoProgressPhaseObserveReceive.receipt_retry value mode ack waiting allowed
      exact ⟨.lower, ⟨⟨path, .allReleased, [], value, observed,
        retry_finish active path source (.lower first second head) mode value (.old _ _)
          (by simp only [CampusTCPTwoProgressSender.Part.offset, CampusTCPTwoProgressSender.Part.bytes,
            CampusTCPTwoProgressReceiver.Stage.bytes, List.length_append]; omega) observed⟩⟩⟩
  | upper first second head =>
    rcases upper_before core with prior | prior
    · subst beforeStage
      obtain ⟨value⟩ := CampusTCPTwoProgressPhaseReceive.upper_at core path covered
      have observed := CampusTCPTwoProgressPhaseObserveReceive.receipt_retry value mode ack waiting allowed
      exact ⟨.upper, ⟨⟨path, .allReleased, upper, value, observed,
        retry_finish active path source (.upper first second head) mode value .upper
          (by change lower.length + upper.length ≤ (lower ++ upper).length; simp only [List.length_append, Nat.le_refl]) observed⟩⟩⟩
    · subst beforeStage
      obtain ⟨value⟩ := CampusTCPTwoProgressPhaseReceive.old_upper_at core path covered
      have observed := CampusTCPTwoProgressPhaseObserveReceive.receipt_retry value mode ack waiting allowed
      exact ⟨.upper, ⟨⟨path, .allReleased, [], value, observed,
        retry_finish active path source (.upper first second head) mode value (.old _ _)
          (by change lower.length + upper.length ≤ (lower ++ upper).length; simp only [List.length_append, Nat.le_refl]) observed⟩⟩⟩

theorem Received.step_eq {target : CampusTCPTwoProgressMonitor.DropTarget}
    (value : Received core part target) (actual : Step input)
    (before : actual.before = current.report.final)
    (event : actual.event = .deliver value.path.index value.path.emission.bytes true) :
    value.value.value.delivery.step = actual := value.value.step_eq actual before event

end Netlib.Check.CampusTCPTwoProgressPhaseReceiveState
