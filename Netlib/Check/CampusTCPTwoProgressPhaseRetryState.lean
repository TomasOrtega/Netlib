import Netlib.Check.CampusTCPTwoProgressEvidence
import Netlib.Check.CampusTCPTwoProgressPhaseSources

/-!
# Joint packet state after a funded timeout

The waiting state supplies an actual unspent loss cause.
The new ingress carries the same current-head retry and writer ancestry.
-/

namespace Netlib.Check.CampusTCPTwoProgressPhaseRetryState

open Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPRoundPhaseBase (Move)
open CampusTCPTwoProgressStart
open CampusTCPTwoProgressPhaseBase (Core Arrived)
open CampusTCPTwoProgressPhaseState
open CampusTCPTwoProgressReadWriter (SelectedOutput)
open CampusTCPTwoProgressSetup (config)

namespace M
export CampusTCPTwoProgressMonitor (Monitor observe timerTarget)
end M
namespace S
export CampusTCPTwoProgressSender (Stage Part Original)
end S
namespace R
export CampusTCPTwoProgressReceiver (Stage)
end R
namespace Retry
export CampusTCPTwoProgressRetry (HeadRange)
export CampusTCPTwoProgressPhaseRetry (Retried)
end Retry

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current : Cut input complete} {sender : Actor} {gateway : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {native : NativeEnv cut gateway initial.gatewayState.session.entry} {quantum allowance : Nat}
variable {monitor : M.Monitor} {sent : S.Stage initial} {received : R.Stage}
variable {core : Core initial native quantum allowance current monitor sent received}
variable {part : S.Part} {head : Recovery.Outstanding} {rest : List Recovery.Outstanding} {position target : Nat} {actual : Step input}

private theorem selection_retry (selected : Retry.HeadRange sent part head rest) (now : Nat) :
    Retry.HeadRange (sent.retry now) part { head with lastAt := now, retried := true } rest := by
  cases selected <;> constructor

private theorem same_role (before : Retry.HeadRange sent part head rest)
    (after : Retry.HeadRange (sent.retry now) role nextHead nextRest) : role = part := by
  cases before <;> cases after <;> rfl

private theorem upper_missing (active : Active core) (value : Retry.Retried core part head rest position actual) :
    (sent.retry core.live.senderFlight.recovery.now).retiredBytes = 0 → ¬Arrived received .upper →
      (M.observe (config initial native quantum allowance) monitor actual).upper.phase = .done →
      ∃ position, value.next.losses.book.cause .upper = some position := by
  intro zero missing done
  cases selection : value.value.selection with
  | lower first second head =>
    obtain ⟨position, chosen⟩ := active.upperMissing rfl missing (by simpa only [value.observed] using done)
    exact ⟨position, by rw [value.book]; exact chosen⟩
  | upper first second head =>
    have positive := List.length_pos_iff.mpr initial.lowerNonempty
    change lower.length = 0 at zero
    omega

private def after_retry (active : Active core) (value : Retry.Retried core part head rest position actual)
    (waiting : monitor.waiting = true)
    (source : SelectedOutput initial value.value.move.after value.path.output.produced) : Active value.next := by
  have mode := active.waiting_mode waiting
  obtain ⟨lowerDone, upperDone⟩ := active.recovery mode
  obtain ⟨ackNone, _⟩ := active.waiting waiting
  have nextAck : (M.observe (config initial native quantum allowance) monitor actual).ack = none := by
    rw [value.observed]
    exact ackNone
  exact {
    mode := Or.inr (by rw [value.observed]; exact mode)
    preparing := by cases value.value.selection <;> rfl
    nonempty := by cases value.value.selection <;> intro impossible <;> cases impossible
    lowerLane := .done (by rw [value.observed]; exact lowerDone)
    upperLane := .done (by rw [value.observed]; exact upperDone)
    retry := .active part { head with lastAt := core.live.senderFlight.recovery.now, retried := true } rest
      (selection_retry value.value.selection _) (.ingress value.path source)
    ack := by unfold AckState; rw [nextAck]; exact PUnit.unit
    originals := by intro impossible; rw [value.observed] at impossible; change monitor.mode = .originals at impossible; rw [mode] at impossible; cases impossible
    recovery := fun _ => by simpa only [value.observed] using And.intro lowerDone upperDone
    recoveryHead := by
      intro _ _ role nextHead nextRest chosen
      have same := CampusTCPTwoProgressRecoveryHead.head_eq (selection_retry value.value.selection _) chosen
      rw [← same]
    serial := by intro impossible; rw [nextAck] at impossible; cases impossible
    ackNonempty := by intro impossible; rw [nextAck] at impossible; cases impossible
    waiting := by intro impossible; rw [value.observed] at impossible; cases impossible
    runnable := by intro _ _ _; rw [value.path.phase]; decide
    originalOpen := by intro impossible; rw [value.observed] at impossible; change monitor.mode = .originals at impossible; rw [mode] at impossible; cases impossible
    debt := by
      intro role nextHead nextRest selected
      have roleEq := same_role value.value.selection selected
      cases roleEq
      exact ⟨.retry (.ingress value.path)⟩
    upperMissing := upper_missing active value
    zeroAck := by intro _ impossible; rw [nextAck] at impossible; cases impossible
    sources := active.sources.non_delivery value.value.move (by rw [value.value.facts.event]; trivial) }

structure RetriedState (active : Active core) (part : S.Part) (head : Recovery.Outstanding) (rest : List Recovery.Outstanding) where
  actual : Step input
  position : Nat
  value : Retry.Retried core part head rest position actual
  next : Active value.next

theorem lower_at {first : S.Original initial .lower} {second : S.Original initial .upper}
    {core : Core initial native quantum allowance current monitor (.both first second head) received}
    (active : Active core) (waiting : monitor.waiting = true) (budget : allowance ≤ 2)
    (timer : M.timerTarget core.live.senderFlight.recovery = some target) (due : target ≤ core.live.senderFlight.recovery.now) :
    Nonempty (RetriedState active .lower head [second.entry]) := by
  have mode := active.waiting_mode waiting
  obtain ⟨ackNone, _⟩ := active.waiting waiting
  obtain ⟨position, cause⟩ := active.waiting_cause waiting .lower head [second.entry] (.lower first second head)
  obtain ⟨actual, ⟨value⟩⟩ := CampusTCPTwoProgressPhaseRetry.lower_at core mode ackNone waiting budget cause timer due
  exact ⟨⟨actual, position, value, after_retry active value waiting (CampusTCPTwoProgressPhaseSources.lower_retry_source value)⟩⟩

theorem upper_at {first : S.Original initial .lower} {second : S.Original initial .upper}
    {core : Core initial native quantum allowance current monitor (.tail first second head) received}
    (active : Active core) (waiting : monitor.waiting = true) (budget : allowance ≤ 2)
    (timer : M.timerTarget core.live.senderFlight.recovery = some target) (due : target ≤ core.live.senderFlight.recovery.now) :
    Nonempty (RetriedState active .upper head []) := by
  have mode := active.waiting_mode waiting
  obtain ⟨ackNone, _⟩ := active.waiting waiting
  obtain ⟨position, cause⟩ := active.waiting_cause waiting .upper head [] (.upper first second head)
  obtain ⟨actual, ⟨value⟩⟩ := CampusTCPTwoProgressPhaseRetry.upper_at core mode ackNone waiting budget cause timer due
  exact ⟨⟨actual, position, value, after_retry active value waiting (CampusTCPTwoProgressPhaseSources.upper_retry_source value)⟩⟩

variable {active : Active core}

def RetriedState.move (record : RetriedState active part head rest) : Move current record.actual := record.value.value.move

theorem RetriedState.event (record : RetriedState active part head rest) : record.actual.event = .timeout sender true :=
  record.value.value.facts.event

def RetriedState.evidence (record : RetriedState active part head rest) :
    CampusTCPTwoProgressEvidence.Evidence initial native quantum allowance record.move.after
      (M.observe (config initial native quantum allowance) monitor record.actual) :=
  .active record.value.next record.next

end Netlib.Check.CampusTCPTwoProgressPhaseRetryState
