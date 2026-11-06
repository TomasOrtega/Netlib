import Netlib.Check.CampusTCPTwoProgressPhaseDebt
import Netlib.Check.CampusTCPTwoProgressPhaseSources
import Netlib.Check.CampusTCPTwoProgressReceiptSources
import Netlib.Check.CampusTCPTwoProgressRecoveryHead

/-!
# Current typed packet state after both original sends

Live data paths retain selected writer ancestry and current coverage.
The head debt names current work, a covering ACK, or a recorded loss.
-/

namespace Netlib.Check.CampusTCPTwoProgressPhaseState

open Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart
open CampusTCPTwoProgressPhaseBase (Core Arrived)
open CampusTCPTwoProgressPaths
open CampusTCPTwoProgressReadWriter (SelectedOutput)
open CampusTCPTwoProgressPathsReady (rangeAt)

namespace S
export CampusTCPTwoProgressSender (Part Stage Original)
end S
namespace R
export CampusTCPTwoProgressReceiver (Stage)
end R
namespace M
export CampusTCPTwoProgressMonitor (Monitor Lane)
end M

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current : Cut input complete} {sender : Actor} {gateway : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {native : NativeEnv cut gateway initial.gatewayState.session.entry} {quantum allowance : Nat}
variable {monitor : M.Monitor} {sent : S.Stage initial} {received : R.Stage}

inductive DataWork (initial : TwoWriteInitial cut sender gateway lower upper)
    (native : NativeEnv cut gateway initial.gatewayState.session.entry) (current : Cut input complete)
    (view : CampusTCPTwoProgressGatewayState.View initial current) (part : S.Part) (lane : M.Lane) where
  | ingress (path : DataIngress initial current part lane) (source : SelectedOutput initial current path.output.produced)
  | ticket (path : DataTicket initial native current part lane) (source : SelectedOutput initial current path.output.produced)
  | link (path : DataLink initial current part lane) (source : SelectedOutput initial current path.served.ticket.value.produced)
      (covered : (rangeAt view part).isSome = true)

def DataWork.work {view : CampusTCPTwoProgressGatewayState.View initial current} {part : S.Part} {lane : M.Lane}
    (value : DataWork initial native current view part lane) : CampusTCPTwoProgressPhaseDebt.Work initial native current part lane := by
  cases value with
  | ingress path _ => exact .ingress path
  | ticket path _ => exact .ticket path
  | link path _ _ => exact .link path

inductive OriginalLane (initial : TwoWriteInitial cut sender gateway lower upper)
    (native : NativeEnv cut gateway initial.gatewayState.session.entry) (current : Cut input complete)
    (view : CampusTCPTwoProgressGatewayState.View initial current) (received : R.Stage) (part : S.Part) (lane : M.Lane) where
  | active (work : DataWork initial native current view part lane) (missing : ¬Arrived received part)
  | done (phase : lane.phase = .done)

inductive RetryLane (initial : TwoWriteInitial cut sender gateway lower upper)
    (native : NativeEnv cut gateway initial.gatewayState.session.entry) (current : Cut input complete)
    (view : CampusTCPTwoProgressGatewayState.View initial current) (sent : S.Stage initial) (lane : M.Lane) where
  | active (part : S.Part) (head : Recovery.Outstanding) (rest : List Recovery.Outstanding)
      (selected : CampusTCPTwoProgressRetry.HeadRange sent part head rest)
      (work : DataWork initial native current view part lane)
  | done (phase : lane.phase = .done)

inductive AckWork (core : Core initial native quantum allowance current monitor sent received) (lane : M.Lane) where
  | pending (phase : lane.phase = .needAck) (queue : core.live.receiverFacts.reaction.work.pending ≠ [])
  | ingress (path : AckIngress initial current (received.bytes lower upper).length lane)
  | ticket (path : AckTicket initial native current (received.bytes lower upper).length lane)
  | link (path : AckLink initial current (received.bytes lower upper).length lane)

def AckState (core : Core initial native quantum allowance current monitor sent received) : Type :=
  match monitor.ack with
  | none => PUnit
  | some lane => AckWork core lane

structure Active (core : Core initial native quantum allowance current monitor sent received) where
  mode : monitor.mode = .originals ∨ monitor.mode = .recovery
  preparing : sent.preparing = false
  nonempty : sent.ledger ≠ []
  lowerLane : OriginalLane initial native current core.live.gatewayState received .lower monitor.lower
  upperLane : OriginalLane initial native current core.live.gatewayState received .upper monitor.upper
  retry : RetryLane initial native current core.live.gatewayState sent monitor.retry
  ack : AckState core
  originals : monitor.mode = .originals → monitor.retry.phase = .done ∧ monitor.waiting = false ∧ monitor.retries = 0
  recovery : monitor.mode = .recovery → monitor.lower.phase = .done ∧ monitor.upper.phase = .done
  recoveryHead : monitor.mode = .recovery → monitor.waiting = false →
    ∀ part head rest, CampusTCPTwoProgressRetry.HeadRange sent part head rest → head.retried = true
  serial : monitor.ack.isSome = true → monitor.retry.phase = .done
  ackNonempty : monitor.ack.isSome = true → received ≠ .empty
  ackGateway : ∀ lane, monitor.ack = some lane → lane.phase = .ackLink →
    (core.live.gatewayState.gateway.session.lane sender.direction).acknowledged =
      initial.geometry.«prefix» + (received.bytes lower upper).length
  waiting : monitor.waiting = true → monitor.ack = none ∧ monitor.retry.phase = .done
  runnable : monitor.mode = .recovery → monitor.waiting = false → monitor.ack = none → monitor.retry.phase ≠ .done
  originalOpen : monitor.mode = .originals → monitor.ack = none → ¬(monitor.lower.phase = .done ∧ monitor.upper.phase = .done)
  debt : ∀ part head rest, CampusTCPTwoProgressRetry.HeadRange sent part head rest → Nonempty (CampusTCPTwoProgressPhaseDebt.Debt core part)
  upperMissing : sent.retiredBytes = 0 → ¬Arrived received .upper → monitor.upper.phase = .done →
    ∃ position, core.losses.book.cause .upper = some position
  zeroAck : ∀ lane, monitor.ack = some lane → sent.retiredBytes = (received.bytes lower upper).length →
    core.live.senderFlight.recovery.duplicateAcks = 0
  sources : CampusTCPTwoProgressReceiptSources.History initial current

theorem Active.waiting_mode {core : Core initial native quantum allowance current monitor sent received}
    (value : Active core) (waiting : monitor.waiting = true) : monitor.mode = .recovery := by
  rcases value.mode with original | recovery
  · have quiet := (value.originals original).2.1
    rw [quiet] at waiting
    cases waiting
  · exact recovery

theorem Active.waiting_cause {core : Core initial native quantum allowance current monitor sent received}
    (value : Active core) (waiting : monitor.waiting = true)
    (part : S.Part) (head : Recovery.Outstanding) (rest : List Recovery.Outstanding)
    (selected : CampusTCPTwoProgressRetry.HeadRange sent part head rest) :
    ∃ position, core.losses.book.cause part = some position := by
  obtain ⟨lowerDone, upperDone⟩ := value.recovery (value.waiting_mode waiting)
  obtain ⟨ackNone, retryDone⟩ := value.waiting waiting
  obtain ⟨debt⟩ := value.debt part head rest selected
  exact debt.waiting_cause lowerDone upperDone retryDone ackNone

theorem Active.waiting_credit {core : Core initial native quantum allowance current monitor sent received}
    (value : Active core) (waiting : monitor.waiting = true)
    (part : S.Part) (head : Recovery.Outstanding) (rest : List Recovery.Outstanding)
    (selected : CampusTCPTwoProgressRetry.HeadRange sent part head rest) : monitor.retries < allowance := by
  obtain ⟨position, chosen⟩ := value.waiting_cause waiting part head rest selected
  exact core.timeout_credit part position chosen

variable {first : S.Original initial .lower} {actual : Step input}

def Active.ofBoth {before : CampusTCPTwoProgressPreparation.PendingUpper initial native quantum allowance current monitor first}
    (value : CampusTCPTwoProgressPreparation.Both before actual)
    (sources : CampusTCPTwoProgressReceiptSources.History initial current) : Active value.value.next := by
  have lower : OriginalLane initial native value.value.value.facts.move.after value.value.next.live.gatewayState .empty .lower
      (CampusTCPTwoProgressMonitor.observe (CampusTCPTwoProgressSetup.config initial native quantum allowance) monitor actual).lower := by
    cases value.lowerPath with
    | ingress path produced =>
      exact .active (.ingress path ((SelectedOutput.ofIssued value.value.next.originals.1).reindex produced.symm)) (by intro impossible; cases impossible)
    | lost phase _ _ _ _ _ => exact .done phase
  have upper : OriginalLane initial native value.value.value.facts.move.after value.value.next.live.gatewayState .empty .upper
      (CampusTCPTwoProgressMonitor.observe (CampusTCPTwoProgressSetup.config initial native quantum allowance) monitor actual).upper :=
    .active (.ingress value.value.path (CampusTCPTwoProgressPhaseSources.second_source value.value)) (by intro impossible; cases impossible)
  refine {
    mode := Or.inl value.mode
    preparing := rfl
    nonempty := by simp only [CampusTCPTwoProgressSender.Stage.ledger, ne_eq, List.cons_ne_nil, not_false_eq_true]
    lowerLane := lower, upperLane := upper
    retry := .done value.retry
    ack := ?_
    originals := fun _ => ⟨value.retry, value.waiting, value.retries⟩
    recovery := ?_
    recoveryHead := by
      intro mode
      rw [value.mode] at mode
      cases mode
    serial := ?_
    ackNonempty := ?_
    ackGateway := by
      intro lane pending _
      rw [value.ack] at pending
      cases pending
    waiting := ?_
    runnable := ?_
    originalOpen := ?_
    debt := ?_
    upperMissing := ?_
    zeroAck := ?_
    sources := sources.non_delivery value.value.value.facts.move (by rw [value.value.value.facts.event]; trivial) }
  · unfold AckState
    rw [value.ack]
    exact PUnit.unit
  · intro mode
    rw [value.mode] at mode
    cases mode
  · intro pending
    rw [value.ack] at pending
    cases pending
  · intro pending
    rw [value.ack] at pending
    cases pending
  · intro waiting
    rw [value.waiting] at waiting
    cases waiting
  · intro mode
    rw [value.mode] at mode
    cases mode
  · intro _ _ both
    have phase := value.value.path.phase.symm.trans both.2
    cases phase
  · intro part head rest selected
    cases selected
    exact ⟨CampusTCPTwoProgressPhaseDebt.after_originals_lower value⟩
  · intro _ _ done
    have phase := value.value.path.phase.symm.trans done
    cases phase
  · intro lane ack
    rw [value.ack] at ack
    cases ack

end Netlib.Check.CampusTCPTwoProgressPhaseState
