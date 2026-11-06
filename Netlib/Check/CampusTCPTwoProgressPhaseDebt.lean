import Netlib.Check.CampusTCPTwoProgressPhaseRetry
import Netlib.Check.CampusTCPTwoProgressPathDrop
import Netlib.Check.CampusTCPTwoProgressPreparation

/-!
# Current work or an unspent loss for each head

A pending path or ACK can explain an outstanding head.
When all paths are done, an actual recorded loss must remain.
-/

namespace Netlib.Check.CampusTCPTwoProgressPhaseDebt

open Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart
open CampusTCPTwoProgressPhaseBase (Core)
open CampusTCPTwoProgressPaths

namespace S
export CampusTCPTwoProgressSender (Part Stage Original)
end S
namespace M
export CampusTCPTwoProgressMonitor (Monitor Lane)
end M

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current next : Cut input complete} {sender : Actor} {gateway : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {native : NativeEnv cut gateway initial.gatewayState.session.entry} {quantum allowance : Nat}
variable {monitor : M.Monitor} {sent : S.Stage initial} {received : CampusTCPTwoProgressReceiver.Stage}
variable {part : S.Part} {lane : M.Lane}

inductive Work (initial : TwoWriteInitial cut sender gateway lower upper)
    (native : NativeEnv cut gateway initial.gatewayState.session.entry) (current : Cut input complete)
    (part : S.Part) (lane : M.Lane) where
  | ingress (path : DataIngress initial current part lane)
  | ticket (path : DataTicket initial native current part lane)
  | link (path : DataLink initial current part lane)

theorem Work.not_done (work : Work initial native current part lane) : lane.phase ≠ .done := by
  cases work with
  | ingress path => rw [path.phase]; decide
  | ticket path => rw [path.phase]; decide
  | link path => rw [path.phase]; decide

def Work.clock (work : Work initial native current part lane)
    (placement : CampusTCPRecoveryRoundPhaseBase.At current next) : Work initial native next part lane := by
  cases work with
  | ingress path => exact .ingress (path.clock placement)
  | ticket path => exact .ticket (path.clock placement)
  | link path => exact .link (path.clock placement)

inductive Debt (core : Core initial native quantum allowance current monitor sent received) (role : S.Part) where
  | cause (position : Nat) (chosen : core.losses.book.cause role = some position)
  | lower (same : role = .lower) (work : Work initial native current .lower monitor.lower)
  | upper (same : role = .upper) (work : Work initial native current .upper monitor.upper)
  | retry (work : Work initial native current role monitor.retry)
  | ack (lane : M.Lane) (pending : monitor.ack = some lane)
      (covered : role.offset lower + (role.bytes lower upper).length ≤ (received.bytes lower upper).length)

variable {core : Core initial native quantum allowance current monitor sent received}

def Debt.clock (debt : Debt core part) {actor : Actor} {millis : Nat} {actual : Step input}
    (clocked : CampusTCPTwoProgressClock.Clocked cut current
      (CampusTCPTwoProgressSetup.config initial native quantum allowance) monitor actor millis actual)
    (allowed : CampusTCPTwoProgressMonitor.Allowed (CampusTCPTwoProgressSetup.config initial native quantum allowance)
      current.report.final monitor (.advanceClock actor millis)) : Debt (core.clock clocked allowed) part := by
  cases debt with
  | cause position chosen => exact .cause position chosen
  | lower same work => exact .lower same (work.clock clocked.placement)
  | upper same work => exact .upper same (work.clock clocked.placement)
  | retry work => exact .retry (work.clock clocked.placement)
  | ack lane pending covered => exact .ack lane pending covered

def after_drop {produced : Produced input.active input.passive} {packetID : Nat}
    {target : CampusTCPTwoProgressMonitor.DropTarget} {actual : Step input}
    {drop : CampusTCPTwoProgressPathDrop.Dropped core produced packetID target actual}
    (credited : CampusTCPTwoProgressPathDrop.Credited drop part) : Debt credited.result.next part := by
  apply Debt.cause core.losses.book.losses.length
  rw [credited.result.bookEq]
  cases part <;> rfl

def after_timeout {head : Recovery.Outstanding} {rest : List Recovery.Outstanding} {position : Nat} {actual : Step input}
    (retried : CampusTCPTwoProgressPhaseRetry.Retried core part head rest position actual) : Debt retried.next part :=
  .retry (.ingress retried.path)

def after_originals_lower {first : S.Original initial .lower}
    {before : CampusTCPTwoProgressPreparation.PendingUpper initial native quantum allowance current monitor first}
    {actual : Step input} (value : CampusTCPTwoProgressPreparation.Both before actual) : Debt value.value.next .lower := by
  cases value.lowerPath with
  | ingress path _ => exact .lower rfl (.ingress path)
  | lost _ position _ _ _ chosen => exact .cause position chosen

def after_originals_upper {first : S.Original initial .lower}
    {before : CampusTCPTwoProgressPreparation.PendingUpper initial native quantum allowance current monitor first}
    {actual : Step input} (value : CampusTCPTwoProgressPreparation.Both before actual) : Debt value.value.next .upper :=
  .upper rfl (.ingress value.value.path)

theorem Debt.waiting_cause (debt : Debt core part)
    (lowerDone : monitor.lower.phase = .done) (upperDone : monitor.upper.phase = .done)
    (retryDone : monitor.retry.phase = .done) (ackNone : monitor.ack = none) :
    ∃ position, core.losses.book.cause part = some position := by
  cases debt with
  | cause position chosen => exact ⟨position, chosen⟩
  | lower _ work => exact False.elim (work.not_done lowerDone)
  | upper _ work => exact False.elim (work.not_done upperDone)
  | retry work => exact False.elim (work.not_done retryDone)
  | ack lane pending _ => rw [ackNone] at pending; cases pending

theorem Debt.waiting_credit (debt : Debt core part)
    (lowerDone : monitor.lower.phase = .done) (upperDone : monitor.upper.phase = .done)
    (retryDone : monitor.retry.phase = .done) (ackNone : monitor.ack = none) : monitor.retries < allowance := by
  obtain ⟨position, chosen⟩ := debt.waiting_cause lowerDone upperDone retryDone ackNone
  exact core.timeout_credit part position chosen

variable {first : S.Original initial .lower} {second : S.Original initial .upper} {head : Recovery.Outstanding} {target : Nat}

theorem lower_at (core : Core initial native quantum allowance current monitor (.both first second head) received)
    (debt : Debt core .lower) (mode : monitor.mode = .recovery) (ackNone : monitor.ack = none)
    (waiting : monitor.waiting = true) (lowerDone : monitor.lower.phase = .done) (upperDone : monitor.upper.phase = .done)
    (retryDone : monitor.retry.phase = .done) (budget : allowance ≤ 2)
    (timer : CampusTCPTwoProgressMonitor.timerTarget core.live.senderFlight.recovery = some target)
    (due : target ≤ core.live.senderFlight.recovery.now) :
    ∃ actual position, Nonempty (CampusTCPTwoProgressPhaseRetry.Retried core .lower head [second.entry] position actual) := by
  obtain ⟨position, chosen⟩ := debt.waiting_cause lowerDone upperDone retryDone ackNone
  obtain ⟨actual, result⟩ := CampusTCPTwoProgressPhaseRetry.lower_at core mode ackNone waiting budget chosen timer due
  exact ⟨actual, position, result⟩

theorem upper_at (core : Core initial native quantum allowance current monitor (.tail first second head) received)
    (debt : Debt core .upper) (mode : monitor.mode = .recovery) (ackNone : monitor.ack = none)
    (waiting : monitor.waiting = true) (lowerDone : monitor.lower.phase = .done) (upperDone : monitor.upper.phase = .done)
    (retryDone : monitor.retry.phase = .done) (budget : allowance ≤ 2)
    (timer : CampusTCPTwoProgressMonitor.timerTarget core.live.senderFlight.recovery = some target)
    (due : target ≤ core.live.senderFlight.recovery.now) :
    ∃ actual position, Nonempty (CampusTCPTwoProgressPhaseRetry.Retried core .upper head [] position actual) := by
  obtain ⟨position, chosen⟩ := debt.waiting_cause lowerDone upperDone retryDone ackNone
  obtain ⟨actual, result⟩ := CampusTCPTwoProgressPhaseRetry.upper_at core mode ackNone waiting budget chosen timer due
  exact ⟨actual, position, result⟩

end Netlib.Check.CampusTCPTwoProgressPhaseDebt
