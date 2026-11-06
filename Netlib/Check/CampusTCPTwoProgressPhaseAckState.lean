import Netlib.Check.CampusTCPTwoProgressPhaseState
import Netlib.Check.CampusTCPTwoProgressPhaseAckSend
import Netlib.Check.CampusTCPTwoProgressPathRetain
import Netlib.Check.CampusTCPTwoProgressGatewayRanges

/-!
# Joint packet state through actual ACK output

The output retains every other current path and loss cause.
The actual receiver queue supplies its response credit.
-/

namespace Netlib.Check.CampusTCPTwoProgressPhaseAckState

open Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart
open CampusTCPTwoProgressPhaseBase (Core)
open CampusTCPTwoProgressPhaseState
open CampusTCPTwoProgressPaths
open CampusTCPTwoProgressPathsReady (rangeAt)

namespace M
export CampusTCPTwoProgressMonitor (Monitor Lane observe)
end M
namespace S
export CampusTCPTwoProgressSender (Stage Part)
end S
namespace R
export CampusTCPTwoProgressReceiver (Stage)
end R
namespace Ack
export CampusTCPTwoProgressPhaseAckSend (AckSent ingressLane)
end Ack
namespace D
export CampusTCPTwoProgressPhaseDebt (Debt Work)
end D
namespace P
export CampusTCPTwoProgressPathRetain (consumedPacket QuietWork)
end P

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current : Cut input complete} {sender : Actor} {gateway : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {native : NativeEnv cut gateway initial.gatewayState.session.entry} {quantum allowance : Nat}
variable {monitor : M.Monitor} {sent : S.Stage initial} {received : R.Stage}
variable {core : Core initial native quantum allowance current monitor sent received} {lane : M.Lane} {actual : Step input}

private theorem original_sent {part : S.Part} {before : M.Lane}
    (value : OriginalLane initial native current core.live.gatewayState received part before) : before.phase ≠ .needSend := by
  cases value with
  | active work missing =>
    cases work with
    | ingress path _ => rw [path.phase]; decide
    | ticket path _ => rw [path.phase]; decide
    | link path _ _ => rw [path.phase]; decide
  | done phase => rw [phase]; decide

private theorem gateway_frame (value : Ack.AckSent core lane actual) :
    beforeService input value.value.move.after.report.final gateway = beforeService input current.report.final gateway := by
  rw [value.value.move.final, ← value.value.facts.beforeEq]
  exact CampusTCPRoundLocal.step_service_nonservice actual (by rw [value.value.facts.event]; trivial) gateway

private theorem sender_recovery (value : Ack.AckSent core lane actual) :
    value.next.live.senderFlight.recovery = core.live.senderFlight.recovery := by
  exact Option.some.inj (value.next.live.senderFlight.runtime.symm.trans
    ((congrArg (fun state : Endpoint.State => state.recovery) value.value.peer).trans core.live.senderFlight.runtime))

private def work_after {part : S.Part} {before : M.Lane} (value : Ack.AckSent core lane actual)
    (work : D.Work initial native current part before) : D.Work initial native value.value.move.after part before := by
  cases work with
  | ingress path => exact .ingress (path.after_move value.value.move (by rw [value.value.facts.event]; intro impossible; cases impossible))
  | ticket path => exact .ticket (path.after_quiet value.value.move (by rw [value.value.facts.event]; trivial))
  | link path => exact .link (path.after_move value.value.move (by rw [value.value.facts.event]; intro impossible; cases impossible))

private def data_after {part : S.Part} {before : M.Lane} (value : Ack.AckSent core lane actual)
    (work : DataWork initial native current core.live.gatewayState part before) :
    DataWork initial native value.value.move.after value.next.live.gatewayState part before := by
  cases work with
  | ingress path source =>
    exact .ingress (path.after_move value.value.move (by rw [value.value.facts.event]; intro impossible; cases impossible))
      (source.retain_steps value.value.move.retained)
  | ticket path source =>
    exact .ticket (path.after_quiet value.value.move (by rw [value.value.facts.event]; trivial))
      (source.retain_steps value.value.move.retained)
  | link path source covered =>
    have ranges := core.live.gatewayState.ranges_same value.next.live.gatewayState (gateway_frame value)
    have kept : (rangeAt value.next.live.gatewayState part).isSome = true := by
      cases part
      · change value.next.live.gatewayState.ranges.lowerRun.isSome = true
        rw [ranges.1]
        exact covered
      · change value.next.live.gatewayState.ranges.upperRun.isSome = true
        rw [ranges.2]
        exact covered
    exact .link (path.after_move value.value.move (by rw [value.value.facts.event]; intro impossible; cases impossible))
      (source.retain_steps value.value.move.retained) kept

private def original_after {part : S.Part} {before : M.Lane} (value : Ack.AckSent core lane actual)
    (work : OriginalLane initial native current core.live.gatewayState received part before) :
    OriginalLane initial native value.value.move.after value.next.live.gatewayState received part before := by
  cases work with
  | active work missing => exact .active (data_after value work) missing
  | done phase => exact .done phase

private def retry_after (value : Ack.AckSent core lane actual)
    (work : RetryLane initial native current core.live.gatewayState sent monitor.retry) :
    RetryLane initial native value.value.move.after value.next.live.gatewayState sent monitor.retry := by
  cases work with
  | active part head rest selected work => exact .active part head rest selected (data_after value work)
  | done phase => exact .done phase

private def debt_after {part : S.Part} (value : Ack.AckSent core lane actual) (debt : D.Debt core part) : D.Debt value.next part := by
  cases debt with
  | cause position chosen => exact .cause position (by rw [value.book]; exact chosen)
  | lower same work =>
    exact .lower same (by simpa only [value.observed] using work_after value work)
  | upper same work =>
    exact .upper same (by simpa only [value.observed] using work_after value work)
  | retry work =>
    exact .retry (by simpa only [value.observed] using work_after value work)
  | ack prior pending covered =>
    exact .ack (Ack.ingressLane lane current.report.final.outputs.length value.packetID) (by rw [value.observed]) covered

def after_send (active : Active core) (value : Ack.AckSent core lane actual) (selected : monitor.ack = some lane) :
    Active value.next := by
  have serial := active.serial (by rw [selected]; rfl)
  have waiting : monitor.waiting = false := by
    cases equal : monitor.waiting
    · rfl
    · have absent := (active.waiting equal).1
      rw [selected] at absent
      cases absent
  exact {
    mode := by simpa only [value.observed] using active.mode
    preparing := active.preparing
    nonempty := active.nonempty
    lowerLane := by simpa only [value.observed] using original_after value active.lowerLane
    upperLane := by simpa only [value.observed] using original_after value active.upperLane
    retry := by simpa only [value.observed] using retry_after value active.retry
    ack := by
      unfold AckState
      rw [show (M.observe (CampusTCPTwoProgressSetup.config initial native quantum allowance) monitor actual).ack =
        some (Ack.ingressLane lane current.report.final.outputs.length value.packetID) from congrArg (fun state => state.ack) value.observed]
      exact .ingress value.path
    originals := by intro mode; simpa only [value.observed] using active.originals (by simpa only [value.observed] using mode)
    recovery := by intro mode; simpa only [value.observed] using active.recovery (by simpa only [value.observed] using mode)
    recoveryHead := by
      intro mode nonwaiting part head rest chosen
      exact active.recoveryHead (by simpa only [value.observed] using mode)
        (by simpa only [value.observed] using nonwaiting) part head rest chosen
    serial := by intro _; simpa only [value.observed] using serial
    waiting := by intro pending; rw [value.observed, waiting] at pending; cases pending
    runnable := by intro _ _ absent; rw [value.observed] at absent; cases absent
    originalOpen := by intro _ absent; rw [value.observed] at absent; cases absent
    debt := by
      intro part head rest selected
      obtain ⟨debt⟩ := active.debt part head rest selected
      exact ⟨debt_after value debt⟩
    zeroAck := by
      intro nextLane _ coordinate
      rw [sender_recovery value]
      exact active.zeroAck lane selected coordinate
    ackNonempty := fun _ => active.ackNonempty (by rw [selected]; rfl)
    ackGateway := by
      intro nextLane pending phase
      rw [value.observed] at pending
      have impossible := (congrArg (fun state => state.phase) (Option.some.inj pending)).trans phase
      cases impossible
    upperMissing := by
      intro zero missing done
      obtain ⟨position, chosen⟩ := active.upperMissing zero missing (by simpa only [value.observed] using done)
      exact ⟨position, by rw [value.book]; exact chosen⟩
    sources := active.sources.non_delivery value.value.move (by rw [value.value.facts.event]; trivial) }

structure Sent (active : Active core) (lane : M.Lane) (actual : Step input) where
  value : Ack.AckSent core lane actual
  next : Active value.next

theorem send_at (active : Active core) (selected : monitor.ack = some lane) (phase : lane.phase = .needAck) :
    ∃ actual, Nonempty (Sent active lane actual) := by
  have work : AckWork core lane := by simpa only [AckState, selected] using active.ack
  have pending : core.live.receiverFacts.reaction.work.pending ≠ [] := by
    cases work with
    | pending _ queue => exact queue
    | ingress path => have impossible := path.phase.symm.trans phase; cases impossible
    | ticket path => have impossible := path.phase.symm.trans phase; cases impossible
    | link path => have impossible := path.phase.symm.trans phase; cases impossible
  obtain ⟨actual, ⟨value⟩⟩ := CampusTCPTwoProgressPhaseAckSend.ack_at core active.mode
    (original_sent active.lowerLane) (original_sent active.upperLane) selected phase pending
  exact ⟨actual, ⟨⟨value, after_send active value selected⟩⟩⟩

end Netlib.Check.CampusTCPTwoProgressPhaseAckState
