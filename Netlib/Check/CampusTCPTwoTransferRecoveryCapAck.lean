import Netlib.Check.CampusTCPTwoTransferHandoffRTO
import Netlib.Check.CampusTCPTwoTransferAckRetire

/-!
# Fixed pending cap through the actual ACK receipt

Only lower retirement can leave another sender record.
In recovery, that actual retired head has already been retried.
-/

namespace Netlib.Check.CampusTCPTwoTransferRecoveryCap

open Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart
open CampusTCPTwoTransferNative (Checks Routing)
open CampusTCPTwoTransferLocatedCore (Core config)
open CampusTCPTwoTransferPhaseState (Active)
open CampusTCPTwoTransferHandoffRTO (PendingCap at_core of_core same_core)

namespace W
export CampusTCPTwoTransferMonitor (Monitor observe)
end W
namespace S
export CampusTCPTwoProgressSender (Stage Retires)
end S
namespace R
export CampusTCPTwoProgressReceiver (Stage)
end R
namespace A
export CampusTCPTwoTransferAckReceiveCore (Advanced Zero)
end A

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current : Cut input complete} {sender : Actor} {gateway location : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {checks : Checks cut initial.gatewayState.session.entry} {routing : Routing cut gateway}
variable {quantum allowance capacity : Nat} {reverseLower reverseUpper : List UInt8}
variable {monitor : W.Monitor} {sent next : S.Stage initial} {received : R.Stage}
variable {lane : CampusTCPTwoProgressMonitor.Lane}
variable {core : Core initial checks routing quantum allowance reverseLower reverseUpper current monitor location sent received}
variable {path : CampusTCPTwoProgressPaths.AckLink initial current (received.bytes lower upper).length lane}

local notation "cfg" => config initial checks routing quantum allowance reverseLower reverseUpper

theorem advanced_runtime (value : A.Advanced core path) :
    value.nextCore.live.senderFlight.recovery = Endpoint.advancingAckRecovery (endpoint current.endpoints sender)
      path.emission.asInput core.live.senderFlight.recovery := by
  have other : path.served.ticket.value.produced.actor.other = sender := by rw [path.actor]; cases sender <;> rfl
  have selected : endpoint value.value.delivery.move.after.endpoints sender = value.value.delivery.after := by
    change endpoint value.value.delivery.updated sender = value.value.delivery.after
    simpa only [other] using value.value.delivery.selected
  apply Option.some.inj
  exact value.nextCore.live.senderFlight.runtime.symm.trans (by rw [selected]; exact value.value.protocol.runtime)

private theorem retirement_fields (core : Core initial checks routing quantum allowance reverseLower reverseUpper current monitor location sent received)
    (retiring : S.Retires sent amount next) {packet : Endpoint.Input} {after : Endpoint.State}
    (protocol : Endpoint.AdvancingAck (endpoint current.endpoints sender) packet core.live.senderFlight.recovery after)
    (counted : Endpoint.inOrderCount (endpoint current.endpoints sender) packet = amount)
    (retried : ∀ part head rest, CampusTCPTwoProgressRetry.HeadRange sent part head rest → head.retried = true)
    (pending : next.ledger ≠ []) :
    let recovery := Endpoint.advancingAckRecovery (endpoint current.endpoints sender) packet core.live.senderFlight.recovery
    recovery.estimator = core.live.senderFlight.recovery.estimator ∧
      recovery.lastSample = core.live.senderFlight.recovery.lastSample ∧ recovery.rto = core.live.senderFlight.recovery.rto := by
  cases retiring with
  | lower first second head =>
    have size := congrArg Recovery.Outstanding.count core.live.senderFlight.headFixed
    have countedHead : Endpoint.inOrderCount (endpoint current.endpoints sender) packet = head.count := counted.trans size.symm
    exact protocol.head_retried head [second.entry] core.live.senderFlight.ledger countedHead
      (retried .lower head [second.entry] (.lower first second head))
  | both => exact False.elim (pending rfl)
  | tail => exact False.elim (pending rfl)

theorem pending_fields (active : Active core) (value : A.Advanced core path)
    (nonoriginal : monitor.exchange.forward.mode ≠ .originals) (selected : monitor.exchange.forward.ack = some lane)
    (pending : value.nextStage.ledger ≠ []) :
    value.nextCore.live.senderFlight.recovery.estimator = core.live.senderFlight.recovery.estimator ∧
      value.nextCore.live.senderFlight.recovery.lastSample = core.live.senderFlight.recovery.lastSample ∧
      value.nextCore.live.senderFlight.recovery.rto = core.live.senderFlight.recovery.rto := by
  have mode : monitor.exchange.forward.mode = .recovery := active.mode.resolve_left nonoriginal
  have waiting : monitor.exchange.forward.waiting = false := by
    cases equal : monitor.exchange.forward.waiting
    · rfl
    · have absent := (active.waiting equal).1
      rw [selected] at absent
      cases absent
  rw [advanced_runtime value]
  exact retirement_fields core value.value.retiring value.value.protocol value.value.counted
    (active.recoveryHead mode waiting) pending

theorem advanced_cap (active : Active core) (value : A.Advanced core path)
    (nonoriginal : monitor.exchange.forward.mode ≠ .originals) (selected : monitor.exchange.forward.ack = some lane)
    (prior : PendingCap cfg capacity current.report.final monitor) :
    PendingCap cfg capacity value.value.delivery.move.after.report.final (W.observe cfg monitor value.value.delivery.step) := by
  apply of_core value.nextCore
  intro pending
  rw [(pending_fields active value nonoriginal selected pending).2.2, value.observation.retries]
  exact at_core core prior active.nonempty

theorem zero_runtime (value : A.Zero core path) :
    value.nextCore.live.senderFlight.recovery = Endpoint.zeroAckRecovery (endpoint current.endpoints sender)
      path.emission.asInput core.live.senderFlight.recovery := by
  have other : path.served.ticket.value.produced.actor.other = sender := by rw [path.actor]; cases sender <;> rfl
  have selected : endpoint value.value.delivery.move.after.endpoints sender = value.value.delivery.after := by
    change endpoint value.value.delivery.updated sender = value.value.delivery.after
    simpa only [other] using value.value.delivery.selected
  apply Option.some.inj
  exact value.nextCore.live.senderFlight.runtime.symm.trans (by rw [selected]; exact value.value.protocol.runtime)

theorem zero_cap (value : A.Zero core path) (prior : PendingCap cfg capacity current.report.final monitor) :
    PendingCap cfg capacity value.value.delivery.move.after.report.final (W.observe cfg monitor value.value.delivery.step) := by
  apply same_core core value.nextCore prior
  · rw [zero_runtime value]
    unfold Endpoint.zeroAckRecovery
    split <;> rfl
  · exact fun pending => pending
  · exact value.observation.retries

theorem received_cap (active : Active core)
    (value : CampusTCPTwoTransferAckRetire.Received active path)
    (nonoriginal : monitor.exchange.forward.mode ≠ .originals) (selected : monitor.exchange.forward.ack = some lane)
    (prior : PendingCap cfg capacity current.report.final monitor) :
    PendingCap cfg capacity value.move.after.report.final (W.observe cfg monitor value.actual) := by
  cases value with
  | zero value => exact zero_cap value.value prior
  | advanced value => exact advanced_cap active value.value nonoriginal selected prior

end Netlib.Check.CampusTCPTwoTransferRecoveryCap
