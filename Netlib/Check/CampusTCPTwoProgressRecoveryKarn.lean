import Netlib.Check.CampusTCPTwoProgressPhaseState
import Netlib.Check.CampusTCPTwoProgressPhaseAckReceive

/-!
# No new RTT sample for a pending recovery head

A pending recovery ACK follows an actual retry of the current head.
The claim applies while retirement leaves another outstanding head.
-/

namespace Netlib.Check.CampusTCPTwoProgressRecoveryKarn

open Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart
open CampusTCPTwoProgressPhaseBase (Core)
open CampusTCPTwoProgressPhaseState (Active)

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current : Cut input complete} {sender : Actor} {gateway : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {native : NativeEnv cut gateway initial.gatewayState.session.entry} {quantum allowance : Nat}
variable {monitor : CampusTCPTwoProgressMonitor.Monitor}
variable {sent next : CampusTCPTwoProgressSender.Stage initial} {received : CampusTCPTwoProgressReceiver.Stage}
variable {core : Core initial native quantum allowance current monitor sent received}
variable {lane : CampusTCPTwoProgressMonitor.Lane}
variable {path : CampusTCPTwoProgressPaths.AckLink initial current (received.bytes lower upper).length lane}

private theorem retirement_fields (core : Core initial native quantum allowance current monitor sent received)
    (retiring : CampusTCPTwoProgressSender.Retires sent amount next) {packet : Endpoint.Input} {after : Endpoint.State}
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

private theorem advanced_runtime (value : CampusTCPTwoProgressPhaseAckReceive.Advanced core path) :
    value.nextCore.live.senderFlight.recovery = Endpoint.advancingAckRecovery (endpoint current.endpoints sender)
      path.emission.asInput core.live.senderFlight.recovery := by
  have other : path.served.ticket.value.produced.actor.other = sender := by rw [path.actor]; cases sender <;> rfl
  have selected : endpoint value.value.delivery.move.after.endpoints sender = value.value.delivery.after := by
    change endpoint value.value.delivery.updated sender = value.value.delivery.after
    simpa only [other] using value.value.delivery.selected
  apply Option.some.inj
  exact value.nextCore.live.senderFlight.runtime.symm.trans (by rw [selected]; exact value.value.protocol.runtime)

theorem pending_fields (active : Active core) (value : CampusTCPTwoProgressPhaseAckReceive.Advanced core path)
    (nonoriginal : monitor.mode ≠ .originals) (selected : monitor.ack = some lane)
    (pending : value.nextStage.ledger ≠ []) :
    value.nextCore.live.senderFlight.recovery.estimator = core.live.senderFlight.recovery.estimator ∧
      value.nextCore.live.senderFlight.recovery.lastSample = core.live.senderFlight.recovery.lastSample ∧
      value.nextCore.live.senderFlight.recovery.rto = core.live.senderFlight.recovery.rto := by
  have mode : monitor.mode = .recovery := active.mode.resolve_left nonoriginal
  have waiting : monitor.waiting = false := by
    cases equal : monitor.waiting
    · rfl
    · have absent := (active.waiting equal).1
      rw [selected] at absent
      cases absent
  rw [advanced_runtime value]
  exact retirement_fields core value.value.retiring value.value.protocol value.value.counted
    (active.recoveryHead mode waiting) pending

theorem pending_rto (active : Active core) (value : CampusTCPTwoProgressPhaseAckReceive.Advanced core path)
    (nonoriginal : monitor.mode ≠ .originals) (selected : monitor.ack = some lane)
    (pending : value.nextStage.ledger ≠ []) :
    value.nextCore.live.senderFlight.recovery.rto = core.live.senderFlight.recovery.rto :=
  (pending_fields active value nonoriginal selected pending).2.2

end Netlib.Check.CampusTCPTwoProgressRecoveryKarn
