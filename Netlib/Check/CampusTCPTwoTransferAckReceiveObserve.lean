import Netlib.Check.CampusTCPTwoTransferLocatedAckReceive
import Netlib.Check.CampusTCPTwoTransferServiceObserve
import Netlib.Check.CampusTCPTwoTransferPhaseState
import Netlib.Check.CampusTCPTwoTransferOrdinaryPhase

/-!
# Exact observation of the actual ACK receipt

The stored receipt clears the selected ACK lane.
Normalization reads the same resulting sender recovery state.
-/

namespace Netlib.Check.CampusTCPTwoTransferAckReceiveObserve

open Protocol Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart
open CampusTCPTwoTransferNative (Checks Routing)
open CampusTCPTwoTransferLocatedCore (Core config)
open CampusTCPTwoTransferState (LiveAt)
open CampusTCPTwoTransferPaths (AckLink)
open CampusTCPTwoTransferPhaseState (Active)
open CampusTCPTwoTransferServiceObserve (afterService)

namespace W
export CampusTCPTwoTransferMonitor (Monitor Allowed observe controlDemand drainTicket)
end W
namespace M
export CampusTCPTwoProgressMonitor (Monitor Lane observe normalize)
end M
namespace F
export CampusTCPTwoProgressMonitorFacts (observe_action observe_ack phase_beq_self normalize_counters mode_beq)
end F
namespace A
export CampusTCPTwoTransferLocatedAckReceive (Advanced Zero)
end A

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current : Cut input complete} {sender : Actor} {gateway location : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {checks : Checks cut initial.gatewayState.session.entry} {routing : Routing cut gateway}
variable {quantum allowance : Nat} {reverseLower reverseUpper : List UInt8}
variable {monitor : W.Monitor} {sent next : CampusTCPTwoProgressSender.Stage initial}
variable {received : CampusTCPTwoProgressReceiver.Stage} {amount : Nat} {lane : M.Lane}
variable {core : Core initial checks routing quantum allowance reverseLower reverseUpper current monitor location sent received}

local notation "cfg" => config initial checks routing quantum allowance reverseLower reverseUpper
local notation "localCfg" => CampusTCPTwoExchangeMonitor.Config.forward
  (CampusTCPTwoTransferMonitor.Config.at
    (config initial checks routing quantum allowance reverseLower reverseUpper) current.report.final)


def ackCleared (monitor : M.Monitor) (index : Nat) : M.Monitor :=
  { monitor with ack := none, ackReceipts := monitor.ackReceipts ++ [index] }


theorem ordinary_delivery (allowed : W.Allowed cfg current.report.final monitor (.deliver index bytes true)) :
    W.drainTicket current.report.final monitor = none ∧ W.controlDemand monitor = none := by
  by_cases invalid : monitor.mode = .invalid
  · simp only [W.Allowed, CampusTCPTwoTransferMonitor.allowed, invalid, decide_true, ite_true, Bool.false_eq_true] at allowed
  · cases drain : W.drainTicket current.report.final monitor with
    | some ticket => simp [W.Allowed, CampusTCPTwoTransferMonitor.allowed, invalid, drain,
        CampusTCPTwoTransferMonitor.drainServes] at allowed
    | none =>
      cases selected : W.controlDemand monitor with
      | none => exact ⟨rfl, rfl⟩
      | some kind => cases kind <;> simp [W.Allowed, CampusTCPTwoTransferMonitor.allowed, invalid, drain, selected,
          CampusTCPTwoTransferMonitor.Control.serves] at allowed

private theorem local_observed (active : Active core)
    (path : AckLink initial current count lane)
    (delivery : CampusTCPRoundDelivery.Delivery current.report complete current.endpoints path.index path.served path.emission path.emitted)
    (selected : monitor.exchange.forward.ack = some lane)
    (allowed : CampusTCPTwoProgressMonitor.Allowed localCfg current.report.final monitor.exchange.forward
      (.deliver path.index path.emission.bytes true)) :
    M.observe localCfg monitor.exchange.forward delivery.step = M.normalize localCfg delivery.step.result.state
      (ackCleared monitor.exchange.forward current.report.final.receipts.length) := by
  have other : path.served.ticket.value.produced.actor.other = sender := by rw [path.actor]; cases sender <;> rfl
  have receiptActor : delivery.receipt.actor = sender := by rw [delivery.receipt.receiver, delivery.receiptService, other]
  have self : (sender == sender) = true := by cases sender <;> rfl
  have cfgSender : (localCfg).sender = sender := rfl
  rw [F.observe_action _ _ _ delivery.supported delivery.passed
    (by simpa only [delivery.beforeEq, delivery.event] using allowed)
    (.deliver path.index path.emission.bytes true) delivery.event,
    F.observe_ack _ _ _ _ active.mode active.lower_not_needSend active.upper_not_needSend selected]
  simp only [CampusTCPTwoProgressMonitor.observeAck, CampusTCPTwoProgressMonitor.ackLane, path.phase,
    CampusTCPGapProgressMonitor.observeReceipt, delivery.receiptAt, delivery.recorded, other, receiptActor,
    cfgSender, CampusTCPTwoProgressMonitor.Lane.toGap, CampusTCPTwoProgressMonitor.Lane.ofGap,
    Bool.false_eq_true, ite_false, self, Bool.and_self, ite_true, F.phase_beq_self, delivery.beforeEq]
  rfl

private theorem normalize_modes (state : State input) (raw : M.Monitor) (recovery : Recovery.State)
    (runtime : CampusTCPGapProgressMonitor.senderRecovery (localCfg).toConfig state = some recovery)
    (mode : raw.mode = .originals ∨ raw.mode = .recovery) :
    (M.normalize localCfg state raw).mode ≠ .invalid ∧ (M.normalize localCfg state raw).mode ≠ .done := by
  rcases mode with mode | mode
  all_goals
    simp only [M.normalize, mode, runtime]
    split
    · split <;> simp only [ne_eq, reduceCtorEq, not_false_eq_true, and_self]
    · simp only [mode, ne_eq, reduceCtorEq, not_false_eq_true, and_self]

structure Observed (core : Core initial checks routing quantum allowance reverseLower reverseUpper current monitor location sent received)
    (path : AckLink initial current count lane)
    (delivery : CampusTCPRoundDelivery.Delivery current.report complete current.endpoints path.index path.served path.emission path.emitted) : Prop where
  observed : W.observe cfg monitor delivery.step = afterService monitor
    (M.normalize localCfg delivery.step.result.state (ackCleared monitor.exchange.forward current.report.final.receipts.length))
  healthy : (W.observe cfg monitor delivery.step).mode ≠ .invalid
  retries : (W.observe cfg monitor delivery.step).exchange.forward.retries = monitor.exchange.forward.retries
  drops : (W.observe cfg monitor delivery.step).exchange.forward.drops = monitor.exchange.forward.drops
  wholeDrops : (W.observe cfg monitor delivery.step).exchange.drops = monitor.exchange.drops
  timeouts : (W.observe cfg monitor delivery.step).exchange.timeouts = monitor.exchange.timeouts

private theorem finish (core : Core initial checks routing quantum allowance reverseLower reverseUpper current monitor location sent received)
    (active : Active core) (path : AckLink initial current count lane)
    (delivery : CampusTCPRoundDelivery.Delivery current.report complete current.endpoints path.index path.served path.emission path.emitted)
    (selected : monitor.exchange.forward.ack = some lane)
    (ordinary : monitor.mode = .armed ∨ monitor.mode = .finished) (control : W.controlDemand monitor = none)
    (allowed : W.Allowed cfg current.report.final monitor (.deliver path.index path.emission.bytes true))
    (recovery : Recovery.State)
    (runtime : CampusTCPGapProgressMonitor.senderRecovery (localCfg).toConfig delivery.step.result.state = some recovery) :
    Observed core path delivery := by
  have localAllowed := CampusTCPTwoTransferServiceObserve.local_allowed ordinary control active.exchange allowed
  have localObserved := local_observed active path delivery selected localAllowed
  have modes := normalize_modes delivery.step.result.state (ackCleared monitor.exchange.forward current.report.final.receipts.length)
    recovery runtime active.mode
  have allowedActual : W.Allowed cfg current.report.final monitor delivery.step.event := by rw [delivery.event]; exact allowed
  have checked : (delivery.step.result.supported && delivery.step.result.passed &&
      CampusTCPTwoTransferMonitor.allowed cfg delivery.step.before monitor delivery.step.event) = true := by
    rw [delivery.supported, delivery.passed, delivery.beforeEq]
    exact allowedActual
  have innerChecked : (delivery.step.result.supported && delivery.step.result.passed &&
      CampusTCPTwoExchangeMonitor.allowed ((cfg).at delivery.step.before) delivery.step.before monitor.exchange delivery.step.event) = true := by
    rw [delivery.supported, delivery.passed]
    simpa only [Bool.true_and, CampusTCPTwoExchangeMonitor.allowed, active.exchange, delivery.beforeEq,
      delivery.event, CampusTCPTwoProgressMonitor.Allowed] using localAllowed
  have observed : W.observe cfg monitor delivery.step = afterService monitor
      (M.normalize localCfg delivery.step.result.state (ackCleared monitor.exchange.forward current.report.final.receipts.length)) := by
    obtain ⟨drainless, _⟩ := ordinary_delivery allowed
    rw [W.observe, ite_eq_left checked, delivery.beforeEq, drainless, control]
    unfold CampusTCPTwoTransferMonitor.ordinary
    rw [CampusTCPTwoExchangeMonitor.observe, ite_eq_left innerChecked, active.exchange]
    have sameConfig : ((cfg).at delivery.step.before).forward = localCfg := by rw [delivery.beforeEq]
    rw [sameConfig, localObserved]
    simp only [F.mode_beq, modes.1, modes.2, decide_false, Bool.false_eq_true, ite_false]
    change (if decide (monitor.exchange.mode = .invalid) then _ else _) = _
    rw [active.exchange]
    simp only [reduceCtorEq, decide_false, Bool.false_eq_true, ite_false]
    unfold afterService
    congr 2
    · change (match delivery.step.event with | .dropPacket id => monitor.exchange.drops ++ [id] | _ => monitor.exchange.drops) = _
      rw [delivery.event]
    · change (match delivery.step.event with | .timeout _ true => monitor.exchange.timeouts + 1 | _ => monitor.exchange.timeouts) = _
      rw [delivery.event]
  refine ⟨observed, ?_, ?_, ?_, ?_, ?_⟩
  · rw [observed]
    exact CampusTCPTwoTransferServiceObserve.afterService_healthy ordinary _
  · rw [observed]
    exact congrArg Prod.fst (F.normalize_counters localCfg delivery.step.result.state _)
  · rw [observed]
    exact congrArg Prod.snd (F.normalize_counters localCfg delivery.step.result.state _)
  · rw [observed]; rfl
  · rw [observed]; rfl


theorem advancing (core : Core initial checks routing quantum allowance reverseLower reverseUpper current monitor location sent received)
    (active : Active core) (path : AckLink initial current (received.bytes lower upper).length lane)
    (value : A.Advanced core.live next amount path.index path.served path.emission path.emitted)
    (controls : CampusTCPTwoTransferControlState.Phase current.report.final monitor.mode location)
    (selected : monitor.exchange.forward.ack = some lane)
    (allowed : W.Allowed cfg current.report.final monitor (.deliver path.index path.emission.bytes true)) :
    Observed core path value.delivery.toDelivery := by
  have ordinary := controls.ordinary_modes (ordinary_delivery allowed).2
  apply finish core active path value.delivery.toDelivery selected ordinary (ordinary_delivery allowed).2 allowed
    value.joint.senderFlight.recovery
  have cfgSender : (localCfg).sender = sender := rfl
  rw [← value.delivery.move.final]
  simp only [CampusTCPGapProgressMonitor.senderRecovery, value.delivery.move.after.connection, cfgSender, value.joint.senderFlight.runtime]


theorem zero (core : Core initial checks routing quantum allowance reverseLower reverseUpper current monitor location sent received)
    (active : Active core) (path : AckLink initial current (received.bytes lower upper).length lane)
    (value : A.Zero core.live path.index path.served path.emission path.emitted)
    (controls : CampusTCPTwoTransferControlState.Phase current.report.final monitor.mode location)
    (selected : monitor.exchange.forward.ack = some lane)
    (allowed : W.Allowed cfg current.report.final monitor (.deliver path.index path.emission.bytes true)) :
    Observed core path value.delivery.toDelivery := by
  have ordinary := controls.ordinary_modes (ordinary_delivery allowed).2
  apply finish core active path value.delivery.toDelivery selected ordinary (ordinary_delivery allowed).2 allowed
    value.joint.senderFlight.recovery
  have cfgSender : (localCfg).sender = sender := rfl
  rw [← value.delivery.move.final]
  simp only [CampusTCPGapProgressMonitor.senderRecovery, value.delivery.move.after.connection, cfgSender, value.joint.senderFlight.runtime]

end Netlib.Check.CampusTCPTwoTransferAckReceiveObserve
