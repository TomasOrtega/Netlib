import Netlib.Check.CampusTCPTwoTransferLocatedReceive
import Netlib.Check.CampusTCPTwoTransferLocatedCore
import Netlib.Check.CampusTCPTwoProgressPhaseObserveReceive

/-!
# Exact data receipt observation at the current location

The stored receipt supplies its index, local stamp, and released chunk.
The same whole observer starts the current ACK lane.
-/

namespace Netlib.Check.CampusTCPTwoTransferReceiveObserve

open Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart
open CampusTCPTwoTransferNative (Checks Routing)
open CampusTCPTwoTransferLocatedCore (config)
open CampusTCPTwoTransferState (LiveAt)
open CampusTCPTwoTransferPaths (DataLink)
open CampusTCPTwoTransferLocatedReceive (Delivered)

namespace W
export CampusTCPTwoTransferMonitor (Monitor Allowed observe drainTicket controlDemand)
end W
namespace M
export CampusTCPTwoProgressMonitor (Monitor Lane DropTarget dataLane recordData observeData observeOrdinary laneDemand servesOption)
end M
namespace O
export CampusTCPTwoProgressPhaseObserveReceive (receiptLane receiptUpdate dataLaneAt)
end O
namespace F
export CampusTCPTwoProgressMonitorFacts (observe_action observe_original_lower observe_original_upper)
end F

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current : Cut input complete} {sender : Actor} {gateway location : Gateway} {lower upper chunk : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {checks : Checks cut initial.gatewayState.session.entry} {routing : Routing cut gateway}
variable {quantum allowance : Nat} {reverseLower reverseUpper : List UInt8}
variable {monitor : W.Monitor} {sent : CampusTCPTwoProgressSender.Stage initial} {timeouts : Nat}
variable {beforeStage afterStage : CampusTCPTwoProgressReceiver.Stage} {part : CampusTCPTwoProgressSender.Part} {lane : M.Lane}
variable {live : LiveAt initial current location sent timeouts beforeStage} {path : DataLink initial current part lane}

local notation "cfg" => config initial checks routing quantum allowance reverseLower reverseUpper

theorem allowed_receipt (config : CampusTCPTwoTransferMonitor.Config) (state : State input) (monitor : W.Monitor)
    (index : Nat) (bytes : List UInt8) (allowed : W.Allowed config state monitor (.deliver index bytes true)) :
    W.drainTicket state monitor = none ∧ W.controlDemand monitor = none ∧
      CampusTCPTwoExchangeMonitor.Allowed (config.at state) state monitor.exchange (.deliver index bytes true) := by
  by_cases invalid : monitor.mode = .invalid
  · simp only [W.Allowed, CampusTCPTwoTransferMonitor.allowed, invalid, decide_true, ite_true, Bool.false_eq_true] at allowed
  · cases drain : W.drainTicket state monitor with
    | some ticket => simp [W.Allowed, CampusTCPTwoTransferMonitor.allowed, invalid, drain,
        CampusTCPTwoTransferMonitor.drainServes] at allowed
    | none =>
      cases selected : W.controlDemand monitor with
      | none => exact ⟨rfl, rfl, by simpa only [W.Allowed, CampusTCPTwoTransferMonitor.allowed, invalid,
          decide_false, Bool.false_eq_true, ite_false, drain, selected, CampusTCPTwoExchangeMonitor.Allowed] using allowed⟩
      | some kind => cases kind <;> simp [W.Allowed, CampusTCPTwoTransferMonitor.allowed, invalid, drain, selected,
          CampusTCPTwoTransferMonitor.Control.serves] at allowed

def afterReceipt (monitor : W.Monitor) (target : M.DropTarget) (index stamp : Nat) (chunk : List UInt8) : W.Monitor :=
  { monitor with exchange := { monitor.exchange with
    forward := O.receiptUpdate monitor.exchange.forward target index stamp chunk
    slots := monitor.exchange.slots + 1 } }

theorem data_lane (value : Delivered live path afterStage chunk) :
    M.dataLane ((cfg).at current.report.final).forward lane value.value.delivery.step =
      O.receiptLane lane current.report.final.receipts.length value.value.delivery.localStep.stamp := by
  have receiver : value.value.delivery.receipt.actor = sender.other := by
    rw [value.value.delivery.receipt.receiver, value.value.delivery.receiptService, path.actor]
  have recorded : value.value.delivery.step.result.application = some (sender.other, value.value.delivery.localStep) := by
    simpa only [path.actor] using value.value.delivery.recorded
  simp only [M.dataLane, path.phase, CampusTCPGapProgressMonitor.observeReceipt, value.value.delivery.receiptAt,
    recorded, receiver, value.value.delivery.beforeEq, CampusTCPTwoProgressMonitor.Lane.toGap,
    CampusTCPTwoProgressMonitor.Lane.ofGap, O.receiptLane]
  cases sender <;> rfl

private theorem receipt_frame (localConfig : CampusTCPTwoProgressMonitor.Config) (localMonitor : M.Monitor)
    (actual : Step input) (target : M.DropTarget) (notAck : target ≠ .ack) (operation : ApplicationTrace.Step) (index : Nat)
    (decoded : M.dataLane localConfig (O.dataLaneAt localMonitor target) actual =
      O.receiptLane (O.dataLaneAt localMonitor target) index operation.stamp)
    (recorded : actual.result.application = some (actor, operation)) :
    M.observeData localConfig localMonitor actual target = O.receiptUpdate localMonitor target index operation.stamp operation.releasedPayload := by
  cases target with
  | ack => exact False.elim (notAck rfl)
  | lower | upper | retry =>
    simp only [O.dataLaneAt] at decoded
    simp only [M.observeData, decoded, O.receiptLane, M.recordData, recorded, O.receiptUpdate, O.dataLaneAt]
    rfl

private theorem delivered_frame (value : Delivered live path afterStage chunk) (target : M.DropTarget)
    (notAck : target ≠ .ack) (chosen : O.dataLaneAt monitor.exchange.forward target = lane) :
    M.observeData ((cfg).at current.report.final).forward monitor.exchange.forward value.value.delivery.step target =
      O.receiptUpdate monitor.exchange.forward target current.report.final.receipts.length value.value.delivery.localStep.stamp chunk := by
  have decoded : M.dataLane ((cfg).at current.report.final).forward (O.dataLaneAt monitor.exchange.forward target) value.value.delivery.step =
      O.receiptLane (O.dataLaneAt monitor.exchange.forward target) current.report.final.receipts.length value.value.delivery.localStep.stamp := by
    rw [chosen]
    exact data_lane value
  have recorded : value.value.delivery.step.result.application = some (sender.other, value.value.delivery.localStep) := by
    simpa only [path.actor] using value.value.delivery.recorded
  simpa only [value.value.localRelease] using receipt_frame ((cfg).at current.report.final).forward monitor.exchange.forward
    value.value.delivery.step target notAck value.value.delivery.localStep current.report.final.receipts.length decoded recorded

private theorem receipt_serves (value : Delivered live path afterStage chunk) :
    M.servesOption (M.laneDemand ((cfg).at current.report.final).forward value.value.delivery.step.before monitor.exchange.forward lane)
      value.value.delivery.step.event = true := by
  rw [value.value.delivery.beforeEq, value.value.delivery.event]
  exact CampusTCPTwoProgressPhaseObserve.laneDemand_serves _ _ _ _ _ (path.action ((cfg).at current.report.final).forward)

private theorem local_ordinary (value : Delivered live path afterStage chunk)
    (forward : monitor.exchange.mode = .forward)
    (allowed : W.Allowed cfg current.report.final monitor value.value.delivery.step.event) :
    CampusTCPTwoProgressMonitor.observe ((cfg).at current.report.final).forward monitor.exchange.forward value.value.delivery.step =
      M.observeOrdinary ((cfg).at current.report.final).forward monitor.exchange.forward value.value.delivery.step := by
  have ordinary := (allowed_receipt cfg current.report.final monitor path.index path.emission.bytes
    (by rw [← value.value.delivery.event]; exact allowed)).2.2
  apply F.observe_action _ _ _ value.value.delivery.supported value.value.delivery.passed _
    (.deliver path.index path.emission.bytes true) value.value.delivery.event
  rw [value.value.delivery.beforeEq, value.value.delivery.event]
  simpa only [CampusTCPTwoProgressMonitor.Allowed, CampusTCPTwoExchangeMonitor.Allowed,
    CampusTCPTwoExchangeMonitor.allowed, forward] using ordinary

private theorem lift_receipt (value : Delivered live path afterStage chunk) (target : M.DropTarget) (notAck : target ≠ .ack)
    (forward : monitor.exchange.mode = .forward) (mode : monitor.exchange.forward.mode = .originals ∨ monitor.exchange.forward.mode = .recovery)
    (allowed : W.Allowed cfg current.report.final monitor value.value.delivery.step.event)
    (localStep : CampusTCPTwoProgressMonitor.observe ((cfg).at current.report.final).forward monitor.exchange.forward value.value.delivery.step =
      O.receiptUpdate monitor.exchange.forward target current.report.final.receipts.length value.value.delivery.localStep.stamp chunk) :
    W.observe cfg monitor value.value.delivery.step = afterReceipt monitor target current.report.final.receipts.length value.value.delivery.localStep.stamp chunk := by
  obtain ⟨drain, control, ordinary⟩ := allowed_receipt cfg current.report.final monitor path.index path.emission.bytes
    (by rw [← value.value.delivery.event]; exact allowed)
  have checked : (value.value.delivery.step.result.supported && value.value.delivery.step.result.passed &&
      CampusTCPTwoExchangeMonitor.allowed ((cfg).at value.value.delivery.step.before) value.value.delivery.step.before monitor.exchange value.value.delivery.step.event) = true := by
    rw [value.value.delivery.supported, value.value.delivery.passed, value.value.delivery.beforeEq, value.value.delivery.event]
    simpa only [Bool.true_and, CampusTCPTwoExchangeMonitor.Allowed] using ordinary
  have nextMode : (O.receiptUpdate monitor.exchange.forward target current.report.final.receipts.length value.value.delivery.localStep.stamp chunk).mode =
      monitor.exchange.forward.mode := by cases target <;> first | rfl | exact False.elim (notAck rfl)
  have exchange : CampusTCPTwoExchangeMonitor.observe ((cfg).at value.value.delivery.step.before) monitor.exchange value.value.delivery.step =
      (afterReceipt monitor target current.report.final.receipts.length value.value.delivery.localStep.stamp chunk).exchange := by
    rw [CampusTCPTwoExchangeMonitor.observe, ite_eq_left checked, value.value.delivery.beforeEq]
    simp only [forward, localStep, nextMode]
    have healthy : (monitor.exchange.forward.mode == .invalid) = false := by
      rcases mode with original | recovery
      · rw [original]; rfl
      · rw [recovery]; rfl
    have unfinished : (monitor.exchange.forward.mode == .done) = false := by
      rcases mode with original | recovery
      · rw [original]; rfl
      · rw [recovery]; rfl
    rw [healthy, unfinished]
    simp only [Bool.false_eq_true, ite_false]
    change { monitor.exchange with
      forward := O.receiptUpdate monitor.exchange.forward target current.report.final.receipts.length value.value.delivery.localStep.stamp chunk
      slots := monitor.exchange.slots + 1
      drops := (match value.value.delivery.step.event with | .dropPacket id => monitor.exchange.drops ++ [id] | _ => monitor.exchange.drops)
      timeouts := (match value.value.delivery.step.event with | .timeout _ true => monitor.exchange.timeouts + 1 | _ => monitor.exchange.timeouts) } = _
    rw [value.value.delivery.event]
    rfl
  have checkedWhole : (value.value.delivery.step.result.supported && value.value.delivery.step.result.passed &&
      CampusTCPTwoTransferMonitor.allowed cfg value.value.delivery.step.before monitor value.value.delivery.step.event) = true := by
    rw [value.value.delivery.supported, value.value.delivery.passed, value.value.delivery.beforeEq]
    exact allowed
  rw [W.observe, ite_eq_left checkedWhole, value.value.delivery.beforeEq, drain, control,
    CampusTCPTwoTransferMonitor.ordinary, exchange]
  simp only [afterReceipt, forward, reduceCtorEq, decide_false, Bool.false_eq_true, ite_false]

theorem lower_observe {path : DataLink initial current part monitor.exchange.forward.lower}
    (value : Delivered live path afterStage chunk) (forward : monitor.exchange.mode = .forward)
    (mode : monitor.exchange.forward.mode = .originals) (first : monitor.exchange.forward.lower.phase ≠ .needSend)
    (second : monitor.exchange.forward.upper.phase ≠ .needSend) (ack : monitor.exchange.forward.ack = none)
    (allowed : W.Allowed cfg current.report.final monitor value.value.delivery.step.event) :
    W.observe cfg monitor value.value.delivery.step = afterReceipt monitor .lower current.report.final.receipts.length value.value.delivery.localStep.stamp chunk := by
  apply lift_receipt value .lower (by decide) forward (.inl mode) allowed
  rw [local_ordinary value forward allowed, F.observe_original_lower _ _ _ mode first second ack (receipt_serves value)]
  exact delivered_frame value .lower (by decide) rfl

theorem upper_observe {path : DataLink initial current part monitor.exchange.forward.upper}
    (value : Delivered live path afterStage chunk) (forward : monitor.exchange.mode = .forward)
    (mode : monitor.exchange.forward.mode = .originals) (first : monitor.exchange.forward.lower.phase ≠ .needSend)
    (second : monitor.exchange.forward.upper.phase ≠ .needSend) (ack : monitor.exchange.forward.ack = none)
    (lower : M.servesOption (M.laneDemand ((cfg).at current.report.final).forward current.report.final monitor.exchange.forward monitor.exchange.forward.lower)
      value.value.delivery.step.event = false)
    (allowed : W.Allowed cfg current.report.final monitor value.value.delivery.step.event) :
    W.observe cfg monitor value.value.delivery.step = afterReceipt monitor .upper current.report.final.receipts.length value.value.delivery.localStep.stamp chunk := by
  apply lift_receipt value .upper (by decide) forward (.inl mode) allowed
  rw [local_ordinary value forward allowed, F.observe_original_upper _ _ _ mode first second ack
    (by rw [value.value.delivery.beforeEq]; exact lower) (receipt_serves value)]
  exact delivered_frame value .upper (by decide) rfl

theorem retry_observe {path : DataLink initial current part monitor.exchange.forward.retry}
    (value : Delivered live path afterStage chunk) (forward : monitor.exchange.mode = .forward)
    (mode : monitor.exchange.forward.mode = .recovery) (ack : monitor.exchange.forward.ack = none) (waiting : monitor.exchange.forward.waiting = false)
    (allowed : W.Allowed cfg current.report.final monitor value.value.delivery.step.event) :
    W.observe cfg monitor value.value.delivery.step = afterReceipt monitor .retry current.report.final.receipts.length value.value.delivery.localStep.stamp chunk := by
  apply lift_receipt value .retry (by decide) forward (.inr mode) allowed
  rw [local_ordinary value forward allowed]
  simp only [M.observeOrdinary, mode, ack, waiting, Bool.false_eq_true, ite_false]
  simpa only [O.receiptUpdate, mode, ack, waiting] using delivered_frame value .retry (by decide) rfl

end Netlib.Check.CampusTCPTwoTransferReceiveObserve
