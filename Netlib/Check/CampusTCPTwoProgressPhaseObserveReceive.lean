import Netlib.Check.CampusTCPTwoProgressPhaseObserve
import Netlib.Check.CampusTCPTwoProgressPhaseReceive

/-!
# Observation of the actual data receipt

The stored local step supplies the receipt stamp and released chunk.
Each receipt starts the one current ACK path.
-/

namespace Netlib.Check.CampusTCPTwoProgressPhaseObserveReceive

open Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart CampusTCPTwoProgressPhaseBase
open CampusTCPTwoProgressSetup (config)

namespace M
export CampusTCPTwoProgressMonitor
  (Monitor Lane DropTarget dataLane recordData observe observeOrdinary observeData laneDemand servesOption)
end M
namespace F
export CampusTCPTwoProgressMonitorFacts (observe_action observe_original_lower observe_original_upper)
end F
namespace P
export CampusTCPTwoProgressPaths (DataLink)
end P
namespace D
export CampusTCPTwoProgressPhaseReceive (Delivered)
end D
namespace S
export CampusTCPTwoProgressSender (Stage Part)
end S
namespace R
export CampusTCPTwoProgressReceiver (Stage)
end R
local notation "Config" => CampusTCPTwoProgressMonitor.Config

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current : Cut input complete} {sender : Actor} {gateway : Gateway} {lower upper chunk : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {native : NativeEnv cut gateway initial.gatewayState.session.entry} {quantum allowance : Nat}
variable {monitor : M.Monitor} {sent : S.Stage initial} {beforeStage afterStage : R.Stage} {part : S.Part}
variable {lane : M.Lane} {core : Core initial native quantum allowance current monitor sent beforeStage}

def receiptLane (lane : M.Lane) (index stamp : Nat) : M.Lane :=
  ⟨.done, { lane.refs with dataReceipt := some index, dataReceiveStamp := some stamp }⟩

def dataLaneAt (monitor : M.Monitor) : M.DropTarget → M.Lane
  | .lower => monitor.lower
  | .upper => monitor.upper
  | .retry => monitor.retry
  | .ack => { phase := .invalid }

private def replaceData (monitor : M.Monitor) (target : M.DropTarget) (lane : M.Lane) : M.Monitor :=
  match target with
  | .lower => { monitor with lower := lane, lastOriginal := some .lower }
  | .upper => { monitor with upper := lane, lastOriginal := some .upper }
  | .retry => { monitor with retry := lane }
  | .ack => monitor.invalid

def receiptUpdate (monitor : M.Monitor) (target : M.DropTarget) (index stamp : Nat) (released : List UInt8) : M.Monitor :=
  let lane := receiptLane (dataLaneAt monitor target) index stamp
  { replaceData monitor target lane with
    ack := some { phase := .needAck, refs := lane.refs }
    waiting := false
    dataReceipts := monitor.dataReceipts ++ [index]
    releaseStamps := if released.isEmpty then monitor.releaseStamps else monitor.releaseStamps ++ [stamp] }

private theorem receipt_frame (cfg : Config) (monitor : M.Monitor) (actual : Step input) (target : M.DropTarget)
    (notAck : target ≠ .ack) (operation : ApplicationTrace.Step) (index : Nat)
    (decoded : M.dataLane cfg (dataLaneAt monitor target) actual =
      receiptLane (dataLaneAt monitor target) index operation.stamp)
    (recorded : actual.result.application = some (actor, operation)) :
    M.observeData cfg monitor actual target = receiptUpdate monitor target index operation.stamp operation.releasedPayload := by
  cases target with
  | ack => exact False.elim (notAck rfl)
  | lower | upper | retry =>
    simp only [dataLaneAt] at decoded
    simp only [M.observeData, decoded, receiptLane, M.recordData, recorded, receiptUpdate, dataLaneAt, replaceData]
    rfl

theorem delivered_serves {path : P.DataLink initial current part lane} (value : D.Delivered core path afterStage chunk) :
    M.servesOption (M.laneDemand (config initial native quantum allowance) value.value.delivery.step.before monitor lane)
      value.value.delivery.step.event = true := by
  rw [value.value.delivery.beforeEq, value.value.delivery.event]
  exact CampusTCPTwoProgressPhaseObserve.laneDemand_serves _ _ _ _ _ (path.action (config initial native quantum allowance))

private theorem delivered_ordinary {path : P.DataLink initial current part lane} (value : D.Delivered core path afterStage chunk)
    (allowed : CampusTCPTwoProgressMonitor.Allowed (config initial native quantum allowance) current.report.final monitor
      (.deliver path.index path.emission.bytes true)) :
    M.observe (config initial native quantum allowance) monitor value.value.delivery.step =
      M.observeOrdinary (config initial native quantum allowance) monitor value.value.delivery.step :=
  F.observe_action _ _ _ value.value.delivery.supported value.value.delivery.passed
    (by simpa only [value.value.delivery.beforeEq, value.value.delivery.event] using allowed)
    (.deliver path.index path.emission.bytes true) value.value.delivery.event

private theorem delivered_frame {path : P.DataLink initial current part lane} (value : D.Delivered core path afterStage chunk)
    (target : M.DropTarget) (notAck : target ≠ .ack) (chosenLane : dataLaneAt monitor target = lane) :
    M.observeData (config initial native quantum allowance) monitor value.value.delivery.step target =
      receiptUpdate monitor target current.report.final.receipts.length value.value.delivery.localStep.stamp chunk := by
  have decoded : M.dataLane (config initial native quantum allowance) (dataLaneAt monitor target) value.value.delivery.step =
      receiptLane (dataLaneAt monitor target) current.report.final.receipts.length value.value.delivery.localStep.stamp := by
    rw [chosenLane]
    exact value.data_lane
  have recorded : value.value.delivery.step.result.application = some (sender.other, value.value.delivery.localStep) := by
    simpa only [path.actor] using value.value.delivery.recorded
  have frame := receipt_frame (config initial native quantum allowance) monitor value.value.delivery.step target notAck
    value.value.delivery.localStep current.report.final.receipts.length decoded recorded
  simpa only [value.value.localRelease] using frame

theorem receipt_lower {path : P.DataLink initial current part monitor.lower} (value : D.Delivered core path afterStage chunk)
    (mode : monitor.mode = .originals) (first : monitor.lower.phase ≠ .needSend)
    (second : monitor.upper.phase ≠ .needSend) (ack : monitor.ack = none)
    (allowed : CampusTCPTwoProgressMonitor.Allowed (config initial native quantum allowance) current.report.final monitor
      (.deliver path.index path.emission.bytes true)) :
    M.observe (config initial native quantum allowance) monitor value.value.delivery.step =
      receiptUpdate monitor .lower current.report.final.receipts.length value.value.delivery.localStep.stamp chunk := by
  rw [delivered_ordinary value allowed, F.observe_original_lower _ _ _ mode first second ack (delivered_serves value)]
  exact delivered_frame value .lower (by decide) rfl

theorem receipt_upper {path : P.DataLink initial current part monitor.upper} (value : D.Delivered core path afterStage chunk)
    (mode : monitor.mode = .originals) (first : monitor.lower.phase ≠ .needSend)
    (second : monitor.upper.phase ≠ .needSend) (ack : monitor.ack = none)
    (lower : M.servesOption (M.laneDemand (config initial native quantum allowance) value.value.delivery.step.before monitor monitor.lower)
      value.value.delivery.step.event = false)
    (allowed : CampusTCPTwoProgressMonitor.Allowed (config initial native quantum allowance) current.report.final monitor
      (.deliver path.index path.emission.bytes true)) :
    M.observe (config initial native quantum allowance) monitor value.value.delivery.step =
      receiptUpdate monitor .upper current.report.final.receipts.length value.value.delivery.localStep.stamp chunk := by
  rw [delivered_ordinary value allowed, F.observe_original_upper _ _ _ mode first second ack lower (delivered_serves value)]
  exact delivered_frame value .upper (by decide) rfl

theorem receipt_retry {path : P.DataLink initial current part monitor.retry} (value : D.Delivered core path afterStage chunk)
    (mode : monitor.mode = .recovery) (ack : monitor.ack = none) (waiting : monitor.waiting = false)
    (allowed : CampusTCPTwoProgressMonitor.Allowed (config initial native quantum allowance) current.report.final monitor
      (.deliver path.index path.emission.bytes true)) :
    M.observe (config initial native quantum allowance) monitor value.value.delivery.step =
      receiptUpdate monitor .retry current.report.final.receipts.length value.value.delivery.localStep.stamp chunk := by
  rw [delivered_ordinary value allowed]
  simp only [M.observeOrdinary, mode, ack, waiting, Bool.false_eq_true, ite_false]
  simpa only [receiptUpdate, replaceData, mode, ack, waiting] using delivered_frame value .retry (by decide) rfl

theorem receiptUpdate_receipts (monitor : M.Monitor) (target : M.DropTarget) (index stamp : Nat) (released : List UInt8) :
    (receiptUpdate monitor target index stamp released).dataReceipts = monitor.dataReceipts ++ [index] := rfl

theorem receiptUpdate_releases (monitor : M.Monitor) (target : M.DropTarget) (index stamp : Nat) (released : List UInt8) :
    (receiptUpdate monitor target index stamp released).releaseStamps =
      if released.isEmpty then monitor.releaseStamps else monitor.releaseStamps ++ [stamp] := rfl

theorem receiptUpdate_ack (monitor : M.Monitor) (target : M.DropTarget) (index stamp : Nat) (released : List UInt8) :
    (receiptUpdate monitor target index stamp released).ack =
      some { phase := .needAck, refs := (receiptLane (dataLaneAt monitor target) index stamp).refs } := rfl

theorem receiptUpdate_waiting (monitor : M.Monitor) (target : M.DropTarget) (index stamp : Nat) (released : List UInt8) :
    (receiptUpdate monitor target index stamp released).waiting = false := rfl

theorem receiptUpdate_lower (monitor : M.Monitor) (index stamp : Nat) (released : List UInt8) :
    (receiptUpdate monitor .lower index stamp released).lower = receiptLane monitor.lower index stamp := rfl

theorem receiptUpdate_upper (monitor : M.Monitor) (index stamp : Nat) (released : List UInt8) :
    (receiptUpdate monitor .upper index stamp released).upper = receiptLane monitor.upper index stamp := rfl

theorem receiptUpdate_retry (monitor : M.Monitor) (index stamp : Nat) (released : List UInt8) :
    (receiptUpdate monitor .retry index stamp released).retry = receiptLane monitor.retry index stamp := rfl

end Netlib.Check.CampusTCPTwoProgressPhaseObserveReceive
