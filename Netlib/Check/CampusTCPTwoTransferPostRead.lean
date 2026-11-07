import Netlib.Check.CampusTCPTwoTransferReverseGeometry
import Netlib.Check.CampusTCPTwoProgressNetworkState

/-!
# The same read boundary through actual clocks

The selected reader stays fixed while current endpoint clocks advance.
The pending reverse write keeps the same actual report and loss book.
-/

namespace Netlib.Check.CampusTCPTwoTransferPostRead

open Protocol Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPRoundPhaseBase (Move)
open CampusTCPTwoProgressStart
open CampusTCPTwoTransferNative (Checks Routing)
open CampusTCPTwoTransferEvidence (Evidence ReadAdvanced)
open CampusTCPTwoTransferLocatedCore (config)

namespace W
export CampusTCPTwoTransferMonitor (Monitor Allowed observe)
end W
namespace E
export CampusTCPTwoTransferReverseEndpoints (flight closed)
end E

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut readBefore current next : Cut input complete} {sender : Actor} {gateway location : Gateway}
variable {lower upper : List UInt8} {initial : TwoWriteInitial cut sender gateway lower upper}
variable {checks : Checks cut initial.gatewayState.session.entry} {routing : Routing cut gateway}
variable {quantum allowance : Nat} {reverseLower reverseUpper : List UInt8}
variable {readMonitor monitor : W.Monitor} {readActual actual : Step input}
variable {evidence : Evidence initial checks routing quantum allowance reverseLower reverseUpper readBefore readMonitor location}

local notation "cfg" => config initial checks routing quantum allowance reverseLower reverseUpper

def afterClocks (monitor : W.Monitor) (count : Nat) : W.Monitor :=
  { monitor with exchange := { monitor.exchange with slots := monitor.exchange.slots + count } }

@[simp] theorem afterClocks_zero (monitor : W.Monitor) : afterClocks monitor 0 = monitor := by
  cases monitor
  rfl

theorem afterClocks_succ (monitor : W.Monitor) (count : Nat) :
    afterClocks (afterClocks monitor count) 1 = afterClocks monitor (count + 1) := by
  simp only [afterClocks, Nat.add_assoc]

structure After (forward : ReadAdvanced evidence readActual) (current : Cut input complete) (monitor : W.Monitor) where
  clocks : List (Step input)
  history : current.report.steps = forward.value.finalCut.report.steps ++ clocks
  placement : CampusTCPRecoveryRoundPhaseBase.At forward.value.finalCut current
  observed : monitor = afterClocks (W.observe cfg readMonitor readActual) clocks.length
  recorded : CampusTCPTwoTransferRecorded.Recorded cut cfg current monitor
  anchor : CampusTCPTwoTransferState.AnchorAt cut current
  phase : CampusTCPTwoTransferControlState.Phase current.report.final .finished .standby
  senderFlight : CampusTCPTwoProgressSender.Flight initial (endpoint current.endpoints sender)
    (.retired forward.first forward.second) readMonitor.exchange.forward.retries
  receiver : CampusTCPTwoProgressRead.ReceiverClosed initial (endpoint current.endpoints sender.other)
  gatewayState : CampusTCPTwoProgressGatewayAt.ViewAt initial current .standby
  gatewayComplete : CampusTCPTwoTransferGatewayComplete.Facts gatewayState
  senderDuplicate : senderFlight.recovery.duplicateAcks = 0
  originals : CampusTCPTwoProgressSourceHistory.Originals initial current (.retired forward.first forward.second)
  writer : CampusTCPTwoProgressWriteHistory.History initial current (lower ++ upper)
  sources : CampusTCPTwoProgressReceiptSources.History initial current
  readHistory : CampusTCPTwoProgressHistory.Complete cut current sender.other (lower ++ upper) forward.value.value.operation
  losses : CampusTCPTwoTransferLossHistory.History initial cfg current monitor
  book : losses.book = forward.value.losses.book

variable {forward : ReadAdvanced evidence readActual}

def ofRead (forward : ReadAdvanced evidence readActual) :
    After forward forward.value.finalCut (W.observe cfg readMonitor readActual) := by
  have located := CampusTCPTwoTransferReverseWrite.read_location forward
  subst location
  exact {
    clocks := [], history := (List.append_nil _).symm
    placement := CampusTCPRecoveryRoundPhaseBase.At.refl _
    observed := (afterClocks_zero _).symm
    recorded := forward.recorded
    anchor := forward.value.value.anchor
    phase := CampusTCPTwoTransferReverseWrite.read_phase forward
    senderFlight := E.flight forward
    receiver := E.closed forward
    gatewayState := forward.value.gatewayState
    gatewayComplete := forward.gateway_complete
    senderDuplicate := forward.sender_duplicate
    originals := forward.value.originals
    writer := forward.value.writer
    sources := forward.value.sources
    readHistory := forward.value.value.history
    losses := forward.value.losses
    book := rfl }

variable (value : After forward current monitor)

theorem After.finished (value : After forward current monitor) : monitor.mode = .finished := by
  rw [value.observed]
  exact CampusTCPTwoTransferReverseWrite.read_finished forward

theorem After.needWrite (value : After forward current monitor) : monitor.exchange.mode = .needWrite := by
  rw [value.observed]
  exact forward.need_write

theorem After.forward_eq (value : After forward current monitor) : monitor.exchange.forward = (W.observe cfg readMonitor readActual).exchange.forward := by
  rw [value.observed]
  rfl

theorem After.controls (value : After forward current monitor) : monitor.controls = (W.observe cfg readMonitor readActual).controls := by
  rw [value.observed]
  rfl

theorem After.currentRouting (value : After forward current monitor) : Routing current .standby := CampusTCPTwoTransferControlState.finished_routing value.phase

def After.native : NativeEnv current .standby value.gatewayState.gateway.session.entry :=
  CampusTCPTwoProgressReframe.native_entry (checks.native_env value.anchor.toRetained value.currentRouting)
    value.gatewayState.gateway.identity.entry

theorem After.local_allowed (value : After forward current monitor) {actor : Actor} {millis : Nat}
    (allowed : W.Allowed cfg current.report.final monitor (.advanceClock actor millis)) :
    CampusTCPTwoProgressMonitor.Allowed ((cfg).at current.report.final).forward
      current.report.final monitor.exchange.forward (.advanceClock actor millis) := by
  have inner := CampusTCPTwoTransferClockBound.allowed_clock cfg current.report.final monitor actor millis allowed
  simpa only [CampusTCPTwoExchangeMonitor.Allowed, CampusTCPTwoExchangeMonitor.allowed,
    value.needWrite, CampusTCPTwoProgressMonitor.Allowed] using inner

private theorem observe_clock (taskConfig : CampusTCPTwoTransferMonitor.Config) (monitor : W.Monitor)
    (finished : monitor.mode = .finished) (needWrite : monitor.exchange.mode = .needWrite)
    (actual : Step input) (supported : actual.result.supported = true) (passed : actual.result.passed = true)
    (event : actual.event = .advanceClock actor millis)
    (allowed : W.Allowed taskConfig actual.before monitor actual.event) :
    W.observe taskConfig monitor actual = afterClocks monitor 1 := by
  have noDrain := CampusTCPTwoTransferControlObserve.noDrain_of_non_capture actual.before monitor
    (by rw [finished]; decide)
  have control : CampusTCPTwoTransferMonitor.controlDemand monitor = none := by
    rw [CampusTCPTwoTransferMonitor.controlDemand, finished]
  have checked : (actual.result.supported && actual.result.passed &&
      CampusTCPTwoTransferMonitor.allowed taskConfig actual.before monitor actual.event) = true := by
    rw [supported, passed]
    exact allowed
  have innerAllowed : CampusTCPTwoExchangeMonitor.allowed (taskConfig.at actual.before) actual.before monitor.exchange actual.event = true := by
    simpa only [W.Allowed, CampusTCPTwoTransferMonitor.allowed, finished, reduceCtorEq,
      decide_false, Bool.false_eq_true, ite_false, noDrain, control] using allowed
  have innerChecked : (actual.result.supported && actual.result.passed &&
      CampusTCPTwoExchangeMonitor.allowed (taskConfig.at actual.before) actual.before monitor.exchange actual.event) = true := by
    rw [supported, passed]
    exact innerAllowed
  rw [W.observe, ite_eq_left checked, noDrain, control, CampusTCPTwoTransferMonitor.ordinary,
    CampusTCPTwoExchangeMonitor.observe, ite_eq_left innerChecked, needWrite, event]
  change (if decide (monitor.exchange.mode = .invalid) then monitor.invalid else _) = _
  rw [needWrite]
  simp only [reduceCtorEq, decide_false, Bool.false_eq_true, ite_false]
  unfold afterClocks
  congr 1
  change { monitor.exchange with
    slots := monitor.exchange.slots + 1
    drops := match actual.event with | .dropPacket id => monitor.exchange.drops ++ [id] | _ => monitor.exchange.drops
    timeouts := match actual.event with | .timeout _ true => monitor.exchange.timeouts + 1 | _ => monitor.exchange.timeouts } = _
  rw [event]

structure Clocked (value : After forward current monitor) (actor : Actor) (millis : Nat) (actual : Step input) where
  move : Move current actual
  event : actual.event = .advanceClock actor millis
  placement : CampusTCPRecoveryRoundPhaseBase.At current move.after
  next : After forward move.after (W.observe cfg monitor actual)
  observed : W.observe cfg monitor actual = afterClocks monitor 1
  clocks : next.clocks = value.clocks ++ [actual]
  book : next.losses.book = value.losses.book

theorem Step.clock {actor : Actor} {millis : Nat} (value : After forward current monitor)
    (actual : Step input) (before : actual.before = current.report.final)
    (event : actual.event = .advanceClock actor millis)
    (allowed : W.Allowed cfg current.report.final monitor actual.event) : Nonempty (Clocked value actor millis actual) := by
  have localAllowed := value.local_allowed (by rw [← event]; exact allowed)
  let anchor := CampusTCPGapProgressPhaseBase.Anchor.refl current value.anchor.guards
  obtain ⟨clocked⟩ := CampusTCPTwoProgressClock.Step.clock actual anchor ((cfg).at current.report.final).forward
    monitor.exchange.forward actor millis before event localAllowed
  have observed := observe_clock cfg monitor value.finished value.needWrite actual clocked.move.supported
    clocked.move.passed event (by rw [before]; exact allowed)
  have senderTime := CampusTCPTwoProgressNetworkState.clock_time clocked value.anchor.guards localAllowed sender
  have receiverTime := CampusTCPTwoProgressNetworkState.clock_time clocked value.anchor.guards localAllowed sender.other
  let flight := value.senderFlight.clock (clocked.placement.frame.endpointFrame sender) senderTime
  let receiver := value.receiver.clock (clocked.placement.frame.endpointFrame sender.other) receiverTime
  let view := value.gatewayState.reframe (clocked.placement.frame.beforeService .standby)
  let losses := value.losses.append clocked.move
    (by simp only [CampusTCPTwoProgressLossHistory.isDrop, event])
    (by simp only [CampusTCPTwoExchangeLoss.isTimeoutOutput, event])
    (by rw [observed]; rfl) (by rw [observed]; rfl) (by rw [observed]; rfl) (by rw [observed]; rfl)
  have phase : CampusTCPTwoTransferControlState.Phase clocked.move.after.report.final .finished .standby := by
    cases value.phase with
    | finished fields => exact .finished (fields.nonservice clocked.move (by rw [event]; trivial))
  let next : After forward clocked.move.after (W.observe cfg monitor actual) := {
    clocks := value.clocks ++ [actual]
    history := by rw [clocked.move.history, value.history, List.append_assoc]
    placement := value.placement.trans clocked.placement
    observed := by
      calc
        W.observe cfg monitor actual = afterClocks monitor 1 := observed
        _ = afterClocks (afterClocks (W.observe cfg readMonitor readActual) value.clocks.length) 1 :=
          congrArg (fun raw => afterClocks raw 1) value.observed
        _ = afterClocks (W.observe cfg readMonitor readActual) (value.clocks.length + 1) := afterClocks_succ _ _
        _ = afterClocks (W.observe cfg readMonitor readActual) (value.clocks ++ [actual]).length := by
          simp only [List.length_append, List.length_cons, List.length_nil]
    recorded := value.recorded.snoc clocked.move allowed
    anchor := ⟨⟨value.anchor.retained.trans clocked.move.retained, fun selected => (value.anchor.policy selected).trans
      (congrArg CampusTCPService.Before.environment (clocked.placement.frame.beforeService selected)).symm⟩,
      clocked.anchor.guards⟩
    phase
    senderFlight := flight
    receiver
    gatewayState := view
    gatewayComplete := value.gatewayComplete.same_service view (clocked.placement.frame.beforeService .standby)
    senderDuplicate := value.senderDuplicate
    originals := value.originals.clock clocked.placement
    writer := value.writer.clock clocked.placement
    sources := value.sources.non_delivery clocked.move (by rw [event]; trivial)
    readHistory := value.readHistory.clock clocked.placement
    losses
    book := value.book }
  exact ⟨⟨clocked.move, event, clocked.placement, next, observed, rfl, rfl⟩⟩

end Netlib.Check.CampusTCPTwoTransferPostRead
