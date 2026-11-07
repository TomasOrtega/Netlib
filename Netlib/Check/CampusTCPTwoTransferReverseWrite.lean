import Netlib.Check.CampusTCPTwoTransferReverseEndpoints
import Netlib.Check.CampusTCPTwoTransferGatewayComplete
import Netlib.Check.CampusTCPTwoTransferOrdinaryPhase
import Netlib.Check.CampusTCPTwoProgressGatewayAtReady

/-!
# The actual reverse write after the located forward read

The same report supplies the writer, gateway start, and current native checks.
The whole observer retains the forward leg and its shared loss counters.
-/

namespace Netlib.Check.CampusTCPTwoTransferReverseWrite

open Protocol Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart
open CampusTCPTwoTransferNative (Checks Routing)
open CampusTCPTwoTransferEvidence (Evidence ReadAdvanced)
open CampusTCPTwoTransferLocatedCore (config)
open CampusTCPTwoTransferRecorded (Recorded)
open CampusTCPTwoProgressReframe (retain_basis native_env native_entry)

namespace W
export CampusTCPTwoTransferMonitor (Monitor Allowed observe controlDemand drainTicket)
end W
namespace X
export CampusTCPTwoExchangeMonitor (allowed observe)
end X
namespace E
export CampusTCPTwoTransferReverseEndpoints (flight closed sender_idle reserves after_write_sender after_write_receiver)
end E

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current : Cut input complete} {sender : Actor} {gateway location : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {checks : Checks cut initial.gatewayState.session.entry} {routing : Routing cut gateway}
variable {quantum allowance : Nat} {reverseLower reverseUpper : List UInt8}
variable {monitor : W.Monitor} {readActual actual : Step input}
variable {evidence : Evidence initial checks routing quantum allowance reverseLower reverseUpper current monitor location}

local notation "cfg" => config initial checks routing quantum allowance reverseLower reverseUpper


theorem read_phase (forward : ReadAdvanced evidence readActual) :
    CampusTCPTwoTransferControlState.Phase forward.value.finalCut.report.final .finished location := by
  change CampusTCPTwoTransferControlState.Phase forward.value.value.move.after.report.final .finished location
  have control : W.controlDemand monitor = none := by rw [W.controlDemand, forward.value.finished]
  have phase := evidence.controls.nonservice control forward.value.value.move (by rw [forward.value.value.event]; trivial)
  simpa only [forward.value.finished] using phase


theorem read_location (forward : ReadAdvanced evidence readActual) : location = .standby := by
  have phase := read_phase forward
  cases phase
  rfl


theorem read_routing (forward : ReadAdvanced evidence readActual) : Routing forward.value.finalCut .standby :=
  CampusTCPTwoTransferControlState.finished_routing (read_phase forward)


theorem read_finished (forward : ReadAdvanced evidence readActual) : (W.observe cfg monitor readActual).mode = .finished := by
  rw [forward.value.observed]
  exact forward.value.finished


def afterWrite (monitor : W.Monitor) : W.Monitor :=
  { monitor with exchange := { monitor.exchange with
    mode := .reverse, reverse := .initial, slots := monitor.exchange.slots + 1, writeSlot := some monitor.exchange.slots } }

private theorem write_allowed (forward : ReadAdvanced evidence readActual) :
    W.Allowed cfg forward.value.finalCut.report.final (W.observe cfg monitor readActual)
      (.write sender.other (reverseLower ++ reverseUpper)) := by
  have finished := read_finished forward
  have drainless := CampusTCPTwoTransferControlObserve.noDrain_of_non_capture forward.value.finalCut.report.final
    (W.observe cfg monitor readActual) (by rw [finished]; decide)
  have control : W.controlDemand (W.observe cfg monitor readActual) = none := by rw [W.controlDemand, finished]
  have valid : (W.observe cfg monitor readActual).mode ≠ .invalid := by rw [finished]; decide
  rw [W.Allowed, CampusTCPTwoTransferMonitor.allowed,
    ite_eq_right (by simpa only [decide_eq_true_eq] using valid), drainless, control, X.allowed, forward.need_write]
  change (sender.other == sender.other && (reverseLower ++ reverseUpper) == (reverseLower ++ reverseUpper)) = true
  have self : (sender.other == sender.other) = true := by cases sender <;> rfl
  simp only [self, beq_self_eq_true, Bool.true_and]

private theorem write_observed (forward : ReadAdvanced evidence readActual)
    (write : CampusTCPWriteEnabled.WriteMove forward.value.finalCut sender.other (reverseLower ++ reverseUpper) actual) :
    W.observe cfg (W.observe cfg monitor readActual) actual = afterWrite (W.observe cfg monitor readActual) := by
  let before := W.observe cfg monitor readActual
  have allowed : W.Allowed cfg forward.value.finalCut.report.final before actual.event := by
    rw [write.event]
    exact write_allowed forward
  have checked : (actual.result.supported && actual.result.passed &&
      CampusTCPTwoTransferMonitor.allowed cfg actual.before before actual.event) = true := by
    rw [write.move.supported, write.move.passed, write.move.beforeEq]
    exact allowed
  have finished : before.mode = .finished := read_finished forward
  have drainless := CampusTCPTwoTransferControlObserve.noDrain_of_non_capture forward.value.finalCut.report.final before
    (by rw [finished]; decide)
  have control : W.controlDemand before = none := by rw [W.controlDemand, finished]
  have innerAllowed : X.allowed ((cfg).at actual.before) actual.before before.exchange actual.event = true := by
    rw [write.event, X.allowed, show before.exchange.mode = .needWrite from forward.need_write]
    change (sender.other == sender.other && (reverseLower ++ reverseUpper) == (reverseLower ++ reverseUpper)) = true
    have self : (sender.other == sender.other) = true := by cases sender <;> rfl
    simp only [self, beq_self_eq_true, Bool.true_and]
  have innerChecked : (actual.result.supported && actual.result.passed &&
      X.allowed ((cfg).at actual.before) actual.before before.exchange actual.event) = true := by
    rw [write.move.supported, write.move.passed]
    exact innerAllowed
  change W.observe cfg before actual = afterWrite before
  rw [W.observe, ite_eq_left checked, write.move.beforeEq, drainless, control]
  unfold CampusTCPTwoTransferMonitor.ordinary
  rw [X.observe, ite_eq_left innerChecked, show before.exchange.mode = .needWrite from forward.need_write, write.event]
  simp only [reduceCtorEq, decide_false, Bool.false_eq_true, ite_false]
  unfold afterWrite
  congr 2
  · change (match actual.event with | .dropPacket id => before.exchange.drops ++ [id] | _ => before.exchange.drops) = _
    rw [write.event]
  · change (match actual.event with | .timeout _ true => before.exchange.timeouts + 1 | _ => before.exchange.timeouts) = _
    rw [write.event]

structure Boundary (forward : ReadAdvanced evidence readActual) (actual : Step input) where
  write : CampusTCPWriteEnabled.WriteMove forward.value.finalCut sender.other (reverseLower ++ reverseUpper) actual
  basis : StartupBasis write.move.after
  gatewayState : GatewayStart write.move.after basis .standby
  session : gatewayState.session = forward.value.gatewayState.gateway.session
  batch : WrittenBatch write.move.after sender.other (reverseLower ++ reverseUpper)
  batchWriter : batch.writer = write.operation
  senderState : WrittenSender write.move.after sender.other reverseLower reverseUpper
  receiverState : EmptyReceiver write.move.after sender (reverseLower ++ reverseUpper)
  native : NativeEnv write.move.after .standby gatewayState.session.entry
  nativeIngress : native.ingress = checks.ingress .standby
  allowed : W.Allowed cfg forward.value.finalCut.report.final (W.observe cfg monitor readActual) actual.event
  observed : W.observe cfg (W.observe cfg monitor readActual) actual = afterWrite (W.observe cfg monitor readActual)
  recorded : Recorded cut cfg write.move.after (W.observe cfg (W.observe cfg monitor readActual) actual)

private theorem entry_ingress {current : Cut input complete} {oldEntry newEntry : NetfilterNAT.Entry}
    (env : NativeEnv current .standby oldEntry) (same : newEntry = oldEntry) :
    (native_entry env same).ingress = env.ingress := by cases same; rfl


def of_write (forward : ReadAdvanced evidence readActual)
    (reserve : CampusTCPTwoReverseReserves.Initial initial reverseLower reverseUpper)
    (write : CampusTCPWriteEnabled.WriteMove forward.value.finalCut sender.other (reverseLower ++ reverseUpper) actual) :
    Boundary forward actual := by
  have locationEq := read_location forward
  subst location
  have retained : cut.report.steps <+: write.move.after.report.steps := forward.value.value.anchor.retained.trans write.move.retained
  let currentGateway := forward.value.gatewayState.gateway.reframe (write.gateway .standby)
  let start := currentGateway.start_at retained
  let env := checks.native_env forward.value.value.anchor.toRetained (read_routing forward)
  let nextEnv := native_env env write.environment
  have pending := CampusTCPTwoReverseEndpoints.closed_pending (E.closed forward)
  have sent := (CampusTCPTwoReverseEndpoints.closed_idle (E.closed forward)).sent
  have allowed : W.Allowed cfg forward.value.finalCut.report.final (W.observe cfg monitor readActual) actual.event := by
    rw [write.event]
    exact write_allowed forward
  exact {
    write
    basis := retain_basis initial.basis retained
    gatewayState := start
    session := rfl
    batch := write.batch pending sent
    batchWriter := rfl
    senderState := E.after_write_sender forward reserve write
    receiverState := E.after_write_receiver forward reserve write
    native := native_entry nextEnv currentGateway.identity.entry
    nativeIngress := entry_ingress nextEnv currentGateway.identity.entry
    allowed, observed := write_observed forward write
    recorded := forward.recorded.snoc write.move allowed }


theorem write_initial (forward : ReadAdvanced evidence readActual)
    (reserve : CampusTCPTwoReverseReserves.Initial initial reverseLower reverseUpper) :
    ∃ actual, Nonempty (Boundary forward actual) := by
  have fits : (endpoint forward.value.finalCut.endpoints sender.other).pending.length + (reverseLower ++ reverseUpper).length ≤
      (endpoint forward.value.finalCut.endpoints sender.other).pendingLimit := by
    rw [CampusTCPTwoReverseEndpoints.closed_pending (E.closed forward), List.length_nil, Nat.zero_add]
    exact (E.reserves forward reserve).pending
  obtain ⟨actual, ⟨write⟩⟩ := CampusTCPWriteEnabled.write_at forward.value.finalCut sender.other (reverseLower ++ reverseUpper) fits
  exact ⟨actual, ⟨of_write forward reserve write⟩⟩


theorem write_actual (forward : ReadAdvanced evidence readActual)
    (reserve : CampusTCPTwoReverseReserves.Initial initial reverseLower reverseUpper)
    (actual : Step input) (before : actual.before = forward.value.finalCut.report.final)
    (event : actual.event = .write sender.other (reverseLower ++ reverseUpper)) : Nonempty (Boundary forward actual) := by
  have fits : (endpoint forward.value.finalCut.endpoints sender.other).pending.length + (reverseLower ++ reverseUpper).length ≤
      (endpoint forward.value.finalCut.endpoints sender.other).pendingLimit := by
    rw [CampusTCPTwoReverseEndpoints.closed_pending (E.closed forward), List.length_nil, Nat.zero_add]
    exact (E.reserves forward reserve).pending
  obtain ⟨write⟩ := CampusTCPWriteEnabled.Step.write actual forward.value.finalCut sender.other (reverseLower ++ reverseUpper) before event fits
  exact ⟨of_write forward reserve write⟩


theorem Boundary.history {forward : ReadAdvanced evidence readActual} (boundary : Boundary forward actual) :
    boundary.write.move.after.report.steps = forward.value.finalCut.report.steps ++ [actual] := boundary.write.move.history


theorem Boundary.recovery {forward : ReadAdvanced evidence readActual} (boundary : Boundary forward actual) :
    (endpoint boundary.write.move.after.endpoints sender.other).recovery =
      (endpoint forward.value.finalCut.endpoints sender.other).recovery := by rw [boundary.write.selected]; rfl


theorem Boundary.ack {forward : ReadAdvanced evidence readActual} (boundary : Boundary forward actual) :
    (endpoint boundary.write.move.after.endpoints sender.other).ackReaction =
      (endpoint forward.value.finalCut.endpoints sender.other).ackReaction := by rw [boundary.write.selected]; rfl


theorem Boundary.suffix {forward : ReadAdvanced evidence readActual} (boundary : Boundary forward actual) :
    boundary.recorded.suffix = forward.recorded.suffix ++ [actual] := by
  apply List.append_cancel_left
  rw [← boundary.recorded.history, boundary.write.move.history, forward.recorded.history, List.append_assoc]

theorem Boundary.counter_fields {forward : ReadAdvanced evidence readActual} (boundary : Boundary forward actual) :
    (W.observe cfg (W.observe cfg monitor readActual) actual).exchange.forward = (W.observe cfg monitor readActual).exchange.forward ∧
      (W.observe cfg (W.observe cfg monitor readActual) actual).exchange.drops = (W.observe cfg monitor readActual).exchange.drops ∧
      (W.observe cfg (W.observe cfg monitor readActual) actual).exchange.timeouts = (W.observe cfg monitor readActual).exchange.timeouts ∧
      (W.observe cfg (W.observe cfg monitor readActual) actual).exchange.slots = (W.observe cfg monitor readActual).exchange.slots + 1 ∧
      (W.observe cfg (W.observe cfg monitor readActual) actual).exchange.writeSlot = some (W.observe cfg monitor readActual).exchange.slots ∧
      (W.observe cfg (W.observe cfg monitor readActual) actual).controls = (W.observe cfg monitor readActual).controls := by
  rw [boundary.observed]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩


theorem Boundary.reverse_mode {forward : ReadAdvanced evidence readActual} (boundary : Boundary forward actual) :
    (W.observe cfg (W.observe cfg monitor readActual) actual).exchange.mode = .reverse := by rw [boundary.observed]; rfl


theorem Boundary.healthy {forward : ReadAdvanced evidence readActual} (boundary : Boundary forward actual) :
    (W.observe cfg (W.observe cfg monitor readActual) actual).mode ≠ .invalid := by
  rw [boundary.observed]
  change (W.observe cfg monitor readActual).mode ≠ .invalid
  rw [read_finished forward]
  decide

end Netlib.Check.CampusTCPTwoTransferReverseWrite
