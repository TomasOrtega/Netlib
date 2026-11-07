import Netlib.Check.CampusTCPTwoTransferPostRead

/-!
# Reverse writing at the current post-read cut

Actual intervening clocks retain the selected reader and writer history.
The reverse batch comes from the same current write operation.
-/

namespace Netlib.Check.CampusTCPTwoTransferCurrentReverseWrite

open Protocol Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart
open CampusTCPTwoTransferNative (Checks Routing)
open CampusTCPTwoTransferEvidence (Evidence ReadAdvanced)
open CampusTCPTwoTransferPostRead (After)
open CampusTCPTwoTransferLocatedCore (config)
open CampusTCPTwoProgressReframe (retain_basis native_env native_entry)
open CampusTCPTwoReverseEndpoints (Reserves closed_idle closed_pending closed_pendingLimit closed_mss written_idle)

namespace W
export CampusTCPTwoTransferMonitor (Monitor Allowed observe)
end W
export CampusTCPTwoTransferReverseWrite (afterWrite)

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut readBefore current : Cut input complete} {sender : Actor} {gateway location : Gateway}
variable {lower upper : List UInt8} {initial : TwoWriteInitial cut sender gateway lower upper}
variable {checks : Checks cut initial.gatewayState.session.entry} {routing : Routing cut gateway}
variable {quantum allowance : Nat} {reverseLower reverseUpper : List UInt8}
variable {readMonitor monitor : W.Monitor} {readActual actual : Step input}
variable {evidence : Evidence initial checks routing quantum allowance reverseLower reverseUpper readBefore readMonitor location}
variable {forward : ReadAdvanced evidence readActual}

local notation "cfg" => config initial checks routing quantum allowance reverseLower reverseUpper

variable (value : After forward current monitor)

def sender_idle : IdleEndpoint (endpoint current.endpoints sender) where
  recovery := value.senderFlight.recovery
  reaction := value.senderFlight.reaction
  runtime := value.senderFlight.runtime
  ackRuntime := value.senderFlight.ackRuntime
  outstanding := value.senderFlight.ledger
  sent := by rw [value.senderFlight.core]; rfl
  deadline := (value.senderFlight.idle rfl).1
  timedOut := (value.senderFlight.idle rfl).2.1
  timeoutCount := (value.senderFlight.idle rfl).2.2
  duplicate := value.senderDuplicate
  valid := value.senderFlight.valid
  coherent := value.senderFlight.coherent
  prepared := value.senderFlight.prepared
  storage := value.senderFlight.storage

theorem reserves (value : After forward current monitor) (reserve : CampusTCPTwoReverseReserves.Initial initial reverseLower reverseUpper) :
    Reserves current sender reverseLower reverseUpper where
  pending := by rw [closed_pendingLimit value.receiver]; exact reserve.pending
  mss := by rw [closed_mss value.receiver]; exact reserve.mss
  window := by
    apply Nat.le_trans _ value.receiver.sendWindow_floor
    exact Nat.le_min.mpr ⟨reserve.window, by simpa only [List.length_append,
      CampusTCPTwoProgressReceiver.advertisedFloor] using reserve.receive⟩
  receiveSpace := Nat.le_trans reserve.receive value.senderFlight.advertised

def after_write_sender (reserve : CampusTCPTwoReverseReserves.Initial initial reverseLower reverseUpper)
    (write : CampusTCPWriteEnabled.WriteMove current sender.other (reverseLower ++ reverseUpper) actual) :
    WrittenSender write.move.after sender.other reverseLower reverseUpper where
  idle := by
    rw [write.selected]
    exact written_idle (closed_idle value.receiver) _ (by
      rw [closed_pending value.receiver, List.length_nil, Nat.zero_add]
      exact (reserves value reserve).pending)
  pending := by rw [write.selected]; simp only [Endpoint.writeState, closed_pending value.receiver, List.nil_append]
  held := by rw [write.selected]; exact value.receiver.held
  window := by rw [write.selected]; exact (reserves value reserve).window
  mss := by rw [write.selected]; exact (reserves value reserve).mss

def after_write_receiver (reserve : CampusTCPTwoReverseReserves.Initial initial reverseLower reverseUpper)
    (write : CampusTCPWriteEnabled.WriteMove current sender.other (reverseLower ++ reverseUpper) actual) :
    EmptyReceiver write.move.after sender (reverseLower ++ reverseUpper) := by
  have peer : endpoint write.move.after.endpoints sender = endpoint current.endpoints sender := by
    have other : sender.other.other = sender := by cases sender <;> rfl
    simpa only [other] using write.peer
  exact {
    idle := by rw [peer]; exact sender_idle value
    pending := by rw [peer]; exact value.senderFlight.pending
    unread := by rw [peer, value.senderFlight.core]; exact reserve.unread
    held := by
      rw [peer]
      have store := congrArg CampusTCPTwoProgressSender.Parameters.receiveStore value.senderFlight.fixed
      change (endpoint current.endpoints sender).receiveStore = (endpoint cut.endpoints sender).receiveStore at store
      rw [store]
      exact initial.senderState.held
    space := by rw [peer]; exact (reserves value reserve).receiveSpace }

theorem write_allowed (value : After forward current monitor) : W.Allowed cfg current.report.final monitor (.write sender.other (reverseLower ++ reverseUpper)) := by
  have noDrain := CampusTCPTwoTransferControlObserve.noDrain_of_non_capture current.report.final monitor
    (by rw [value.finished]; decide)
  have control : CampusTCPTwoTransferMonitor.controlDemand monitor = none := by
    rw [CampusTCPTwoTransferMonitor.controlDemand, value.finished]
  have valid : monitor.mode ≠ .invalid := by rw [value.finished]; decide
  rw [W.Allowed, CampusTCPTwoTransferMonitor.allowed,
    ite_eq_right (by simpa only [decide_eq_true_eq] using valid), noDrain, control,
    CampusTCPTwoExchangeMonitor.allowed, value.needWrite]
  change (sender.other == sender.other && (reverseLower ++ reverseUpper) == (reverseLower ++ reverseUpper)) = true
  have self : (sender.other == sender.other) = true := by cases sender <;> rfl
  simp only [self, beq_self_eq_true, Bool.true_and]

private theorem write_observed (value : After forward current monitor)
    (write : CampusTCPWriteEnabled.WriteMove current sender.other (reverseLower ++ reverseUpper) actual) :
    W.observe cfg monitor actual = afterWrite monitor := by
  have allowed : W.Allowed cfg current.report.final monitor actual.event := by rw [write.event]; exact write_allowed value
  have checked : (actual.result.supported && actual.result.passed &&
      CampusTCPTwoTransferMonitor.allowed cfg actual.before monitor actual.event) = true := by
    rw [write.move.supported, write.move.passed, write.move.beforeEq]
    exact allowed
  have noDrain := CampusTCPTwoTransferControlObserve.noDrain_of_non_capture current.report.final monitor
    (by rw [value.finished]; decide)
  have control : CampusTCPTwoTransferMonitor.controlDemand monitor = none := by
    rw [CampusTCPTwoTransferMonitor.controlDemand, value.finished]
  have innerAllowed : CampusTCPTwoExchangeMonitor.allowed ((cfg).at actual.before) actual.before monitor.exchange actual.event = true := by
    rw [write.event, CampusTCPTwoExchangeMonitor.allowed, value.needWrite]
    change (sender.other == sender.other && (reverseLower ++ reverseUpper) == (reverseLower ++ reverseUpper)) = true
    have self : (sender.other == sender.other) = true := by cases sender <;> rfl
    simp only [self, beq_self_eq_true, Bool.true_and]
  have innerChecked : (actual.result.supported && actual.result.passed &&
      CampusTCPTwoExchangeMonitor.allowed ((cfg).at actual.before) actual.before monitor.exchange actual.event) = true := by
    rw [write.move.supported, write.move.passed]
    exact innerAllowed
  rw [W.observe, ite_eq_left checked, write.move.beforeEq, noDrain, control,
    CampusTCPTwoTransferMonitor.ordinary, CampusTCPTwoExchangeMonitor.observe,
    ite_eq_left innerChecked, value.needWrite, write.event]
  simp only [reduceCtorEq, decide_false, Bool.false_eq_true, ite_false]
  unfold CampusTCPTwoTransferReverseWrite.afterWrite
  congr 2
  · change (match actual.event with | .dropPacket id => monitor.exchange.drops ++ [id] | _ => monitor.exchange.drops) = _
    rw [write.event]
  · change (match actual.event with | .timeout _ true => monitor.exchange.timeouts + 1 | _ => monitor.exchange.timeouts) = _
    rw [write.event]

structure Boundary (value : After forward current monitor) (actual : Step input) where
  write : CampusTCPWriteEnabled.WriteMove current sender.other (reverseLower ++ reverseUpper) actual
  basis : StartupBasis write.move.after
  gatewayState : GatewayStart write.move.after basis .standby
  session : gatewayState.session = value.gatewayState.gateway.session
  batch : WrittenBatch write.move.after sender.other (reverseLower ++ reverseUpper)
  batchWriter : batch.writer = write.operation
  senderState : WrittenSender write.move.after sender.other reverseLower reverseUpper
  receiverState : EmptyReceiver write.move.after sender (reverseLower ++ reverseUpper)
  native : NativeEnv write.move.after .standby gatewayState.session.entry
  nativeIngress : native.ingress = checks.ingress .standby
  allowed : W.Allowed cfg current.report.final monitor actual.event
  observed : W.observe cfg monitor actual = afterWrite monitor
  recorded : CampusTCPTwoTransferRecorded.Recorded cut cfg write.move.after (W.observe cfg monitor actual)

private theorem entry_ingress {current : Cut input complete} {oldEntry newEntry : NetfilterNAT.Entry}
    (native : NativeEnv current .standby oldEntry) (same : newEntry = oldEntry) :
    (native_entry native same).ingress = native.ingress := by cases same; rfl

def of_write (reserve : CampusTCPTwoReverseReserves.Initial initial reverseLower reverseUpper)
    (write : CampusTCPWriteEnabled.WriteMove current sender.other (reverseLower ++ reverseUpper) actual) : Boundary value actual := by
  have retained : cut.report.steps <+: write.move.after.report.steps := value.anchor.retained.trans write.move.retained
  let currentGateway := value.gatewayState.gateway.reframe (write.gateway .standby)
  let start := currentGateway.start_at retained
  let native := checks.native_env value.anchor.toRetained value.currentRouting
  let nextNative := native_env native write.environment
  have allowed : W.Allowed cfg current.report.final monitor actual.event := by rw [write.event]; exact write_allowed value
  exact {
    write
    basis := retain_basis initial.basis retained
    gatewayState := start
    session := rfl
    batch := write.batch (closed_pending value.receiver) (closed_idle value.receiver).sent
    batchWriter := rfl
    senderState := after_write_sender value reserve write
    receiverState := after_write_receiver value reserve write
    native := native_entry nextNative currentGateway.identity.entry
    nativeIngress := entry_ingress nextNative currentGateway.identity.entry
    allowed
    observed := write_observed value write
    recorded := value.recorded.snoc write.move allowed }

theorem write_at (reserve : CampusTCPTwoReverseReserves.Initial initial reverseLower reverseUpper) :
    ∃ actual, Nonempty (Boundary value actual) := by
  have fits : (endpoint current.endpoints sender.other).pending.length + (reverseLower ++ reverseUpper).length ≤
      (endpoint current.endpoints sender.other).pendingLimit := by
    rw [closed_pending value.receiver, List.length_nil, Nat.zero_add]
    exact (reserves value reserve).pending
  obtain ⟨actual, ⟨write⟩⟩ := CampusTCPWriteEnabled.write_at current sender.other (reverseLower ++ reverseUpper) fits
  exact ⟨actual, ⟨of_write value reserve write⟩⟩

theorem write_actual (reserve : CampusTCPTwoReverseReserves.Initial initial reverseLower reverseUpper)
    (actual : Step input) (before : actual.before = current.report.final)
    (event : actual.event = .write sender.other (reverseLower ++ reverseUpper)) : Nonempty (Boundary value actual) := by
  have fits : (endpoint current.endpoints sender.other).pending.length + (reverseLower ++ reverseUpper).length ≤
      (endpoint current.endpoints sender.other).pendingLimit := by
    rw [closed_pending value.receiver, List.length_nil, Nat.zero_add]
    exact (reserves value reserve).pending
  obtain ⟨write⟩ := CampusTCPWriteEnabled.Step.write actual current sender.other (reverseLower ++ reverseUpper) before event fits
  exact ⟨of_write value reserve write⟩

theorem Boundary.history (boundary : Boundary value actual) :
    boundary.write.move.after.report.steps = forward.value.finalCut.report.steps ++ (value.clocks ++ [actual]) := by
  rw [boundary.write.move.history, value.history, List.append_assoc]

theorem Boundary.suffix (boundary : Boundary value actual) :
    boundary.recorded.suffix = value.recorded.suffix ++ [actual] := by
  apply List.append_cancel_left
  rw [← boundary.recorded.history, boundary.write.move.history, value.recorded.history, List.append_assoc]

theorem Boundary.recovery (boundary : Boundary value actual) :
    (endpoint boundary.write.move.after.endpoints sender.other).recovery = (endpoint current.endpoints sender.other).recovery := by
  rw [boundary.write.selected]
  rfl

theorem Boundary.counter_fields (boundary : Boundary value actual) :
    (W.observe cfg monitor actual).exchange.forward = monitor.exchange.forward ∧
      (W.observe cfg monitor actual).exchange.drops = monitor.exchange.drops ∧
      (W.observe cfg monitor actual).exchange.timeouts = monitor.exchange.timeouts ∧
      (W.observe cfg monitor actual).exchange.slots = monitor.exchange.slots + 1 ∧
      (W.observe cfg monitor actual).exchange.writeSlot = some monitor.exchange.slots ∧
      (W.observe cfg monitor actual).controls = monitor.controls := by
  rw [boundary.observed]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem Boundary.reverse_mode (boundary : Boundary value actual) : (W.observe cfg monitor actual).exchange.mode = .reverse := by
  rw [boundary.observed]
  rfl

end Netlib.Check.CampusTCPTwoTransferCurrentReverseWrite
