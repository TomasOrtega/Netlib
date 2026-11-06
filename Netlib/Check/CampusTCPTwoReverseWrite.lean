import Netlib.Check.CampusTCPTwoProgressEvidence
import Netlib.Check.CampusTCPTwoProgressReframe
import Netlib.Check.CampusTCPTwoReverseEndpoints
import Netlib.Check.CampusTCPTwoReverseReserves

/-!
# The actual reverse write and its retained boundary

The write keeps the completed forward report and native sources.
Initial reserves and actual forward histories supply the endpoint guards.
Gateway sequence geometry is a separate obligation.
-/

namespace Netlib.Check.CampusTCPTwoReverseWrite

open Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart
open CampusTCPTwoProgressEvidence (Complete)
open CampusTCPTwoProgressReframe
open CampusTCPTwoReverseEndpoints (Reserves)

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current : Cut input complete} {sender : Actor} {gateway : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {native : NativeEnv cut gateway initial.gatewayState.session.entry} {quantum allowance : Nat}
variable {monitor : CampusTCPTwoProgressMonitor.Monitor} {reverseLower reverseUpper : List UInt8}

structure Boundary {nativeSource : NativeEnv cut gateway initial.gatewayState.session.entry}
    (forward : Complete initial nativeSource quantum allowance current monitor)
    (reverseLower reverseUpper : List UInt8) (actual : Step input) where
  write : CampusTCPWriteEnabled.WriteMove current sender.other (reverseLower ++ reverseUpper) actual
  basis : StartupBasis write.move.after
  gatewayState : GatewayStart write.move.after basis gateway
  session : gatewayState.session = forward.completed.gatewayState.gateway.session
  batch : WrittenBatch write.move.after sender.other (reverseLower ++ reverseUpper)
  batchWriter : batch.writer = write.operation
  senderState : WrittenSender write.move.after sender.other reverseLower reverseUpper
  receiverState : EmptyReceiver write.move.after sender (reverseLower ++ reverseUpper)
  native : NativeEnv write.move.after gateway gatewayState.session.entry
  nativeIngress : native.ingress = nativeSource.ingress

private theorem entry_ingress {oldEntry newEntry : Protocol.NetfilterNAT.Entry}
    (env : NativeEnv current gateway oldEntry) (same : newEntry = oldEntry) :
    (native_entry env same).ingress = env.ingress := by
  cases same
  rfl

def of_write (forward : Complete initial native quantum allowance current monitor)
    (reserve : Reserves current sender reverseLower reverseUpper)
    (unread : (endpoint cut.endpoints sender).core.received = []) {actual : Step input}
    (write : CampusTCPWriteEnabled.WriteMove current sender.other (reverseLower ++ reverseUpper) actual) :
    Boundary forward reverseLower reverseUpper actual := by
  have pending := CampusTCPTwoReverseEndpoints.closed_pending forward.completed.receiver
  have sent := (CampusTCPTwoReverseEndpoints.receiver_idle forward.completed).sent
  let currentGateway := forward.completed.gatewayState.gateway.reframe (write.gateway gateway)
  have retained : cut.report.steps <+: write.move.after.report.steps :=
    forward.completed.anchor.retained.trans write.move.retained
  let start := gateway_start currentGateway retained
  let env := native_env native (forward.completed.anchor.environment.trans write.environment)
  exact {
    write
    basis := retain_basis initial.basis retained
    gatewayState := start
    session := rfl
    batch := write.batch pending sent
    batchWriter := rfl
    senderState := CampusTCPTwoReverseEndpoints.after_write_sender forward.completed reserve write
    receiverState := CampusTCPTwoReverseEndpoints.after_write_receiver forward.completed reserve unread forward.senderDuplicate write
    native := native_entry env currentGateway.identity.entry
    nativeIngress := entry_ingress env currentGateway.identity.entry }

theorem write_current (forward : Complete initial native quantum allowance current monitor)
    (reserve : Reserves current sender reverseLower reverseUpper)
    (unread : (endpoint cut.endpoints sender).core.received = []) :
    ∃ actual : Step input, Nonempty (Boundary forward reverseLower reverseUpper actual) := by
  have fits : (endpoint current.endpoints sender.other).pending.length + (reverseLower ++ reverseUpper).length ≤
      (endpoint current.endpoints sender.other).pendingLimit := by
    rw [CampusTCPTwoReverseEndpoints.closed_pending forward.completed.receiver, List.length_nil, Nat.zero_add]
    exact reserve.pending
  obtain ⟨actual, ⟨write⟩⟩ := CampusTCPWriteEnabled.write_at current sender.other (reverseLower ++ reverseUpper) fits
  exact ⟨actual, ⟨of_write forward reserve unread write⟩⟩

theorem write_initial (forward : Complete initial native quantum allowance current monitor)
    (reserve : CampusTCPTwoReverseReserves.Initial initial reverseLower reverseUpper) :
    ∃ actual : Step input, Nonempty (Boundary forward reverseLower reverseUpper actual) :=
  write_current forward (CampusTCPTwoReverseReserves.at_current forward reserve) reserve.unread

theorem write_actual (forward : Complete initial native quantum allowance current monitor)
    (reserve : CampusTCPTwoReverseReserves.Initial initial reverseLower reverseUpper)
    (actual : Step input) (before : actual.before = current.report.final)
    (event : actual.event = .write sender.other (reverseLower ++ reverseUpper)) :
    Nonempty (Boundary forward reverseLower reverseUpper actual) := by
  let currentReserve := CampusTCPTwoReverseReserves.at_current forward reserve
  have fits : (endpoint current.endpoints sender.other).pending.length + (reverseLower ++ reverseUpper).length ≤
      (endpoint current.endpoints sender.other).pendingLimit := by
    rw [CampusTCPTwoReverseEndpoints.closed_pending forward.completed.receiver, List.length_nil, Nat.zero_add]
    exact currentReserve.pending
  obtain ⟨write⟩ := CampusTCPWriteEnabled.Step.write actual current sender.other (reverseLower ++ reverseUpper) before event fits
  exact ⟨of_write forward currentReserve reserve.unread write⟩

variable {actual : Step input}
variable {forward : Complete initial native quantum allowance current monitor}

theorem Boundary.history (boundary : Boundary forward reverseLower reverseUpper actual) :
    boundary.write.move.after.report.steps = current.report.steps ++ [actual] := boundary.write.move.history

theorem Boundary.ack (boundary : Boundary forward reverseLower reverseUpper actual) :
    (endpoint boundary.write.move.after.endpoints sender.other).ackReaction =
      (endpoint current.endpoints sender.other).ackReaction :=
  CampusTCPTwoReverseEndpoints.after_write_ack boundary.write

theorem Boundary.recovery (boundary : Boundary forward reverseLower reverseUpper actual) :
    (endpoint boundary.write.move.after.endpoints sender.other).recovery =
      (endpoint current.endpoints sender.other).recovery :=
  CampusTCPTwoReverseEndpoints.after_write_recovery boundary.write

end Netlib.Check.CampusTCPTwoReverseWrite
