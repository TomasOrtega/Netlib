import Netlib.Check.CampusTCPTwoExchangeComplete

/-!
# Permissions for both actual exchange reads

Initial compliance passes through the same reverse write.
Both readers and the write remain in the completed report.
-/

namespace Netlib.Check.CampusTCPTwoExchangeComplete

open Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current : Cut input complete} {sender : Actor} {gateway : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {native : NativeEnv cut gateway initial.gatewayState.session.entry} {quantum allowance : Nat}
variable {reverseLower reverseUpper : List UInt8} {monitor : CampusTCPTwoExchangeMonitor.Monitor}

theorem Complete.written_compliant (value : Complete initial native quantum allowance reverseLower reverseUpper current monitor)
    (prior : cut.report.compliant = true) : value.start.boundary.write.move.after.report.compliant = true := by
  have old := value.forward.compliant prior
  change (value.before.report.steps.all (·.result.supported) && value.before.report.steps.all (·.result.passed)) = true at old
  simp only [Bool.and_eq_true] at old
  simp only [Report.compliant, Report.supported, value.start.boundary.write.move.history, List.all_append,
    List.all_cons, List.all_nil, old.1, old.2, value.start.boundary.write.move.supported,
    value.start.boundary.write.move.passed, Bool.and_self]

theorem Complete.compliant (value : Complete initial native quantum allowance reverseLower reverseUpper current monitor)
    (prior : cut.report.compliant = true) : current.report.compliant = true :=
  value.reverse.compliant (value.written_compliant prior)

theorem Complete.forward_read_permissions (value : Complete initial native quantum allowance reverseLower reverseUpper current monitor)
    (prior : cut.report.compliant = true) (index : Nat) (byte : UInt8) (selected : (lower ++ upper)[index]? = some byte) :
    ∃ origin : CampusTCPTwoProgressReadSuffix.SuffixReadOrigin value.forward.completed index byte,
      Nonempty (CampusTCPTwoProgressWriteOrigins.SelectedWriteOrigin initial origin.attempt origin.read.origin.localIndex byte) ∧
        CampusTCPRoundOrigins.ServicePermissions origin.delivery.service.joint.step origin.delivery.receive.receipt.served :=
  value.forward.read_permissions prior index byte selected

theorem Complete.reverse_read_permissions (value : Complete initial native quantum allowance reverseLower reverseUpper current monitor)
    (prior : cut.report.compliant = true) (index : Nat) (byte : UInt8)
    (selected : (reverseLower ++ reverseUpper)[index]? = some byte) :
    ∃ origin : CampusTCPTwoProgressReadSuffix.SuffixReadOrigin value.reverse.completed index byte,
      Nonempty (CampusTCPTwoProgressWriteOrigins.SelectedWriteOrigin value.start.reverseInitial
        origin.attempt origin.read.origin.localIndex byte) ∧
        CampusTCPRoundOrigins.ServicePermissions origin.delivery.service.joint.step origin.delivery.receive.receipt.served :=
  value.reverse.read_permissions (value.written_compliant prior) index byte selected

theorem Complete.reverse_writer_recorded (value : Complete initial native quantum allowance reverseLower reverseUpper current monitor) :
    value.actual.result.application = some (sender.other, value.start.reverseInitial.write.writer) := by
  rw [show value.start.reverseInitial.write.writer = value.start.boundary.write.operation from value.start.boundary.batchWriter]
  exact value.start.boundary.write.recorded

theorem Complete.forward_reader_retained (value : Complete initial native quantum allowance reverseLower reverseUpper current monitor) :
    value.forward.completed.reader ∈ current.report.steps :=
  (value.start.boundary.write.move.retained.trans value.reverse.completed.anchor.retained).subset value.forward.completed.member

theorem Complete.actual_write_retained (value : Complete initial native quantum allowance reverseLower reverseUpper current monitor) :
    value.actual ∈ current.report.steps :=
  value.reverse.completed.anchor.retained.subset value.start.boundary.write.move.member

theorem Complete.reverse_reader_retained (value : Complete initial native quantum allowance reverseLower reverseUpper current monitor) :
    value.reverse.completed.reader ∈ current.report.steps := value.reverse.completed.member

end Netlib.Check.CampusTCPTwoExchangeComplete
