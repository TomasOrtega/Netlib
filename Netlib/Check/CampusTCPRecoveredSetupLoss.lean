import Netlib.Check.CampusTCPReportLoss
import Netlib.Check.CampusTCPRecoveredSetupAppend

/-!
# Retained loss allowance through recovery setup

Drain and endpoint setup add six actual slots and no loss events.
Later transfer uses the allowance left by the same startup report.
-/

namespace Netlib.Check.CampusTCPRecoveredSetupLoss

open CampusTCPModel CampusTCPRecoveredSetup CampusTCPRecoveredSetupAppend
open CampusTCPReportLoss

variable {input : Input} {events : List Event} {report : Report input events}
variable {ready : DrainReady report} {archive : RecoveryArchive input.active input.passive}
variable {start : Prefix input events archive} {bytes : List UInt8}

theorem Drained.retained (drained : Drained ready archive) : report.steps <+: drained.next.report.steps :=
  ⟨[drained.actual], drained.history.symm⟩

theorem Prepared.retained (value : Prepared start bytes) : start.report.steps <+: value.next.report.steps :=
  ⟨value.joints, value.history.symm⟩

theorem Prepared.joint_drop_ids (value : Prepared start bytes) : dropIDs value.joints = [] := by
  simp only [dropIDs, Prepared.joints, List.filterMap_cons, List.filterMap_nil, dropID,
    CampusTCPDropIDs.dropID, CampusTCPDropIDs.eventDropID,
    value.clientRecovery.eventEq, value.serverRecovery.eventEq, value.clientAck.eventEq,
    value.serverAck.eventEq, value.written.eventEq]

theorem Prepared.joint_drops (value : Prepared start bytes) : drops value.joints = 0 := by
  rw [← dropIDs_length, Prepared.joint_drop_ids value]
  rfl

theorem Drained.drop_count (drained : Drained ready archive) :
    drained.next.report.final.custody.dropped = report.final.custody.dropped := by
  rw [CampusTCPReportLoss.Report.drop_count, drained.history, drops_append,
    ← CampusTCPReportLoss.Report.drop_count report]
  simp only [drops, List.countP_cons, List.countP_nil, drained.event,
    CampusTCPCustodyFacts.dropEvent, Bool.false_eq_true, ite_false, Nat.add_zero]

theorem Prepared.drop_count (value : Prepared start bytes) :
    value.next.report.final.custody.dropped = start.report.final.custody.dropped := by
  rw [CampusTCPReportLoss.Report.drop_count, value.history, drops_append,
    Prepared.joint_drops value, Nat.add_zero, CampusTCPReportLoss.Report.drop_count]

theorem Drained.elapsed (drained : Drained ready archive) :
    drained.next.report.final.time = report.final.time + 1 := by
  rw [drained.final, drained.actual.clock, drained.before]

theorem Prepared.elapsed (value : Prepared start bytes) :
    value.next.report.final.time = start.report.final.time + 5 := by
  rw [Prepared.next, value.written.final, value.written.actual.clock, value.written.before,
    value.serverAck.final, value.serverAck.actual.clock, value.serverAck.before,
    value.clientAck.final, value.clientAck.actual.clock, value.clientAck.before,
    value.serverRecovery.final, value.serverRecovery.actual.clock, value.serverRecovery.before,
    value.clientRecovery.final, value.clientRecovery.actual.clock, value.clientRecovery.before]

theorem Prepared.whole_retained (drained : Drained ready archive) (value : Prepared drained.next bytes) :
    report.steps <+: value.next.report.steps :=
  (Drained.retained drained).trans (Prepared.retained value)

theorem Prepared.whole_elapsed (drained : Drained ready archive) (value : Prepared drained.next bytes) :
    value.next.report.final.time = report.final.time + 6 := by
  rw [Prepared.elapsed value, Drained.elapsed drained]

theorem Prepared.whole_drop_count (drained : Drained ready archive) (value : Prepared drained.next bytes) :
    value.next.report.final.custody.dropped = report.final.custody.dropped :=
  (Prepared.drop_count value).trans (Drained.drop_count drained)

theorem Prepared.remaining_allowance (drained : Drained ready archive) (value : Prepared drained.next bytes)
    (later : Report input laterEvents) (retained : value.next.report.steps <+: later.steps)
    (allowance : Nat) (bounded : later.final.custody.dropped ≤ allowance) :
    drops (later.steps.drop value.next.report.steps.length) ≤ allowance - report.final.custody.dropped := by
  have remaining := CampusTCPReportLoss.Report.remaining_allowance value.next.report later retained allowance bounded
  rw [Prepared.whole_drop_count drained value] at remaining
  exact remaining

end Netlib.Check.CampusTCPRecoveredSetupLoss
