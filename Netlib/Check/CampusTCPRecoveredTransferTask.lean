import Netlib.Check.CampusTCPRecoveredForwardRaw
import Netlib.Check.CampusTCPRecoveredReverseRaw
import Netlib.Check.CampusTCPRecoveredTransferFrames
import Netlib.Check.CampusTCPRecoveredSetupLoss
import Netlib.Check.CampusTCPTwoTransferNative

/-!
# Both transfer directions at the actual recovered cut

Original byte bounds supply both reverse reserve records.
The task keeps the actual drain, setup operations, writer, and loss ledger.
-/

namespace Netlib.Check.CampusTCPRecoveredTransferTask

open Protocol.TCP CampusTCPModel CampusTCPRecoveredSetup CampusTCPRecoveredSetupAppend
open CampusTCPRecoveryStartupCold CampusTCPRecoveryStartupTransport

namespace E
export CampusTCPRecoveredTwoWriteEndpoints (cut)
end E
namespace I
export CampusTCPRecoveredTwoWriteInitial (Built)
end I

structure RawReserves (input : Input) (lower upper reverseLower reverseUpper : List UInt8) : Prop where
  forward : CampusTCPRecoveredForwardRaw.RawReserves input lower upper
  reverse : CampusTCPRecoveredReverseReserves.RawReserves input reverseLower reverseUpper
  reverseLowerNonempty : reverseLower ≠ []
  reverseUpperNonempty : reverseUpper ≠ []

variable {input : Input} {events : List Event} {report : Report input events}
variable {ready : DrainReady report} {lower upper reverseLower reverseUpper : List UInt8}

structure Task (ready : DrainReady report) (lower upper reverseLower reverseUpper : List UInt8) where
  archive : RecoveryArchive input.active input.passive
  drained : Drained ready archive
  prepared : Prepared drained.next (lower ++ upper)
  built : I.Built drained prepared
  reverseEndpoints : CampusTCPTwoReverseReserves.Initial built.initial reverseLower reverseUpper
  reverseGateway : CampusTCPTwoReverseGeometry.Initial built.initial reverseLower reverseUpper
  reverseLowerNonempty : reverseLower ≠ []
  reverseUpperNonempty : reverseUpper ≠ []
  primaryEmpty : (E.cut prepared).report.final.outstanding .primary = 0
  standbyEmpty : (E.cut prepared).report.final.standby.transport = Checkpoint.Gateway.initial

theorem prepare (ready : DrainReady report) (raw : RawReserves input lower upper reverseLower reverseUpper)
    (cold : ColdProfile report) (primary : PrimaryServices report) :
    Nonempty (Task ready lower upper reverseLower reverseUpper) := by
  obtain ⟨archive, drained, value, ⟨built⟩⟩ := CampusTCPRecoveredForwardRaw.setup ready raw.forward cold primary
  obtain ⟨endpoints, gateway⟩ := CampusTCPRecoveredReverseReserves.both_of_raw drained value built raw.reverse
  exact ⟨⟨archive, drained, value, built, endpoints, gateway, raw.reverseLowerNonempty, raw.reverseUpperNonempty,
    CampusTCPRecoveredTransferFrames.Prepared.primary_empty drained value cold,
    CampusTCPRecoveredTransferFrames.Prepared.standby_initial drained value cold primary⟩⟩

variable (task : Task ready lower upper reverseLower reverseUpper)

theorem Task.retained : report.steps <+: (E.cut task.prepared).report.steps :=
  CampusTCPRecoveredSetupLoss.Prepared.whole_retained task.drained task.prepared

theorem Task.elapsed : (E.cut task.prepared).report.final.time = report.final.time + 6 :=
  CampusTCPRecoveredSetupLoss.Prepared.whole_elapsed task.drained task.prepared

theorem Task.drop_count :
    (E.cut task.prepared).report.final.custody.dropped = report.final.custody.dropped :=
  CampusTCPRecoveredSetupLoss.Prepared.whole_drop_count task.drained task.prepared

theorem Task.target_namespace
    (checks : CampusTCPTwoTransferNative.Checks (E.cut task.prepared) task.built.initial.gatewayState.session.entry) :
    (E.cut task.prepared).report.final.standby.guard.source.ns = (input.deployment .standby).executionNS := by
  let current := (checks.paths .standby .client).checks
  exact (congrArg (fun source => source.ns) current.guardSource).symm.trans current.guard.namespaceEq

end Netlib.Check.CampusTCPRecoveredTransferTask
