import Netlib.Check.CampusTCPStartupEntryTask
import Netlib.Check.CampusTCPStartupCurrentAt
import Netlib.Check.CampusTCPRecoveredNative

/-!
# Native paths for the actual data entry

The entry's retained preparation and drive histories derive both deployments'
checks and current routing for the same actual setup task.
-/

namespace Netlib.Check.CampusTCPStartupEntryNative

open Protocol.TCP CampusTCPModel CampusTCPStartupEntry

namespace E
export CampusTCPStartupTransferExecution (initial actions)
end E
namespace R
export CampusTCPStartupEntryTask (Realized)
end R
namespace N
export CampusTCPTwoTransferNative (Checks Routing)
end N
namespace C
export CampusTCPRecoveredTwoWriteEndpoints (cut)
end C

variable {input : Input} {events : List CampusTCPModel.Event}
variable {config : CampusTCPStartupTransferMonitor.Config} {whole : Report input events} {slot : Nat}

theorem Entry.preparation_within (entry : Entry config whole slot) :
    config.startup.preparation.length ≤ whole.steps.length := by
  obtain ⟨located⟩ := CampusTCPStartupSetupInterval.locate entry
  have before := CampusTCPStartupOpening.preparation_before located.within located.before located.mode
  exact Nat.le_trans (Nat.le_of_lt before) located.within

def preparation (entry : Entry config whole slot) : Report input ((whole.steps.take config.startup.preparation.length).map (·.event)) :=
  CampusTCPSchedule.Report.cut whole config.startup.preparation.length (Entry.preparation_within entry)

structure Native (entry : Entry config whole slot) where
  realized : R.Realized entry
  checks : N.Checks (C.cut realized.task.prepared) realized.task.built.initial.gatewayState.session.entry
  routing : N.Routing (C.cut realized.task.prepared) .primary
  ingress : checks.ingress = config.transfer.ingress

variable (profile : CampusTCPStartupNative.Profile (input.contextFor .primary)
  (beforeService input (CampusTCPSchedule.stateAt input.initial whole.steps config.startup.preparation.length) .primary)
  input.zone (Handshake.outbound input.active config.startup.remote))

theorem from_entry (entry : Entry config whole slot) (prep : CampusTCPStartupProfile.Prep config.startup)
    (actions : E.actions config input.initial (E.initial config) whole.steps = true)
    (paths : CampusTCPRecoveredNative.DataPaths (base := preparation entry) config profile)
    (raw : CampusTCPRecoveredTransferTask.RawReserves input config.transfer.lower config.transfer.upper
      config.transfer.reverseLower config.transfer.reverseUpper) : Nonempty (Native entry) := by
  obtain ⟨realized⟩ := CampusTCPStartupEntryTask.from_entry entry prep actions raw
  obtain ⟨located⟩ := CampusTCPStartupCurrentAt.at_drive profile prep actions realized.located.within
    realized.located.before realized.located.mode
  let checks := CampusTCPRecoveredNative.Built.checks located.history located.value paths realized.task.drained
    realized.task.prepared realized.task.built
  exact ⟨⟨realized, checks,
    CampusTCPRecoveredNative.Built.routing located.value realized.task.drained realized.task.prepared realized.task.built,
    rfl⟩⟩

end Netlib.Check.CampusTCPStartupEntryNative
