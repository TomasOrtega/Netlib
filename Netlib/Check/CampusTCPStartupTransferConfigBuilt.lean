import Netlib.Check.CampusTCPStartupTransferConfig
import Netlib.Check.CampusTCPRecoveredTwoWriteInitial
import Netlib.Check.CampusTCPTwoTransferLocatedCore

/-!
# The stored handoff configures the actual transfer task

The selected snapshot comes from the prepared report's retained archive.
Both initial intervals come from the actual endpoint recovery states.
-/

namespace Netlib.Check.CampusTCPStartupTransferConfigBuilt

open CampusTCPModel CampusTCPEnabled CampusTCPRecoveredSetup CampusTCPRecoveredSetupAppend
open CampusTCPStartupTransferConfig CampusTCPRecoveredTwoWriteInitial

namespace L
export CampusTCPTwoTransferLocatedCore (config)
end L
namespace N
export CampusTCPTwoTransferNative (Checks Routing)
end N
namespace E
export CampusTCPRecoveredTwoWriteEndpoints (cut)
end E

variable {input : Input} {events : List Event} {report : Report input events}
variable {ready : DrainReady report} {archive : RecoveryArchive input.active input.passive}

theorem Prepared.snapshot (drained : Drained ready archive) (config : CampusTCPStartupTransferConfig.Config)
    (value : Prepared drained.next (config.lower ++ config.upper)) :
    snapshot value.next.report.final = some ⟨archive, value.next.report.final.custody.dropped⟩ :=
  snapshot_of_archive _ value.next.archived

theorem Built.data_config (drained : Drained ready archive) (config : CampusTCPStartupTransferConfig.Config)
    (value : Prepared drained.next (config.lower ++ config.upper))
    (built : Built (lower := config.lower) (upper := config.upper) drained value)
    (checks : N.Checks (E.cut value) built.initial.gatewayState.session.entry)
    (routing : N.Routing (E.cut value) .primary)
    (ingress : checks.ingress = config.ingress)
    (namespaceEq : config.executionNS = (input.deployment .standby).executionNS) :
    config.data ⟨archive, value.next.report.final.custody.dropped⟩ =
      L.config built.initial checks routing config.quantum
        (config.lossAllowance - value.next.report.final.custody.dropped) config.reverseLower config.reverseUpper := by
  simp only [CampusTCPStartupTransferConfig.Config.data, CampusTCPStartupTransferConfig.Handoff.activeRTO,
    CampusTCPStartupTransferConfig.Handoff.passiveRTO, L.config,
    CampusTCPTwoTransferLocatedCore.sourceNative, CampusTCPTwoTransferNative.Checks.monitorConfig,
    CampusTCPTwoExchangeSetup.config, CampusTCPTwoProgressSetup.config,
    CampusTCPTwoTransferNative.Checks.native_env, built.senderTimer.2.1, built.receiverTimer.2.1,
    ingress, namespaceEq]

theorem Built.selected_config (drained : Drained ready archive) (config : CampusTCPStartupTransferConfig.Config)
    (value : Prepared drained.next (config.lower ++ config.upper))
    (built : Built (lower := config.lower) (upper := config.upper) drained value)
    (checks : N.Checks (E.cut value) built.initial.gatewayState.session.entry)
    (routing : N.Routing (E.cut value) .primary)
    (ingress : checks.ingress = config.ingress)
    (namespaceEq : config.executionNS = (input.deployment .standby).executionNS)
    (selected : snapshot value.next.report.final = some handoff) :
    config.data handoff = L.config built.initial checks routing config.quantum
      (config.lossAllowance - value.next.report.final.custody.dropped) config.reverseLower config.reverseUpper := by
  have same := Option.some.inj (selected.symm.trans (Prepared.snapshot drained config value))
  rw [same]
  exact Built.data_config drained config value built checks routing ingress namespaceEq

end Netlib.Check.CampusTCPStartupTransferConfigBuilt
