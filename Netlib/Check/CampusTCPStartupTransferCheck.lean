import Netlib.Check.CampusTCPStartupNativeCheck
import Netlib.Check.CampusTCPStartupTransferObserved

/-!
# Checked native prerequisites for the actual startup and transfer prefix

Finite checks retain the original preparation, paths, storage, and loss budget.
Observed completion then supplies the same actual transfer history.
-/

namespace Netlib.Check.CampusTCPStartupTransferCheck

open Packet Protocol
namespace N
export CampusTCPStartupNativeCheck (verify profile dataPaths)
end N
namespace O
export CampusTCPStartupTransferObserved (preparation Result complete_at doneAt)
end O
namespace E
export CampusTCPStartupTransferExecution (actions initial)
end E

private def preparationEvent : CampusTCPModel.Event → Bool
  | .authentication _ | .install _ | .stage _ | .installGuard _
  | .installAt _ _ | .stageAt _ _ | .installGuardAt _ _ => true
  | _ => false

private theorem preparation_correct (event : CampusTCPModel.Event) :
    preparationEvent event = true ↔ CampusTCPStartupProfile.PreparationEvent event := by
  cases event <;> simp [preparationEvent, CampusTCPStartupProfile.PreparationEvent]

def rawReserves (input : CampusTCPModel.Input) (config : CampusTCPStartupTransferMonitor.Config) :
    Except String (PLift (CampusTCPRecoveredTransferTask.RawReserves input
      config.transfer.lower config.transfer.upper config.transfer.reverseLower config.transfer.reverseUpper)) := do
  let lower ← N.verify (config.transfer.lower ≠ []) "The original lower record is empty."
  let upper ← N.verify (config.transfer.upper ≠ []) "The original upper record is empty."
  let pending ← N.verify ((config.transfer.lower ++ config.transfer.upper).length ≤ input.active.pendingLimit)
    "The original forward write exceeds pending storage."
  let mss ← N.verify (config.transfer.lower.length + config.transfer.upper.length ≤
    TCP.Handshake.effectiveMSS input.active (TCP.Handshake.receiveOffer input.passive))
    "The original forward records exceed MSS."
  let capacity ← N.verify ((config.transfer.lower ++ config.transfer.upper).length ≤ input.passive.capacity)
    "The original forward records exceed receiver capacity."
  let reverseLower ← N.verify (config.transfer.reverseLower ≠ []) "The original reverse lower record is empty."
  let reverseUpper ← N.verify (config.transfer.reverseUpper ≠ []) "The original reverse upper record is empty."
  let reversePending ← N.verify ((config.transfer.reverseLower ++ config.transfer.reverseUpper).length ≤ input.passive.pendingLimit)
    "The original reverse write exceeds pending storage."
  let reverseMss ← N.verify (config.transfer.reverseLower.length + config.transfer.reverseUpper.length ≤
    TCP.Handshake.effectiveMSS input.passive (TCP.Handshake.receiveOffer input.active))
    "The original reverse records exceed MSS."
  let reverseCapacity ← N.verify ((config.transfer.reverseLower ++ config.transfer.reverseUpper).length ≤ input.active.capacity)
    "The original reverse records exceed receiver capacity."
  return ⟨⟨⟨lower.property, upper.property, pending.property, mss.property, capacity.property⟩,
    ⟨reversePending.property, reverseMss.property, reverseCapacity.property⟩,
    reverseLower.property, reverseUpper.property⟩⟩

structure CheckedReport (report : CampusTCPModel.Report input events)
    (config : CampusTCPStartupTransferMonitor.Config) (slot : Nat) where
  prepared : config.startup.preparation.length ≤ report.steps.length
  profile : CampusTCPStartupNative.Profile (input.contextFor .primary)
    (CampusTCPModel.beforeService input (O.preparation report config prepared).final .primary)
    input.zone (TCP.Handshake.outbound input.active config.startup.remote)
  paths : CampusTCPRecoveredNative.DataPaths
    (base := O.preparation report config prepared) config profile
  prep : CampusTCPStartupProfile.Prep config.startup
  raw : CampusTCPRecoveredTransferTask.RawReserves input
    config.transfer.lower config.transfer.upper config.transfer.reverseLower config.transfer.reverseUpper
  budget : config.transfer.lossAllowance ≤ 2
  namespaceEq : config.transfer.executionNS = (input.deployment .standby).executionNS
  result : Nonempty (O.Result config report slot)

def checkReport (report : CampusTCPModel.Report input events)
    (config : CampusTCPStartupTransferMonitor.Config) (slot : Nat) :
    Except String (CheckedReport report config slot) := do
  let prepared ← N.verify (config.startup.preparation.length ≤ report.steps.length)
    "The actual native preparation prefix is incomplete."
  let base := O.preparation report config prepared.property
  let paths : CampusTCPStartupNativeCheck.Paths :=
    ⟨⟨config.transfer.ingress .primary .client, CampusTCPModel.Actor.nextHop .client⟩,
      ⟨config.transfer.ingress .primary .server, CampusTCPModel.Actor.nextHop .server⟩⟩
  let profile ← N.profile (input.contextFor .primary) (CampusTCPModel.beforeService input base.final .primary)
    input.zone (TCP.Handshake.outbound input.active config.startup.remote) paths
  let dataPaths ← N.dataPaths base config profile
  let preparation ← N.verify (config.startup.preparation.all preparationEvent = true)
    "The original preparation contains a transport event."
  have prep : CampusTCPStartupProfile.Prep config.startup := by
    intro event member
    exact (preparation_correct event).mp (List.all_eq_true.mp preparation.property event member)
  let raw ← rawReserves input config
  let actions ← N.verify (E.actions config input.initial (E.initial config) report.steps = true)
    "The exact retained startup and transfer prefix fails its original action contract."
  let budget ← N.verify (config.transfer.lossAllowance ≤ 2) "The original loss profile exceeds two."
  let namespaceEq ← N.verify (config.transfer.executionNS = (input.deployment .standby).executionNS)
    "The original transfer selected another namespace lifetime."
  let within ← N.verify (slot ≤ report.steps.length) "The actual transfer cut is absent."
  let done ← N.verify (O.doneAt config report.steps slot = true)
    "The exact retained transfer prefix is unfinished."
  have completed := O.complete_at profile prep actions.property budget.property prepared.property dataPaths raw.down
    namespaceEq.property slot within.property done.property
  return ⟨prepared.property, profile, dataPaths, prep, raw.down, budget.property, namespaceEq.property, completed⟩

end Netlib.Check.CampusTCPStartupTransferCheck
