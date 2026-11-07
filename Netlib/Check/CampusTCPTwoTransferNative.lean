import Netlib.Check.CampusTCPTwoTransferState
import Netlib.Check.CampusTCPTwoProgressReframe
import Netlib.Check.CampusTCPTwoTransferMonitor

/-!
# Native checks for both actual deployments

Each gateway keeps its own ingress, policy, guard, and namespace checks.
The current routing facts select those checks without changing the source entry.
-/

namespace Netlib.Check.CampusTCPTwoTransferNative

open Packet Protocol CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart
open CampusTCPTwoTransferState (Retained)

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current next : Cut input complete} {entry : NetfilterNAT.Entry} {gateway : Gateway}

structure Checks (cut : Cut input complete) (entry : NetfilterNAT.Entry) where
  ingress : Gateway → Actor → I.InterfaceRef
  paths : ∀ gateway actor, CampusTCPRoundGateway.Native (input.contextFor gateway)
    (beforeService input cut.report.final gateway) (ingress gateway actor) entry actor.direction actor.nextHop
  configured : ∀ gateway, input.configured gateway = true

structure Routing (current : Cut input complete) (gateway : Gateway) : Prop where
  owners : ∀ actor, current.report.final.owner actor = gateway
  unpaused : current.report.final.assignmentPaused = false
  primary : gateway = .primary → current.report.final.primarySealed = false ∧ current.report.final.primaryFenced = false
  standby : gateway = .standby → ∃ installation : InstalledCheckpoint,
    current.report.final.installation = some installation ∧
      current.report.final.primarySealed = true ∧ current.report.final.primaryFenced = true

theorem Routing.ofNative (native : NativeEnv current gateway entry) : Routing current gateway :=
  ⟨native.owners, native.unpaused, native.primary, native.standby⟩

def Checks.reframe (checks : Checks cut entry) (retained : Retained cut current) : Checks current entry where
  ingress := checks.ingress
  paths := fun gateway actor => CampusTCPTwoProgressReframe.native_path (checks.paths gateway actor)
    _ (retained.policy gateway)
  configured := checks.configured

@[simp] theorem Checks.reframe_ingress (checks : Checks cut entry) (retained : Retained cut current) :
    (checks.reframe retained).ingress = checks.ingress := rfl

def Checks.native_env (checks : Checks cut entry) (retained : Retained cut current)
    (routing : Routing current gateway) : NativeEnv current gateway entry where
  ingress := checks.ingress gateway
  paths := (checks.reframe retained).paths gateway
  configured := checks.configured gateway
  owners := routing.owners
  unpaused := routing.unpaused
  primary := routing.primary
  standby := routing.standby

theorem Checks.route (checks : Checks cut entry) (retained : Retained cut current)
    (routing : Routing current gateway) (actor : Actor) : RouteReady current.report.final actor :=
  (checks.native_env retained routing).route actor

theorem Checks.service_phase (checks : Checks cut entry) (retained : Retained cut current)
    (routing : Routing current gateway) : CampusTCPGatewayEnabled.ServicePhaseReady current.report.final gateway :=
  (checks.native_env retained routing).service_phase

def Checks.monitorConfig (checks : Checks cut entry) (exchange : CampusTCPTwoExchangeMonitor.Config) :
    CampusTCPTwoTransferMonitor.Config :=
  ⟨exchange, checks.ingress, (input.deployment .standby).executionNS⟩

theorem Checks.monitor_ingress (checks : Checks cut entry)
    (routing : Routing current gateway) (actor : Actor) :
    checks.ingress (current.report.final.owner actor) actor = checks.ingress gateway actor := by
  rw [routing.owners actor]

end Netlib.Check.CampusTCPTwoTransferNative
