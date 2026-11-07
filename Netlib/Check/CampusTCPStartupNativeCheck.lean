import Netlib.Check.CampusTCPStartupNative
import Netlib.Check.CampusTCPRecoveredNative

/-!
# Executable native startup prerequisites

Checks use the actual stored policy, candidate, and interface lifetimes.
Both directions and gateways are checked before packet service.
-/

namespace Netlib.Check.CampusTCPStartupNativeCheck

open Packet Protocol CampusTCPService

def verify (condition : Prop) [Decidable condition] (message : String) :
    Except String { _value : Unit // condition } :=
  if accepted : condition then .ok ⟨(), accepted⟩ else .error message

private def witnessed (value : Except String α) : Except String { result : α // value = .ok result } :=
  match value with
  | .error reason => .error reason
  | .ok result => .ok ⟨result, rfl⟩

private theorem ingress_source (value : IngressGuard.Checked now executionNS expected maintenance application)
    (computed : IngressGuard.check now executionNS expected maintenance application source budget = .ok value) :
    value.source = source := by
  unfold IngressGuard.check at computed
  repeat' first
    | (cases computed; rfl)
    | (split at computed <;> try simp [bind, Except.bind, pure, throw] at computed)

def checks (context : CampusTCPService.Context) (before : Before) (ingress : I.InterfaceRef) :
    Except String (Checks context before ingress) := do
  let afterBound ← verify (before.after ≤ context.authentication.observations.length)
    "The native startup authentication prefix is out of bounds."
  let live ← verify (ingress ∈ before.live) "The native startup ingress lifetime is not current."
  let namespaceEq ← verify (ingress.ns = context.executionNS) "The native startup namespace lifetime differs."
  let forward ← witnessed (SessionInstallation.check context.authentication context.requirements before.after
    (active context before) context.configs 100000)
  let guard ← witnessed (IngressGuard.check (current context before) context.executionNS before.attachments []
    context.application before.guard 100000)
  return ⟨afterBound.property, live.property, namespaceEq.property, 100000,
    forward.val, forward.property, guard.val, guard.property, ingress_source guard.val guard.property⟩

structure Route where
  ingress : I.InterfaceRef
  hop : String

structure Paths where
  original : Route
  reply : Route

def Paths.get (paths : Paths) : FlowNAT.Direction → Route
  | .original => paths.original
  | .reply => paths.reply

def path (context : CampusTCPService.Context) (before : Before) (entry : NetfilterNAT.Entry)
    (direction : FlowNAT.Direction) (route : Route) :
    Except String { value : CampusTCPStartupNative.Path context before entry direction //
      value.ingress = route.ingress ∧ value.hop = route.hop } := do
  let checks ← checks context before route.ingress
  let budget ← verify (checks.budget = 100000) "The native startup check budget differs."
  let forwardComparison ← verify (checks.forward.passed = true) "The native startup forward comparison failed."
  let guardComparison ← verify (checks.guard.passed = true) "The native startup ingress comparison failed."
  let ingressPermit ← verify (before.guard.permits route.ingress.ifindex.val (entry.flow.input direction) = true)
    "The stored native ingress policy denies this startup path."
  let covered ← verify (context.application.any (·.accepts (entry.flow.input direction)) = true)
    "The native startup input is outside the application classes."
  let routed ← verify (Routing.nextHop (before.configuration.pipeline context.routing).routes
    ((ConntrackLifecycle.destinationStage entry direction).apply (entry.flow.input direction)).destination = some route.hop)
    "The native startup route differs from the declared hop."
  let forward ← verify (StatefulACL.Policy.evaluate (before.configuration.pipeline context.routing).forwardDefault
    (before.configuration.pipeline context.routing).forward .established
    ((ConntrackLifecycle.destinationStage entry direction).apply (entry.flow.input direction)) = .permit)
    "The native startup established forward policy denies this path."
  let late ← verify (StatefulACL.Policy.evaluate (before.configuration.pipeline context.routing).lateDefault
    (before.configuration.pipeline context.routing).late .established
    ((ConntrackLifecycle.sourceStage entry direction).apply
      ((ConntrackLifecycle.destinationStage entry direction).apply (entry.flow.input direction))) = .permit)
    "The native startup established late policy denies this path."
  return ⟨⟨route.ingress, route.hop, checks, budget.property, forwardComparison.property, guardComparison.property,
    ingressPermit.property, covered.property, routed.property, forward.property, late.property⟩, rfl, rfl⟩

def profile (context : CampusTCPService.Context) (before : Before) (zone : Nat) (header : Header) (paths : Paths) :
    Except String (CampusTCPStartupNative.Profile context before zone header) := do
  let entry := CampusTCPStartupNative.selectedEntry before zone header
  let zoneBound ← verify (zone < 65536) "The native startup zone is out of bounds."
  let compatible ← verify entry.Compatible "The native startup candidate is incompatible."
  let original ← verify (entry.flow.original = header) "The native startup candidate has another original tuple."
  let originalZone ← verify (entry.flow.originalZone = zone) "The native startup original zone differs."
  let replyZone ← verify (entry.flow.replyZone = zone) "The native startup reply zone differs."
  let trackerValid ← verify before.tracker.Valid "The native startup tracker is invalid."
  let fresh ← verify (before.tracker.model.keys.all (fun key =>
    decide (key ≠ entry.flow.key .original) && decide (key ≠ entry.flow.key .reply)) = true)
    "The native startup candidate keys are already present."
  have freshKeys : ConntrackLifecycle.FreshKeys before.tracker entry := by
    constructor
    · intro member
      have denied : entry.flow.key .original ≠ entry.flow.key .original ∧
          entry.flow.key .original ≠ entry.flow.key .reply := by
        simpa only [Bool.and_eq_true, decide_eq_true_eq] using List.all_eq_true.mp fresh.property _ member
      exact denied.1 rfl
    · intro member
      have denied : entry.flow.key .reply ≠ entry.flow.key .original ∧
          entry.flow.key .reply ≠ entry.flow.key .reply := by
        simpa only [Bool.and_eq_true, decide_eq_true_eq] using List.all_eq_true.mp fresh.property _ member
      exact denied.2 rfl
  let empty ← verify (before.admission.phase.entry.isNone = true) "The native startup admission state is not empty."
  have emptyPhase : before.admission.phase = .empty := by
    have absent := empty.property
    cases phase : before.admission.phase <;> simp_all only [TCP.Admission.Phase.entry, Option.isNone_some,
      Bool.false_eq_true]
  let originalPath ← path context before entry .original paths.original
  let replyPath ← path context before entry .reply paths.reply
  let newForward ← verify (StatefulACL.Policy.evaluate (before.configuration.pipeline context.routing).forwardDefault
    (before.configuration.pipeline context.routing).forward .new
    ((ConntrackLifecycle.destinationStage entry .original).apply entry.flow.original) = .permit)
    "The native startup new forward policy denies the candidate."
  let newLate ← verify (StatefulACL.Policy.evaluate (before.configuration.pipeline context.routing).lateDefault
    (before.configuration.pipeline context.routing).late .new
    ((ConntrackLifecycle.sourceStage entry .original).apply
      ((ConntrackLifecycle.destinationStage entry .original).apply entry.flow.original)) = .permit)
    "The native startup new late policy denies the candidate."
  return ⟨zoneBound.property, compatible.property, original.property, originalZone.property, replyZone.property,
    trackerValid.property, freshKeys, emptyPhase,
    (fun direction => match direction with | .original => originalPath.val | .reply => replyPath.val),
    newForward.property, newLate.property⟩

def dataPaths {input : CampusTCPModel.Input} {events : List CampusTCPModel.Event}
    (base : CampusTCPModel.Report input events) (config : CampusTCPStartupTransferMonitor.Config)
    (profile : CampusTCPStartupNative.Profile (input.contextFor .primary)
      (CampusTCPModel.beforeService input base.final .primary) input.zone header) :
    Except String (CampusTCPRecoveredNative.DataPaths (base := base) config profile) := do
  let primaryClientIngress ← verify ((profile.paths .original).ingress = config.transfer.ingress .primary .client)
    "The primary client startup and transfer ingress lifetimes differ."
  let primaryServerIngress ← verify ((profile.paths .reply).ingress = config.transfer.ingress .primary .server)
    "The primary server startup and transfer ingress lifetimes differ."
  let primaryClientHop ← verify ((profile.paths .original).hop = CampusTCPModel.Actor.nextHop .client)
    "The primary client startup and transfer hops differ."
  let primaryServerHop ← verify ((profile.paths .reply).hop = CampusTCPModel.Actor.nextHop .server)
    "The primary server startup and transfer hops differ."
  let client ← path (input.contextFor .standby) (CampusTCPModel.beforeService input base.final .standby)
    profile.entry .original ⟨config.transfer.ingress .standby .client, CampusTCPModel.Actor.nextHop .client⟩
  let server ← path (input.contextFor .standby) (CampusTCPModel.beforeService input base.final .standby)
    profile.entry .reply ⟨config.transfer.ingress .standby .server, CampusTCPModel.Actor.nextHop .server⟩
  let primaryConfigured ← verify (input.configured .primary = true) "The primary native deployment is absent."
  let standbyConfigured ← verify (input.configured .standby = true) "The standby native deployment is absent."
  return {
    primary := {
      ingress := fun side => by cases side; exact primaryClientIngress.property; exact primaryServerIngress.property
      hop := fun side => by cases side; exact primaryClientHop.property; exact primaryServerHop.property }
    standby := fun actor => match actor with | .client => client.val | .server => server.val
    ingress := fun actor => by cases actor; exact client.property.1; exact server.property.1
    hop := fun actor => by cases actor; exact client.property.2; exact server.property.2
    configured := fun gateway => by cases gateway; exact primaryConfigured.property; exact standbyConfigured.property }

end Netlib.Check.CampusTCPStartupNativeCheck
