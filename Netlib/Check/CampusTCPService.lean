import Netlib.Check.SessionInstallation
import Netlib.Check.IngressGuard
import Netlib.Protocol.TCP.Admission
import Netlib.Protocol.TCP.WireForwarding

/-!
# Current campus policy at TCP service

The actual installed ingress and forward policies control packet processing.
Comparison results do not replace those decisions.
One preparation supplies the attachment to TCP admission and wire forwarding.
The TCP admission history does not prove Linux tracker acceptance.
-/

namespace Netlib.Check.CampusTCPService

open Packet Protocol
namespace I
export Protocol.IngressAttachment (Current NamespaceRef InterfaceRef ExpectedAttachment)
end I
namespace W
export Protocol.TCP.WireForwarding (Source Input Outcome Emission)
end W

abbrev Config := Check.ConntrackLifecycle.Config

structure Context where
  authentication : Check.EAP.Input
  requirements : List Compile.SessionFirewall.Intent
  routing : Import.LinuxRoute.Snapshot
  configs : List Config
  executionNS : I.NamespaceRef
  application : List Match

structure Before where
  after : Nat
  configuration : Config
  guard : Import.NftablesIngress.Snapshot
  live : List I.InterfaceRef
  attachments : List I.ExpectedAttachment
  tracker : Protocol.ConntrackLifecycle.State
  admission : TCP.Admission.State

def current (context : Context) (before : Before) : I.Current :=
  ⟨context.authentication.context, before.after,
    Check.SessionFirewall.stateAt context.authentication before.after, before.live⟩

theorem current_safe (context : Context) (before : Before) : (current context before).Safe :=
  Check.SessionFirewall.stateAt_safe _ _

def active (context : Context) (before : Before) : Protocol.SafeHandoff.Configuration :=
  ⟨before.configuration.id, before.configuration.pipeline context.routing⟩

def packetInput (before : Before) (source : W.Source) (zone : Nat) : W.Input :=
  ⟨zone, source.packet,
    if (before.tracker.model.lookup zone source.packet.header).isNone then
      some (before.configuration.nat.candidate zone source.packet.header) else none⟩

def coverage (context : Context) (source : W.Source) : Bool :=
  context.application.any (·.accepts source.packet.header)

theorem coverage_correct (context : Context) (source : W.Source) :
    coverage context source = true ↔ ∃ traffic ∈ context.application, traffic.Holds source.packet.header := by
  simp only [coverage, List.any_eq_true, Match.accepts_iff]

structure Checks (context : Context) (before : Before) (ingress : I.InterfaceRef) where
  afterBound : before.after ≤ context.authentication.observations.length
  currentLive : ingress ∈ before.live
  namespaceEq : ingress.ns = context.executionNS
  budget : Nat
  forward : SessionInstallation.Checked context.authentication context.requirements before.after (active context before)
  forwardComputed : SessionInstallation.check context.authentication context.requirements before.after
    (active context before) context.configs budget = .ok forward
  guard : IngressGuard.Checked (current context before) context.executionNS before.attachments [] context.application
  guardComputed : IngressGuard.check (current context before) context.executionNS before.attachments []
    context.application before.guard budget = .ok guard
  guardSource : guard.source = before.guard

def Checks.decision (checks : Checks context before ingress) (source : W.Source) : Bool :=
  checks.guard.decision ⟨ingress, source.packet.header⟩

structure Processing (context : Context) (before : Before) (source : W.Source) (zone : Nat) where
  prepared : Protocol.ConntrackLifecycle.Prepared (packetInput before source zone).lifecycle
  attached : Protocol.ConntrackLifecycle.prepare before.tracker (packetInput before source zone).lifecycle = .ok prepared
  admitted : TCP.Admission.Result before.admission source.asInput (packetInput before source zone).lifecycle prepared
  admissionComputed : TCP.Admission.step before.admission source.asInput (packetInput before source zone).lifecycle
    prepared rfl = .ok admitted
  outcome : W.Outcome source.packet
  computed : TCP.WireForwarding.process (before.configuration.pipeline context.routing) (packetInput before source zone)
    source.valid prepared = .ok outcome
  nextAdmission : TCP.Admission.State
  committed : TCP.Admission.commit admitted outcome.state = .ok nextAdmission

inductive Operation (context : Context) (before : Before) (source : W.Source) (zone : Nat)
    (ingress : I.InterfaceRef) (checks : Checks context before ingress) where
  | earlyDrop (denied : checks.decision source = false)
  | processed (permitted : checks.decision source = true) (processing : Processing context before source zone)

structure Evidence (context : Context) (before : Before) (source : W.Source) (zone : Nat) (ingress : I.InterfaceRef) where
  checks : Checks context before ingress
  operation : Operation context before source zone ingress checks

def Evidence.passed (value : Evidence context before source zone ingress) : Bool :=
  value.checks.forward.passed && value.checks.guard.passed && coverage context source

def Evidence.processing (value : Evidence context before source zone ingress) : Option (Processing context before source zone) :=
  match value.operation with
  | .earlyDrop _ => none
  | .processed _ processing => some processing

def Evidence.tracker (value : Evidence context before source zone ingress) : Protocol.ConntrackLifecycle.State :=
  match value.operation with
  | .earlyDrop _ => before.tracker
  | .processed _ processing => processing.outcome.state

def Evidence.admission (value : Evidence context before source zone ingress) : TCP.Admission.State :=
  match value.operation with
  | .earlyDrop _ => before.admission
  | .processed _ processing => processing.nextAdmission

def Evidence.output (value : Evidence context before source zone ingress) : Option (W.Emission source.packet) :=
  match value.operation with
  | .earlyDrop _ => none
  | .processed _ processing => processing.outcome.output

inductive Error where
  | input (reason : String)
  | unsupported (reason : TCP.Admission.Unsupported)
  deriving Repr, BEq, DecidableEq

def Error.message : Error → String
  | .input reason => reason
  | .unsupported reason => (TCP.Admission.Error.unsupported reason).message

def admissionError : TCP.Admission.Error → Error
  | .unsupported reason => .unsupported reason

private def checked (value : Except String α) : Except Error { result : α // value = .ok result } :=
  match value with
  | .error reason => .error (.input reason)
  | .ok result => .ok ⟨result, rfl⟩

private theorem ingress_source (value : IngressGuard.Checked now executionNS attachments maintenance application)
    (computed : IngressGuard.check now executionNS attachments maintenance application source budget = .ok value) :
    value.source = source := by
  unfold IngressGuard.check at computed
  repeat' first
    | (cases computed; rfl)
    | (split at computed <;> try simp [bind, Except.bind, pure, throw] at computed)

def run (context : Context) (before : Before) (source : W.Source) (zone : Nat) (ingress : I.InterfaceRef)
    (budget : Nat := 100000) : Except Error (Evidence context before source zone ingress) := do
  if afterBound : before.after ≤ context.authentication.observations.length then
    if currentLive : ingress ∈ before.live then
      if namespaceEq : ingress.ns = context.executionNS then
        let forward ← checked (SessionInstallation.check context.authentication context.requirements before.after
          (active context before) context.configs budget)
        let guard ← checked (IngressGuard.check (current context before) context.executionNS before.attachments []
          context.application before.guard budget)
        let checks : Checks context before ingress :=
          ⟨afterBound, currentLive, namespaceEq, budget, forward.val, forward.property, guard.val, guard.property,
            ingress_source guard.val guard.property⟩
        if permitted : checks.decision source then
          match attached : Protocol.ConntrackLifecycle.prepare before.tracker (packetInput before source zone).lifecycle with
          | .error reason => throw (.input reason.describe)
          | .ok prepared =>
            match admitted : TCP.Admission.step before.admission source.asInput (packetInput before source zone).lifecycle prepared rfl with
            | .error reason => throw (admissionError reason)
            | .ok admission =>
              match computed : TCP.WireForwarding.process (before.configuration.pipeline context.routing)
                  (packetInput before source zone) source.valid prepared with
              | .error reason => throw (.input reason.describe)
              | .ok outcome =>
                match committed : TCP.Admission.commit admission outcome.state with
                | .error reason => throw (admissionError reason)
                | .ok nextAdmission =>
                  return ⟨checks, .processed permitted ⟨prepared, attached, admission, admitted, outcome, computed,
                    nextAdmission, committed⟩⟩
        else return ⟨checks, .earlyDrop (by cases actual : checks.decision source <;> simp_all)⟩
      else throw (.input "The ingress belongs to a different namespace lifetime.")
    else throw (.input "The ingress interface lifetime is not current.")
  else throw (.input "The service prefix exceeds the actual authentication history.")


theorem Checks.actual_decision (checks : Checks context before ingress) (source : W.Source) :
    checks.decision source = before.guard.permits ingress.ifindex.val source.packet.header := by
  unfold Checks.decision IngressGuard.Checked.decision
  rw [checks.guardSource]

theorem Evidence.passed_parts (value : Evidence context before source zone ingress) (passed : value.passed = true) :
    value.checks.forward.passed = true ∧ value.checks.guard.passed = true ∧ coverage context source = true := by
  simpa only [Evidence.passed, Bool.and_eq_true, and_assoc] using passed

theorem Evidence.processed_of_output (value : Evidence context before source zone ingress)
    (emission : W.Emission source.packet) (output : value.output = some emission) :
    ∃ processing, value.processing = some processing ∧ processing.outcome.output = some emission := by
  cases selected : value.operation with
  | earlyDrop denied => simp only [Evidence.output, selected, reduceCtorEq] at output
  | processed permitted processing =>
    exact ⟨processing, by simp only [Evidence.processing, selected],
      by simpa only [Evidence.output, selected] using output⟩

theorem Evidence.ingress_permitted (value : Evidence context before source zone ingress)
    (emission : W.Emission source.packet) (output : value.output = some emission) :
    value.checks.decision source = true := by
  cases selected : value.operation with
  | earlyDrop denied => simp only [Evidence.output, selected, reduceCtorEq] at output
  | processed permitted processing => exact permitted

theorem Evidence.early_preserves (value : Evidence context before source zone ingress)
    (denied : value.checks.decision source = false) :
    value.tracker = before.tracker ∧ value.admission = before.admission ∧ value.output = none := by
  cases selected : value.operation with
  | earlyDrop blocked => simp only [Evidence.tracker, Evidence.admission, Evidence.output, selected, and_self]
  | processed permitted processing => simp only [denied, Bool.false_eq_true] at permitted

theorem Processing.wire_step (value : Processing context before source zone) :
    TCP.WireForwarding.step (before.configuration.pipeline context.routing) before.tracker
      (packetInput before source zone) = .ok value.outcome :=
  TCP.WireForwarding.step_of_process _ _ _ source.bytes source.encoded source.valid value.prepared value.attached
    value.outcome value.computed

theorem Processing.current_permission (value : Processing context before source zone)
    (checks : Checks context before ingress) (passed : checks.forward.passed = true)
    (emission : W.Emission source.packet) (emitted : value.outcome.output = some emission) :
    ∃ requirement ∈ context.requirements, requirement.test.Holds value.outcome.afterDestination ∧
      Session.Valid context.authentication.context (current context before).state.session requirement.scope ∧
      EAPAuth.State.Ready (EAPSession.authContext context.authentication.context) (current context before).state.auth := by
  obtain ⟨model, computed, output, destination, _, _, _⟩ :=
    TCP.WireForwarding.step_output _ _ _ _ value.wire_step emission emitted
  have permission := Examples.SessionFirewallDeployment.output_current_permission checks.forward.compiled
    (Check.SessionFirewall.stateAt_safe context.authentication before.after) _ (checks.forward.forward_equivalent passed)
    before.tracker (packetInput before source zone).lifecycle model emission.target computed output
  rw [← destination] at permission
  exact permission

theorem Evidence.current_permission (value : Evidence context before source zone ingress) (passed : value.passed = true)
    (emission : W.Emission source.packet) (output : value.output = some emission) :
    ∃ processing, value.processing = some processing ∧
      ∃ requirement ∈ context.requirements, requirement.test.Holds processing.outcome.afterDestination ∧
        Session.Valid context.authentication.context (current context before).state.session requirement.scope ∧
        EAPAuth.State.Ready (EAPSession.authContext context.authentication.context) (current context before).state.auth := by
  obtain ⟨processing, selected, emitted⟩ := value.processed_of_output emission output
  exact ⟨processing, selected, processing.current_permission value.checks (value.passed_parts passed).1 emission emitted⟩

theorem Evidence.ingress_permission (value : Evidence context before source zone ingress) (passed : value.passed = true)
    (emission : W.Emission source.packet) (output : value.output = some emission) :
    ∃ attachment ∈ before.attachments,
      IngressAttachment.allows (current context before) attachment ⟨ingress, source.packet.header⟩ = true ∧
      Session.Valid context.authentication.context (current context before).state.session attachment.scope ∧
      EAPAuth.State.Ready (EAPSession.authContext context.authentication.context) (current context before).state.auth ∧
      ingress = attachment.ingress ∧ attachment.origin.principal = context.authentication.context.consumer := by
  exact value.checks.guard.application_permission (current_safe context before) (value.passed_parts passed).2.1
    ⟨ingress, source.packet.header⟩ value.checks.currentLive value.checks.namespaceEq
    ((coverage_correct context source).mp (value.passed_parts passed).2.2) (value.ingress_permitted emission output)

theorem Evidence.bytePath (value : Evidence context before source zone ingress)
    (emission : W.Emission source.packet) (_output : value.output = some emission) :
    TCP.ApplicationTrace.BytePath source.asInput emission.asInput := emission.bytePath source

theorem Evidence.output_none_of_denied (value : Evidence context before source zone ingress) (passed : value.passed = true)
    (denied : ∀ requirement ∈ context.requirements,
      (current context before).state.session.permits context.authentication.context requirement.scope = false) :
    value.output = none := by
  cases emitted : value.output with
  | none => rfl
  | some emission =>
    obtain ⟨processing, selected, requirement, member, matched, valid, ready⟩ := value.current_permission passed emission emitted
    have permitted := (Session.permits_iff _ _ _).mpr valid
    simp only [denied requirement member, Bool.false_eq_true] at permitted

theorem Evidence.output_none_of_unauthorized (value : Evidence context before source zone ingress) (passed : value.passed = true)
    (unauthorized : (current context before).state.auth.authorized = false) : value.output = none := by
  apply value.output_none_of_denied passed
  intro requirement member
  exact EAPSession.unauthorized_denied context.authentication.context (current context before).state requirement.scope
    (current_safe context before).2.1 unauthorized

theorem Evidence.output_none_without_credential (value : Evidence context before source zone ingress) (passed : value.passed = true)
    (missing : (current context before).state.session.credential = none) : value.output = none := by
  apply value.output_none_of_denied passed
  intro requirement member
  simp only [Session.permits, Session.claims, missing, Bool.and_false]

theorem Evidence.output_facts (value : Evidence context before source zone ingress)
    (emission : W.Emission source.packet) (output : value.output = some emission) :
    ∃ processing, value.processing = some processing ∧
      emission.target = processing.outcome.attachment.entry.flow.output processing.outcome.attachment.direction ∧
      processing.outcome.attachment.entry.flow.key processing.outcome.attachment.direction = (zone, source.packet.header) ∧
      processing.outcome.disposition = .forwarded ∧ 1 < source.packet.ip.packet.ttl.toNat ∧
      StatefulACL.Policy.evaluate before.configuration.forward.policy before.configuration.forward.compile
        processing.outcome.attachment.classification processing.outcome.afterDestination = .permit ∧
      StatefulACL.Policy.evaluate before.configuration.late.policy before.configuration.late.compile
        processing.outcome.attachment.classification emission.target = .permit ∧
      Routing.nextHop context.routing.compile processing.outcome.afterDestination.destination = processing.outcome.nextHop ∧
      processing.outcome.nextHop.isSome = true := by
  obtain ⟨processing, selected, emitted⟩ := value.processed_of_output emission output
  have nat := TCP.WireForwarding.step_nat _ _ _ _ processing.wire_step emission emitted
  have filters := TCP.WireForwarding.step_filters _ _ _ _ processing.wire_step emission emitted
  exact ⟨processing, selected, nat.1, nat.2.1, filters⟩

end Netlib.Check.CampusTCPService
