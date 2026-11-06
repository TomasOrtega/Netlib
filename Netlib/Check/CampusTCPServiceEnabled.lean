import Netlib.Protocol.ConntrackLifecycleEnabled
import Netlib.Protocol.TCP.AdmissionEnabled
import Netlib.Protocol.TCP.AdmissionRepeatEnabled
import Netlib.Protocol.TCP.WireForwardingEnabled
import Netlib.Check.CampusTCPService

/-!
# Current gateway service from preceding packet conditions

The comparison evidence is about installed policy and ingress lifetimes.
Packet admission and output follow from old tracker, lane, route, and filter facts.
-/

namespace Netlib.Check.IngressGuard

theorem check_source (value : Checked now executionNS attachments maintenance application)
    (computed : check now executionNS attachments maintenance application source budget = .ok value) :
    value.source = source := by
  unfold check at computed
  repeat' first
    | (cases computed; rfl)
    | (split at computed <;> try simp [bind, Except.bind, pure, throw] at computed)

end Netlib.Check.IngressGuard

namespace Netlib.Check.CampusTCPService

open Packet Protocol

structure ExistingDataReady (context : Context) (before : Before) (source : W.Source) (zone : Nat)
    (ingress : I.InterfaceRef) (hit : FlowNAT.Hit) (session : TCP.Admission.Session) (hop : String) where
  checks : Checks context before ingress
  budget : checks.budget = 100000
  ingressPermit : before.guard.permits ingress.ifindex.val source.packet.header = true
  tracker : ConntrackLifecycle.ExistingReady (before.configuration.pipeline context.routing) before.tracker
    (packetInput before source zone).lifecycle hit hop
  phase : before.admission.phase = .data session
  binding : ∀ record ∈ before.tracker.records, record.entry.flow = hit.entry → record.entry = session.entry
  data : TCP.Admission.DataReady session hit.direction source.packet.segment
  ttl : 1 < source.packet.ip.packet.ttl.toNat
  forwardComparison : checks.forward.passed = true
  guardComparison : checks.guard.passed = true
  covered : coverage context source = true

theorem run_existing_enabled (context : Context) (before : Before) (source : W.Source) (zone : Nat)
    (ingress : I.InterfaceRef) (hit : FlowNAT.Hit) (session : TCP.Admission.Session) (hop : String)
    (ready : ExistingDataReady context before source zone ingress hit session hop) :
    ∃ evidence emission, run context before source zone ingress = .ok evidence ∧
      evidence.output = some emission ∧ evidence.passed = true ∧
      emission.target = hit.output ∧ evidence.tracker.model = before.tracker.model ∧
      ∃ processing, evidence.processing = some processing ∧ processing.outcome.nextHop = some hop := by
  obtain ⟨record, prepared, _, member, same, attached, attachment, changed⟩ :=
    ConntrackLifecycle.prepare_existing_completes before.tracker (packetInput before source zone).lifecycle hit
      ready.tracker.valid ready.tracker.zone ready.tracker.transport ready.tracker.candidate ready.tracker.lookup
  have existing : prepared.attachment.fresh = false := by rw [attachment]; rfl
  have entry : prepared.attachment.entry = session.entry := by
    rw [attachment]
    exact ready.binding record member same
  have data : TCP.Admission.DataReady session prepared.attachment.direction source.packet.segment := by
    rw [attachment]
    exact ready.data
  have allowed : TCP.Admission.Allowed before.admission.phase prepared.attachment source.packet.segment before.admission.observations := by
    rw [ready.phase]
    exact TCP.Admission.DataReady.allowed session prepared.attachment source.packet.segment before.admission.observations entry existing data
  obtain ⟨admitted, admissionComputed⟩ := TCP.Admission.step_exists before.admission source.asInput
    (packetInput before source zone).lifecycle prepared rfl allowed
  have native := ready.tracker.forwarding record member same
  rw [← attachment] at native
  have wireReady : TCP.WireForwarding.ForwardReady (before.configuration.pipeline context.routing)
      (packetInput before source zone) prepared hop :=
    ⟨native.existing, native.route, native.forward, native.late, ready.ttl⟩
  obtain ⟨outcome, emission, computed, emitted, unchanged, _, nextHop, _, target⟩ :=
    TCP.WireForwarding.process_existing_enabled (before.configuration.pipeline context.routing)
      (packetInput before source zone) source.valid prepared hop wireReady
  obtain ⟨confirmedRecord, confirmedMember, confirmedEntry⟩ :=
    ConntrackLifecycle.prepared_selected_confirmed before.tracker hit record prepared member attachment changed
  have confirmed : TCP.Admission.confirmed prepared.attachment.entry outcome.state = true := by
    apply (TCP.Admission.confirmed_correct _ _).mpr
    rw [unchanged]
    exact ⟨confirmedRecord, confirmedMember, confirmedEntry⟩
  have committed := admitted.confirmed_keeps outcome.state confirmed
  let processing : Processing context before source zone :=
    ⟨prepared, attached, admitted, admissionComputed, outcome, computed, admitted.state, committed⟩
  have permitted : ready.checks.decision source = true :=
    (ready.checks.actual_decision source).trans ready.ingressPermit
  let evidence : Evidence context before source zone ingress := ⟨ready.checks, .processed permitted processing⟩
  refine ⟨evidence, emission, ?_, emitted, ?_, ?_, ?_, ?_⟩
  · rw [← ready.budget]
    exact run_of_parts context before source zone ingress ready.checks permitted processing
  · change ready.checks.forward.passed && ready.checks.guard.passed && coverage context source = true
    simp only [ready.forwardComparison, ready.guardComparison, ready.covered, Bool.true_and]
    rfl
  · rw [target, attachment]
    exact congrArg (fun flow => flow.output hit.direction) same
  · change outcome.state.model = before.tracker.model
    rw [unchanged]
    exact ConntrackLifecycle.prepare_model _ _ _ attached
  · exact ⟨processing, rfl, nextHop⟩

structure ExistingRepeatedReady (context : Context) (before : Before) (source : W.Source) (zone : Nat)
    (ingress : I.InterfaceRef) (hit : FlowNAT.Hit) (session : TCP.Admission.Session) (hop : String) where
  checks : Checks context before ingress
  budget : checks.budget = 100000
  ingressPermit : before.guard.permits ingress.ifindex.val source.packet.header = true
  tracker : ConntrackLifecycle.ExistingReady (before.configuration.pipeline context.routing) before.tracker
    (packetInput before source zone).lifecycle hit hop
  phase : before.admission.phase = .data session
  binding : ∀ record ∈ before.tracker.records, record.entry.flow = hit.entry → record.entry = session.entry
  repeated : TCP.Admission.RepeatedReady session hit.direction source.packet.segment before.admission.observations
  ttl : 1 < source.packet.ip.packet.ttl.toNat
  forwardComparison : checks.forward.passed = true
  guardComparison : checks.guard.passed = true
  covered : coverage context source = true

theorem run_existing_repeated_enabled (context : Context) (before : Before) (source : W.Source) (zone : Nat)
    (ingress : I.InterfaceRef) (hit : FlowNAT.Hit) (session : TCP.Admission.Session) (hop : String)
    (ready : ExistingRepeatedReady context before source zone ingress hit session hop) :
    ∃ evidence emission, run context before source zone ingress = .ok evidence ∧
      evidence.output = some emission ∧ evidence.passed = true ∧
      emission.target = hit.output ∧ evidence.tracker.model = before.tracker.model ∧
      ∃ processing, evidence.processing = some processing ∧ processing.outcome.nextHop = some hop := by
  obtain ⟨record, prepared, _, member, same, attached, attachment, changed⟩ :=
    ConntrackLifecycle.prepare_existing_completes before.tracker (packetInput before source zone).lifecycle hit
      ready.tracker.valid ready.tracker.zone ready.tracker.transport ready.tracker.candidate ready.tracker.lookup
  have existing : prepared.attachment.fresh = false := by rw [attachment]; rfl
  have entry : prepared.attachment.entry = session.entry := by
    rw [attachment]
    exact ready.binding record member same
  have repeated : TCP.Admission.RepeatedReady session prepared.attachment.direction source.packet.segment before.admission.observations := by
    rw [attachment]
    exact ready.repeated
  have allowed : TCP.Admission.Allowed before.admission.phase prepared.attachment source.packet.segment before.admission.observations := by
    rw [ready.phase]
    exact TCP.Admission.RepeatedReady.allowed session prepared.attachment source.packet.segment before.admission.observations entry existing repeated
  obtain ⟨admitted, admissionComputed⟩ := TCP.Admission.step_exists before.admission source.asInput
    (packetInput before source zone).lifecycle prepared rfl allowed
  have native := ready.tracker.forwarding record member same
  rw [← attachment] at native
  have wireReady : TCP.WireForwarding.ForwardReady (before.configuration.pipeline context.routing)
      (packetInput before source zone) prepared hop :=
    ⟨native.existing, native.route, native.forward, native.late, ready.ttl⟩
  obtain ⟨outcome, emission, computed, emitted, unchanged, _, nextHop, _, target⟩ :=
    TCP.WireForwarding.process_existing_enabled (before.configuration.pipeline context.routing)
      (packetInput before source zone) source.valid prepared hop wireReady
  obtain ⟨confirmedRecord, confirmedMember, confirmedEntry⟩ :=
    ConntrackLifecycle.prepared_selected_confirmed before.tracker hit record prepared member attachment changed
  have confirmed : TCP.Admission.confirmed prepared.attachment.entry outcome.state = true := by
    apply (TCP.Admission.confirmed_correct _ _).mpr
    rw [unchanged]
    exact ⟨confirmedRecord, confirmedMember, confirmedEntry⟩
  have committed := admitted.confirmed_keeps outcome.state confirmed
  let processing : Processing context before source zone :=
    ⟨prepared, attached, admitted, admissionComputed, outcome, computed, admitted.state, committed⟩
  have permitted : ready.checks.decision source = true :=
    (ready.checks.actual_decision source).trans ready.ingressPermit
  let evidence : Evidence context before source zone ingress := ⟨ready.checks, .processed permitted processing⟩
  refine ⟨evidence, emission, ?_, emitted, ?_, ?_, ?_, ?_⟩
  · rw [← ready.budget]
    exact run_of_parts context before source zone ingress ready.checks permitted processing
  · change ready.checks.forward.passed && ready.checks.guard.passed && coverage context source = true
    simp only [ready.forwardComparison, ready.guardComparison, ready.covered, Bool.true_and]
    rfl
  · rw [target, attachment]
    exact congrArg (fun flow => flow.output hit.direction) same
  · change outcome.state.model = before.tracker.model
    rw [unchanged]
    exact ConntrackLifecycle.prepare_model _ _ _ attached
  · exact ⟨processing, rfl, nextHop⟩

end Netlib.Check.CampusTCPService
