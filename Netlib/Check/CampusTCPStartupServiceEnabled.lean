import Netlib.Check.CampusTCPServiceEnabled
import Netlib.Protocol.TCP.WireForwardingFreshEnabled

/-!
# The first SYN through current campus policy

Current candidate keys, native decisions, and control fields derive service.
The result contains the actual confirmed binding and wire emission.
-/

namespace Netlib.Check.CampusTCPService

open Packet Protocol

structure ExistingAdmissionReady (context : Context) (before : Before) (source : W.Source) (zone : Nat)
    (ingress : I.InterfaceRef) (hit : FlowNAT.Hit) (hop : String) (mode : X.Mode := .ordinary) where
  checks : Checks context before ingress
  budget : checks.budget = 100000
  ingressPermit : before.guard.permits ingress.ifindex.val source.packet.header = true
  tracker : ConntrackLifecycle.ExistingReady (before.configuration.pipeline context.routing) before.tracker
    (packetInput before source zone).lifecycle hit hop
  admission : ∀ record ∈ before.tracker.records, record.entry.flow = hit.entry →
    X.Allowed mode before.admission.phase (ConntrackLifecycle.selectedAttachment record hit.direction)
      source.packet.segment before.admission.observations
  ttl : 1 < source.packet.ip.packet.ttl.toNat
  forwardComparison : checks.forward.passed = true
  guardComparison : checks.guard.passed = true
  covered : coverage context source = true

theorem run_existing_admission_enabled (context : Context) (before : Before) (source : W.Source) (zone : Nat)
    (ingress : I.InterfaceRef) (hit : FlowNAT.Hit) (hop : String)
    (ready : ExistingAdmissionReady context before source zone ingress hit hop mode) :
    ∃ evidence emission, run context before source zone ingress 100000 mode = .ok evidence ∧
      evidence.output = some emission ∧ evidence.passed = true ∧
      emission.target = hit.output ∧ evidence.tracker.model = before.tracker.model ∧
      ∃ processing, evidence.processing = some processing ∧ processing.outcome.nextHop = some hop := by
  obtain ⟨record, prepared, _, member, same, attached, attachment, changed⟩ :=
    ConntrackLifecycle.prepare_existing_completes before.tracker (packetInput before source zone).lifecycle hit
      ready.tracker.valid ready.tracker.zone ready.tracker.transport ready.tracker.candidate ready.tracker.lookup
  have existing : prepared.attachment.fresh = false := by rw [attachment]; rfl
  have allowed : X.Allowed mode before.admission.phase prepared.attachment source.packet.segment before.admission.observations := by
    rw [attachment]
    exact ready.admission record member same
  obtain ⟨admitted, admissionComputed⟩ := X.step_exists mode before.admission source.asInput
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
  let processing : Processing context before source zone mode :=
    ⟨prepared, attached, admitted, admissionComputed, outcome, computed, X.state admitted,
      TCP.AdmissionExecution.Result.confirmed_keeps admitted outcome.state confirmed⟩
  have permitted : ready.checks.decision source = true :=
    (ready.checks.actual_decision source).trans ready.ingressPermit
  let evidence : Evidence context before source zone ingress mode := ⟨ready.checks, .processed permitted processing⟩
  refine ⟨evidence, emission, ?_, emitted, ?_, ?_, ?_, ⟨processing, rfl, nextHop⟩⟩
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

structure FreshSynReady (context : Context) (before : Before) (source : W.Source) (zone : Nat)
    (ingress : I.InterfaceRef) (entry : NetfilterNAT.Entry) (hop : String) where
  checks : Checks context before ingress
  budget : checks.budget = 100000
  ingressPermit : before.guard.permits ingress.ifindex.val source.packet.header = true
  valid : before.tracker.Valid
  zoneBound : zone < 65536
  candidate : (packetInput before source zone).candidate = some entry
  compatible : entry.Compatible
  matching : entry.flow.original = source.packet.header ∧ entry.flow.originalZone = zone
  keys : ConntrackLifecycle.FreshKeys before.tracker entry
  phase : before.admission.phase = .empty
  profile : TCP.Admission.Startup source.packet.segment 2
  forwarding : ConntrackLifecycle.FreshForwardConditions (before.configuration.pipeline context.routing)
    source.packet.header entry hop
  ttl : 1 < source.packet.ip.packet.ttl.toNat
  forwardComparison : checks.forward.passed = true
  guardComparison : checks.guard.passed = true
  covered : coverage context source = true

theorem run_fresh_syn_enabled (context : Context) (before : Before) (source : W.Source) (zone : Nat)
    (ingress : I.InterfaceRef) (entry : NetfilterNAT.Entry) (hop : String)
    (ready : FreshSynReady context before source zone ingress entry hop) (mode : X.Mode := .ordinary) :
    ∃ evidence emission, run context before source zone ingress 100000 mode = .ok evidence ∧
      evidence.output = some emission ∧ evidence.passed = true ∧
      emission.target = entry.flow.output .original ∧
      evidence.tracker.records = before.tracker.records ++ [⟨entry, false⟩] ∧
      ∃ processing, evidence.processing = some processing ∧ processing.outcome.nextHop = some hop := by
  have transport : Conntrack.transport (packetInput before source zone).lifecycle.packet = true := by
    have tcp : source.packet.header.protocol = Packet.Protocol.tcp := by
      simp only [TCP.DecodedIPv4.header]
    simp only [packetInput, TCP.WireForwarding.Input.lifecycle, Conntrack.transport, tcp, true_or, decide_true]
  obtain ⟨prepared, attached, stateEq, attachment⟩ :=
    ConntrackLifecycle.prepare_fresh_enabled before.tracker (packetInput before source zone).lifecycle entry
      ready.valid ready.zoneBound transport ready.candidate ready.compatible ready.matching ready.keys
  have allowed : TCP.Admission.Allowed before.admission.phase prepared.attachment source.packet.segment before.admission.observations := by
    rw [ready.phase, attachment]
    exact ⟨rfl, rfl, ready.profile⟩
  have selected : X.Allowed mode before.admission.phase prepared.attachment source.packet.segment before.admission.observations := by
    cases mode with
    | ordinary => exact allowed
    | startupRecovery => exact Or.inl allowed
  obtain ⟨admitted, admissionComputed⟩ := X.step_exists mode before.admission source.asInput
    (packetInput before source zone).lifecycle prepared rfl selected
  have wireReady : TCP.WireForwarding.FreshForwardReady (before.configuration.pipeline context.routing)
      (packetInput before source zone) prepared hop := by
    refine ⟨by rw [attachment], by rw [attachment], by rw [attachment], ?_, ?_, ?_, ?_, ready.ttl⟩
    · rw [stateEq, attachment]
      exact ready.keys
    · simpa only [TCP.WireForwarding.destination, packetInput, attachment] using ready.forwarding.route
    · simpa only [TCP.WireForwarding.destination, packetInput, attachment] using ready.forwarding.forward
    · simpa only [TCP.WireForwarding.destination, packetInput, attachment] using ready.forwarding.late
  obtain ⟨outcome, emission, computed, emitted, confirmedRecords, _, nextHop, _, target⟩ :=
    TCP.WireForwarding.process_fresh_enabled (before.configuration.pipeline context.routing)
      (packetInput before source zone) source.valid prepared hop wireReady
  have confirmed : TCP.Admission.confirmed prepared.attachment.entry outcome.state = true := by
    apply (TCP.Admission.confirmed_correct _ _).mpr
    refine ⟨⟨prepared.attachment.entry, false⟩, ?_, rfl⟩
    rw [confirmedRecords]
    simp only [List.mem_append, List.mem_singleton, or_true]
  let processing : Processing context before source zone mode :=
    ⟨prepared, attached, admitted, admissionComputed, outcome, computed, X.state admitted,
      TCP.AdmissionExecution.Result.confirmed_keeps admitted outcome.state confirmed⟩
  have permitted : ready.checks.decision source = true :=
    (ready.checks.actual_decision source).trans ready.ingressPermit
  let evidence : Evidence context before source zone ingress mode := ⟨ready.checks, .processed permitted processing⟩
  refine ⟨evidence, emission, ?_, emitted, ?_, ?_, ?_, ⟨processing, rfl, nextHop⟩⟩
  · rw [← ready.budget]
    exact run_of_parts context before source zone ingress ready.checks permitted processing
  · change ready.checks.forward.passed && ready.checks.guard.passed && coverage context source = true
    simp only [ready.forwardComparison, ready.guardComparison, ready.covered, Bool.true_and]
    rfl
  · rw [target, attachment]
  · change outcome.state.records = _
    rw [confirmedRecords, stateEq, attachment]

end Netlib.Check.CampusTCPService
