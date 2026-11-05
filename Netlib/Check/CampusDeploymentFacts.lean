import Netlib.Check.CampusDeployment
import Netlib.Examples.CampusDuplex
import Netlib.Examples.CampusDirect

namespace Netlib.Check.CampusDeployment
open Packet Protocol

def Payload.authenticationTag : Payload input before → Bool
  | .authentication _ => true
  | _ => false

def Payload.networkTag : Payload input before → Bool
  | .network _ => true
  | _ => false

def authenticationTag (finding : Finding input) : Bool := finding.result.payload.authenticationTag
def networkTag (finding : Finding input) : Bool := finding.result.payload.networkTag

theorem Result.counts (result : Result input) :
    result.state.authentication = result.before.authentication + (if result.payload.authenticationTag then 1 else 0) ∧
    result.state.network = result.before.network + (if result.payload.networkTag then 1 else 0) := by
  cases result with
  | mk before payload safe => cases payload <;> simp [Result.state, Payload.state, Payload.authenticationTag, Payload.networkTag]

theorem trace_counts (trace : Replay.Trace (replay input budget) initial findings final) :
    final.authentication = initial.authentication + findings.countP authenticationTag ∧
      final.network = initial.network + findings.countP networkTag := by
  induction trace with
  | nil => simp
  | @cons before final head tail computed rest ih =>
    have beforeEq := step_before input budget before head.observation head.result computed
    have counts := head.result.counts
    have authEq := congrArg State.authentication beforeEq
    have networkEq := congrArg State.network beforeEq
    rw [authEq, networkEq] at counts
    simp only [List.countP_cons]
    change final.authentication = before.authentication + (tail.countP authenticationTag + (if head.result.payload.authenticationTag then 1 else 0)) ∧
      final.network = before.network + (tail.countP networkTag + (if head.result.payload.networkTag then 1 else 0))
    change final.authentication = head.result.state.authentication + tail.countP authenticationTag ∧
      final.network = head.result.state.network + tail.countP networkTag at ih
    omega

theorem Report.prefix_counts (report : Report input budget observations) (finding : Finding input)
    (member : finding ∈ report.findings) :
    ∃ prior later,
      report.findings = prior ++ finding :: later ∧
      Replay.Trace (replay input budget) input.initial prior finding.result.before ∧
      step input budget finding.result.before finding.observation = .ok finding.result ∧
      finding.result.before.authentication = prior.countP authenticationTag ∧
      finding.result.before.network = prior.countP networkTag := by
  obtain ⟨prior, later, before, covered, prefixTrace, computed, _⟩ := report.trace.prefix finding member
  have beforeEq := step_before input budget before finding.observation finding.result computed
  rw [← beforeEq] at prefixTrace computed
  have counts := trace_counts prefixTrace
  exact ⟨prior, later, covered, prefixTrace, computed,
    by simpa only [Input.initial, Nat.zero_add] using counts.1,
    by simpa only [Input.initial, Nat.zero_add] using counts.2⟩

theorem Report.prefixes_safe (report : Report input budget observations) :
    report.final.Safe input ∧ ∀ finding ∈ report.findings, finding.result.state.Safe input :=
  report.trace.invariant (fun state => state.Safe input) (fun _ _ result _ _ => result.safe) input.initial_safe

theorem Certification.checked_of_some (certificate : Certification input after target) (valid : certificate.Valid)
    (active : Protocol.SafeHandoff.Configuration) (selected : target = some active) :
    ∃ checked : SessionInstallation.Checked input.authentication input.requirements after active, checked.passed = true := by
  cases certificate with
  | absent => cases selected
  | present configuration checked =>
    have same := Option.some.inj selected
    subst configuration
    exact ⟨checked, valid⟩

theorem NetworkEvidence.served_event (evidence : NetworkEvidence input before) (matched : evidence.Matches)
    (served : Protocol.SafeHandoff.PacketResult) (stored : evidence.model.served = some served) :
    ∃ id source observed,
      evidence.source.event = .serve id source observed ∧ evidence.event = .serve id ∧
      served.ticket.value.source.bytes = source.bytes ∧ observed.Matches served.outcome := by
  have packets := matched.1.1
  change Check.SafeHandoff.PacketMatches evidence.source evidence.model at packets
  unfold Check.SafeHandoff.PacketMatches at packets
  rw [stored] at packets
  have converted := evidence.converted
  change evidence.source.event.toModel input.handoff.routing input.handoff.configs before.deployment.handoff = .ok evidence.event at converted
  cases event : evidence.source.event with
  | serve id source observed =>
    rw [event, Check.SafeHandoff.Event.toModel] at converted
    have selected := Except.ok.inj converted
    cases established : evidence.model.established with
    | some packet => simp [event, established] at packets
    | none =>
      have pair : served.ticket.value.source.bytes = source.bytes ∧ observed.Matches served.outcome := by
        simpa only [event, established] using packets
      exact ⟨id, source, observed, rfl, selected.symm, pair⟩
  | establish zone source observed => cases evidence.model.established <;> simp_all
  | stage zone key => cases evidence.model.established <;> simp_all
  | commit timeout => cases evidence.model.established <;> simp_all
  | handoff leg gateway => cases evidence.model.established <;> simp_all
  | fence gateway => cases evidence.model.established <;> simp_all
  | forget => cases evidence.model.established <;> simp_all
  | install gateway config => cases evidence.model.established <;> simp_all
  | assign direction source observed => cases evidence.model.established <;> simp_all

theorem NetworkEvidence.serve_current_permission (evidence : NetworkEvidence input before) (matched : evidence.Matches)
    (served : Protocol.SafeHandoff.PacketResult) (stored : evidence.model.served = some served)
    (emission : WireForwarding.Emission served.ticket.value.source.packet) (emitted : served.outcome.output = some emission) :
    Examples.WireNATDeployment.OutputFacts served.ticket.value.source.packet emission ∧
      1 < served.ticket.value.source.packet.ip.packet.ttl.toNat ∧
      Session.Valid input.authentication.context (SessionInstallation.current input.authentication before.authentication).session input.application ∧
      EAPAuth.State.Ready (EAPSession.authContext input.authentication.context)
        (SessionInstallation.current input.authentication before.authentication).auth := by
  obtain ⟨id, _, _, _, event, _⟩ := evidence.served_event matched served stored
  have target : policyTarget before.deployment.handoff evidence.event evidence.model = some served.configuration := by
    simp [policyTarget, stored]
  obtain ⟨checked, passed⟩ := evidence.certificate.checked_of_some matched.2 served.configuration target
  have actual := evidence.actual_step.1
  rw [event] at actual
  obtain ⟨_, raw, computed, rawEq⟩ := Protocol.SafeHandoff.step_core before.deployment.handoff (.serve id) evidence.model actual
  have current : served.configuration = before.deployment.handoff.configurations served.ticket.value.gateway := by
    obtain ⟨completed, outcome, _, reported, _⟩ := Protocol.SafeHandoff.core_serve_facts before.deployment.handoff id raw computed
    have reported' : evidence.model.served = some (⟨completed.item, before.deployment.handoff.configurations completed.item.value.gateway, outcome⟩ : Protocol.SafeHandoff.PacketResult) := by
      simpa only [← rawEq] using reported
    have same := Option.some.inj (stored.symm.trans reported')
    cases same
    rfl
  have installed : Examples.SessionFirewallDeployment.ForwardEquivalent
      (before.deployment.handoff.configurations served.ticket.value.gateway).pipeline checked.compiled := by
    simpa only [current] using checked.forward_equivalent passed
  obtain ⟨facts, live, requirement, member, _, valid, ready⟩ := Examples.SafeHandoffDeployment.serve_current_permission
    checked.compiled (Check.SessionFirewall.stateAt_safe _ _) before.deployment.handoff id evidence.model served
    actual stored installed emission emitted
  rw [input.scopes requirement member] at valid
  exact ⟨facts, live, valid, ready⟩


theorem Report.served_current_permission (report : Report input budget observations) (compliant : report.compliant = true)
    (finding : Finding input) (member : finding ∈ report.findings)
    (evidence : NetworkEvidence input finding.result.before) (payload : finding.result.payload = .network evidence)
    (served : Protocol.SafeHandoff.PacketResult) (stored : evidence.model.served = some served)
    (emission : WireForwarding.Emission served.ticket.value.source.packet) (emitted : served.outcome.output = some emission) :
    ∃ prior later,
      report.findings = prior ++ finding :: later ∧
      Replay.Trace (replay input budget) input.initial prior finding.result.before ∧
      finding.result.before.authentication = prior.countP authenticationTag ∧
      finding.result.before.network = prior.countP networkTag ∧
      Examples.WireNATDeployment.OutputFacts served.ticket.value.source.packet emission ∧
      1 < served.ticket.value.source.packet.ip.packet.ttl.toNat ∧
      Session.Valid input.authentication.context
        (SessionInstallation.current input.authentication finding.result.before.authentication).session input.application ∧
      EAPAuth.State.Ready (EAPSession.authContext input.authentication.context)
        (SessionInstallation.current input.authentication finding.result.before.authentication).auth ∧
      Examples.CampusDuplex.Duplex (Examples.CampusDuplex.interpretation input.authentication.context
        (SessionInstallation.current input.authentication finding.result.before.authentication) input.application finding.result.before.deployment) := by
  have matched := report.finding_matches compliant finding member
  change finding.result.payload.Matches at matched
  rw [payload] at matched
  obtain ⟨prior, later, covered, prefixTrace, _, authCount, networkCount⟩ := report.prefix_counts finding member
  obtain ⟨facts, live, valid, ready⟩ := evidence.serve_current_permission matched served stored emission emitted
  have duplex := (Examples.CampusDuplex.interpretation_duplex_iff input.authentication.context
    (SessionInstallation.current input.authentication finding.result.before.authentication) input.application finding.result.before.deployment).mpr
    ((Session.permits_iff _ _ _).mpr valid)
  exact ⟨prior, later, covered, prefixTrace, authCount, networkCount, facts, live, valid, ready, duplex⟩

theorem NetworkEvidence.observed_output (evidence : NetworkEvidence input before) (matched : evidence.Matches)
    (id : Nat) (source : Protocol.SafeHandoff.Source) (observed : Check.WireForwarding.PacketObservation)
    (event : evidence.source.event = .serve id source observed) (captured : Check.WireForwarding.WirePacket)
    (seen : observed.output = some captured) :
    ∃ (served : Protocol.SafeHandoff.PacketResult) (emission : WireForwarding.Emission served.ticket.value.source.packet),
      evidence.model.served = some served ∧ served.ticket.value.source.bytes = source.bytes ∧
      served.outcome.output = some emission ∧ captured.value = Check.WireForwarding.emissionValue emission := by
  have packets := matched.1.1
  change Check.SafeHandoff.PacketMatches evidence.source evidence.model at packets
  unfold Check.SafeHandoff.PacketMatches at packets
  rw [event] at packets
  cases established : evidence.model.established with
  | some packet => simp [established] at packets
  | none =>
    cases servedEq : evidence.model.served with
    | none => simp [established, servedEq] at packets
    | some served =>
      have pair : served.ticket.value.source.bytes = source.bytes ∧ observed.Matches served.outcome := by
        simpa only [established, servedEq] using packets
      obtain ⟨_, _, _, _, _, _, outputs⟩ := pair.2
      cases emitted : served.outcome.output with
      | none => simp [seen, emitted] at outputs
      | some emission =>
        rw [seen, emitted] at outputs
        exact ⟨served, emission, rfl, pair.1, emitted, Option.some.inj outputs⟩

theorem Report.observed_output_facts (report : Report input budget observations) (compliant : report.compliant = true)
    (finding : Finding input) (member : finding ∈ report.findings)
    (evidence : NetworkEvidence input finding.result.before) (payload : finding.result.payload = .network evidence)
    (id : Nat) (source : Protocol.SafeHandoff.Source) (observed : Check.WireForwarding.PacketObservation)
    (event : evidence.source.event = .serve id source observed) (captured : Check.WireForwarding.WirePacket)
    (seen : observed.output = some captured) :
    ∃ (prior later : List (Finding input)) (served : Protocol.SafeHandoff.PacketResult)
      (emission : WireForwarding.Emission served.ticket.value.source.packet),
      report.findings = prior ++ finding :: later ∧
      Replay.Trace (replay input budget) input.initial prior finding.result.before ∧
      finding.result.before.authentication = prior.countP authenticationTag ∧
      finding.result.before.network = prior.countP networkTag ∧
      evidence.model.served = some served ∧ served.ticket.value.source.bytes = source.bytes ∧
      served.outcome.output = some emission ∧ captured.value = Check.WireForwarding.emissionValue emission ∧
      captured.checked.packet.datagram.payload = served.ticket.value.source.packet.datagram.payload ∧
      captured.checked.packet.ip.packet.ttl.toNat = served.ticket.value.source.packet.ip.packet.ttl.toNat - 1 ∧
      Session.Valid input.authentication.context
        (SessionInstallation.current input.authentication finding.result.before.authentication).session input.application ∧
      EAPAuth.State.Ready (EAPSession.authContext input.authentication.context)
        (SessionInstallation.current input.authentication finding.result.before.authentication).auth ∧
      Examples.CampusDuplex.Duplex (Examples.CampusDuplex.interpretation input.authentication.context
        (SessionInstallation.current input.authentication finding.result.before.authentication) input.application finding.result.before.deployment) := by
  have matched := report.finding_matches compliant finding member
  change finding.result.payload.Matches at matched
  rw [payload] at matched
  obtain ⟨served, emission, stored, sourceEq, emitted, valueEq⟩ := evidence.observed_output matched id source observed event captured seen
  obtain ⟨prior, later, covered, prefixTrace, authCount, networkCount, _, _, valid, ready, duplex⟩ :=
    report.served_current_permission compliant finding member evidence payload served stored emission emitted
  have ipEq := congrArg Prod.fst valueEq
  have dataEq := congrArg Prod.snd valueEq
  change captured.checked.packet.ip.packet = emission.decoded.ip.packet at ipEq
  change captured.checked.packet.datagram = emission.decoded.datagram at dataEq
  exact ⟨prior, later, served, emission, covered, prefixTrace, authCount, networkCount, stored, sourceEq, emitted,
    valueEq, by rw [dataEq]; exact emission.payload, by rw [ipEq]; exact emission.ttl, valid, ready, duplex⟩

def NetworkEvidence.finding (evidence : NetworkEvidence input before) : Check.SafeHandoff.Finding :=
  Replay.finding (Check.SafeHandoff.replay input.handoff.routing input.handoff.configs) evidence.source evidence.model

def Payload.AssignmentOrigin (payload : Payload input before)
    (item : Theory.Outstanding.Item Protocol.SafeHandoff.Ticket) : Prop :=
  match payload with
  | .network evidence => Check.SafeHandoff.AdmissionOrigin before.deployment.handoff evidence.finding item
  | _ => False

theorem Payload.pending_origin (payload : Payload input before)
    (item : Theory.Outstanding.Item Protocol.SafeHandoff.Ticket)
    (member : item ∈ payload.state.deployment.handoff.work.pending) :
    item ∈ before.deployment.handoff.work.pending ∨ payload.AssignmentOrigin item := by
  cases payload with
  | authentication evidence => exact .inl member
  | withdraw evidence =>
    have fields := CampusWithdrawal.step_withdraw_facts before.deployment evidence.operated evidence.computed
    change item ∈ evidence.operated.state.handoff.work.pending at member
    rw [fields.2.2.2.1] at member
    exact .inl member
  | network evidence =>
    have actual : Check.SafeHandoff.step input.handoff.routing input.handoff.configs before.deployment.handoff
        evidence.source = .ok evidence.model := by
      simp only [Check.SafeHandoff.step, NetworkEvidence.source, evidence.converted, bind, Except.bind]
      exact evidence.actual_step.1
    change item ∈ evidence.operated.state.handoff.work.pending at member
    rw [evidence.actual_step.2] at member
    exact Check.SafeHandoff.step_pending_origin before.deployment.handoff evidence.finding actual item member

def AssignmentOrigin (before : State) (finding : Finding input)
    (item : Theory.Outstanding.Item Protocol.SafeHandoff.Ticket) : Prop :=
  finding.result.before = before ∧ finding.result.payload.AssignmentOrigin item

theorem step_pending_origin (before : State) (finding : Finding input)
    (accepted : step input budget before finding.observation = .ok finding.result)
    (item : Theory.Outstanding.Item Protocol.SafeHandoff.Ticket)
    (member : item ∈ finding.result.state.deployment.handoff.work.pending) :
    item ∈ before.deployment.handoff.work.pending ∨ AssignmentOrigin before finding item := by
  have beforeEq := step_before input budget before finding.observation finding.result accepted
  rcases finding.result.payload.pending_origin item member with old | origin
  · have pendingEq := congrArg (fun state => state.deployment.handoff.work.pending) beforeEq
    exact .inl (by simpa only [pendingEq] using old)
  · exact .inr ⟨beforeEq, origin⟩

theorem trace_pending_source (trace : Replay.Trace (replay input budget) initial findings final)
    (item : Theory.Outstanding.Item Protocol.SafeHandoff.Ticket)
    (member : item ∈ final.deployment.handoff.work.pending) :
    item ∈ initial.deployment.handoff.work.pending ∨ ∃ prior finding later before,
      findings = prior ++ finding :: later ∧ Replay.Trace (replay input budget) initial prior before ∧
      step input budget before finding.observation = .ok finding.result ∧ AssignmentOrigin before finding item :=
  trace.origin (fun state item => item ∈ state.deployment.handoff.work.pending) AssignmentOrigin
    (fun before finding item accepted present => step_pending_origin before finding accepted item present) item member

theorem NetworkEvidence.served_pending (evidence : NetworkEvidence input before) (matched : evidence.Matches)
    (served : Protocol.SafeHandoff.PacketResult) (stored : evidence.model.served = some served) :
    served.ticket ∈ before.deployment.handoff.work.pending := by
  obtain ⟨id, _, _, _, event, _⟩ := evidence.served_event matched served stored
  have accepted := evidence.actual_step.1
  rw [event] at accepted
  obtain ⟨_, raw, computed, rawEq⟩ := Protocol.SafeHandoff.step_core before.deployment.handoff (.serve id) evidence.model accepted
  obtain ⟨completed, outcome, _, reported, _⟩ := Protocol.SafeHandoff.core_serve_facts before.deployment.handoff id raw computed
  have reported' : evidence.model.served = some
      (⟨completed.item, before.deployment.handoff.configurations completed.item.value.gateway, outcome⟩ : Protocol.SafeHandoff.PacketResult) := by
    simpa only [← rawEq] using reported
  have same := Option.some.inj (stored.symm.trans reported')
  cases same
  exact completed.member

theorem Report.served_source (report : Report input budget observations) (compliant : report.compliant = true)
    (finding : Finding input) (member : finding ∈ report.findings)
    (evidence : NetworkEvidence input finding.result.before) (payload : finding.result.payload = .network evidence)
    (served : Protocol.SafeHandoff.PacketResult) (stored : evidence.model.served = some served) :
    ∃ servePrior serveLater assignPrior assignFinding assignLater beforeAssign,
      report.findings = servePrior ++ finding :: serveLater ∧
      Replay.Trace (replay input budget) input.initial servePrior finding.result.before ∧
      servePrior = assignPrior ++ assignFinding :: assignLater ∧
      Replay.Trace (replay input budget) input.initial assignPrior beforeAssign ∧
      step input budget beforeAssign assignFinding.observation = .ok assignFinding.result ∧
      AssignmentOrigin beforeAssign assignFinding served.ticket := by
  obtain ⟨prior, later, covered, prefixTrace, _, _, _⟩ := report.prefix_counts finding member
  have matched := report.finding_matches compliant finding member
  change finding.result.payload.Matches at matched
  rw [payload] at matched
  have pending := evidence.served_pending matched served stored
  rcases trace_pending_source prefixTrace served.ticket pending with initial | origin
  · simp [Input.initial, CampusWithdrawal.State.initial, Protocol.SafeHandoff.State.initial] at initial
  · obtain ⟨assignPrior, assignFinding, assignLater, beforeAssign, assignmentCovered, assignmentTrace, accepted, source⟩ := origin
    exact ⟨prior, later, assignPrior, assignFinding, assignLater, beforeAssign, covered, prefixTrace,
      assignmentCovered, assignmentTrace, accepted, source⟩

theorem checked_forward_iff_duplex (input : Input) (after : Nat) (active : Protocol.SafeHandoff.Configuration)
    (checked : SessionInstallation.Checked input.authentication input.requirements after active)
    (passed : checked.passed = true) (state : StatefulACL.CTState) (header : Header)
    (covered : ∃ requirement ∈ input.requirements, requirement.test.Holds header) (withdrawn : Bool) :
    StatefulACL.Policy.evaluate active.pipeline.forwardDefault active.pipeline.forward state header = .permit ↔
      Examples.CampusDirect.Duplex (Examples.CampusDirect.network input.authentication.context
        (SessionInstallation.current input.authentication after) input.application withdrawn) := by
  have same := checked.forward_equivalent passed state header
  have decision : StatefulACL.Policy.evaluate active.pipeline.forwardDefault active.pipeline.forward state header = .permit ↔
      checked.compiled.snapshot.permits header = true := by
    rw [same, ← checked.compiled.statefulSnapshot_permits state header]
    simp [Import.NftablesStateful.Snapshot.permits]
  rw [decision, checked.compiled.permits_iff,
    Examples.CampusDirect.duplex_reachable_iff input.authentication.context
      (SessionInstallation.current input.authentication after) input.application withdrawn]
  constructor
  · rintro ⟨requirement, member, allowed, _⟩
    simpa only [input.scopes requirement member] using allowed
  · intro allowed
    obtain ⟨requirement, member, matched⟩ := covered
    exact ⟨requirement, member, by simpa only [input.scopes requirement member] using allowed, matched⟩

theorem NetworkEvidence.forward_iff_duplex (evidence : NetworkEvidence input before) (matched : evidence.Matches)
    (served : Protocol.SafeHandoff.PacketResult) (stored : evidence.model.served = some served)
    (state : StatefulACL.CTState) (header : Header)
    (covered : ∃ requirement ∈ input.requirements, requirement.test.Holds header) :
    StatefulACL.Policy.evaluate served.configuration.pipeline.forwardDefault served.configuration.pipeline.forward state header = .permit ↔
      Examples.CampusDirect.Duplex (Examples.CampusDirect.network input.authentication.context
        (SessionInstallation.current input.authentication before.authentication) input.application before.deployment.withdrawn) := by
  have target : policyTarget before.deployment.handoff evidence.event evidence.model = some served.configuration := by
    simp [policyTarget, stored]
  obtain ⟨checked, passed⟩ := evidence.certificate.checked_of_some matched.2 served.configuration target
  exact checked_forward_iff_duplex input before.authentication served.configuration checked passed state header covered before.deployment.withdrawn

theorem NetworkEvidence.denied_output_none (evidence : NetworkEvidence input before) (matched : evidence.Matches)
    (served : Protocol.SafeHandoff.PacketResult) (stored : evidence.model.served = some served)
    (denied : (SessionInstallation.current input.authentication before.authentication).session.permits input.authentication.context input.application = false) :
    served.outcome.output = none := by
  cases output : served.outcome.output with
  | none => rfl
  | some emission =>
    have valid := (evidence.serve_current_permission matched served stored emission output).2.2.1
    have permitted := (Session.permits_iff _ _ _).mpr valid
    simp [denied] at permitted

theorem Report.denied_output_none (report : Report input budget observations) (compliant : report.compliant = true)
    (finding : Finding input) (member : finding ∈ report.findings)
    (evidence : NetworkEvidence input finding.result.before) (payload : finding.result.payload = .network evidence)
    (served : Protocol.SafeHandoff.PacketResult) (stored : evidence.model.served = some served)
    (denied : (SessionInstallation.current input.authentication finding.result.before.authentication).session.permits
      input.authentication.context input.application = false) : served.outcome.output = none := by
  have matched := report.finding_matches compliant finding member
  change finding.result.payload.Matches at matched
  rw [payload] at matched
  exact evidence.denied_output_none matched served stored denied

theorem NetworkEvidence.emission_target (evidence : NetworkEvidence input before) (matched : evidence.Matches)
    (served : Protocol.SafeHandoff.PacketResult) (stored : evidence.model.served = some served)
    (emission : WireForwarding.Emission served.ticket.value.source.packet) (emitted : served.outcome.output = some emission) :
    emission.target = served.ticket.value.entry.flow.output served.ticket.value.direction := by
  obtain ⟨id, _, _, _, event, _⟩ := evidence.served_event matched served stored
  have accepted := evidence.actual_step.1
  rw [event] at accepted
  obtain ⟨safe, raw, computed, rawEq⟩ := Protocol.SafeHandoff.step_core before.deployment.handoff (.serve id) evidence.model accepted
  have rawStored : raw.served = some served := by simpa only [← rawEq] using stored
  exact (Protocol.SafeHandoff.core_serve_forwarded before.deployment.handoff id raw safe computed served rawStored emission emitted).2.2.2.1

theorem Report.observed_output_nat_facts (report : Report input budget observations) (compliant : report.compliant = true)
    (finding : Finding input) (member : finding ∈ report.findings)
    (evidence : NetworkEvidence input finding.result.before) (payload : finding.result.payload = .network evidence)
    (id : Nat) (source : Protocol.SafeHandoff.Source) (observed : Check.WireForwarding.PacketObservation)
    (event : evidence.source.event = .serve id source observed) (captured : Check.WireForwarding.WirePacket)
    (seen : observed.output = some captured) :
    ∃ (prior later : List (Finding input)) (served : Protocol.SafeHandoff.PacketResult)
      (emission : WireForwarding.Emission served.ticket.value.source.packet),
      report.findings = prior ++ finding :: later ∧
      Replay.Trace (replay input budget) input.initial prior finding.result.before ∧
      finding.result.before.authentication = prior.countP authenticationTag ∧
      finding.result.before.network = prior.countP networkTag ∧
      evidence.model.served = some served ∧ served.ticket.value.source.bytes = source.bytes ∧
      served.outcome.output = some emission ∧ captured.value = Check.WireForwarding.emissionValue emission ∧
      captured.checked.header = served.ticket.value.entry.flow.output served.ticket.value.direction ∧
      captured.checked.packet.datagram.payload = served.ticket.value.source.packet.datagram.payload ∧
      captured.checked.packet.ip.packet.ttl.toNat = served.ticket.value.source.packet.ip.packet.ttl.toNat - 1 ∧
      Session.Valid input.authentication.context
        (SessionInstallation.current input.authentication finding.result.before.authentication).session input.application ∧
      EAPAuth.State.Ready (EAPSession.authContext input.authentication.context)
        (SessionInstallation.current input.authentication finding.result.before.authentication).auth ∧
      Examples.CampusDirect.Duplex (Examples.CampusDirect.network input.authentication.context
        (SessionInstallation.current input.authentication finding.result.before.authentication) input.application finding.result.before.deployment.withdrawn) := by
  obtain ⟨prior, later, served, emission, covered, prefixTrace, authCount, networkCount, stored, sourceEq, emitted,
    valueEq, data, ttl, valid, ready, _⟩ :=
    report.observed_output_facts compliant finding member evidence payload id source observed event captured seen
  have matched := report.finding_matches compliant finding member
  change finding.result.payload.Matches at matched
  rw [payload] at matched
  have target := evidence.emission_target matched served stored emission emitted
  have ipEq := congrArg Prod.fst valueEq
  have dataEq := congrArg Prod.snd valueEq
  change captured.checked.packet.ip.packet = emission.decoded.ip.packet at ipEq
  change captured.checked.packet.datagram = emission.decoded.datagram at dataEq
  have header : captured.checked.header = served.ticket.value.entry.flow.output served.ticket.value.direction := by
    change captured.checked.packet.header = _
    simp only [UDP.DecodedIPv4.header, ipEq, dataEq]
    exact emission.header.trans target
  have duplex := (Examples.CampusDirect.duplex_reachable_iff input.authentication.context
    (SessionInstallation.current input.authentication finding.result.before.authentication) input.application finding.result.before.deployment.withdrawn).mpr
    ((Session.permits_iff _ _ _).mpr valid)
  exact ⟨prior, later, served, emission, covered, prefixTrace, authCount, networkCount, stored, sourceEq, emitted,
    valueEq, header, data, ttl, valid, ready, duplex⟩


theorem Report.forward_iff_duplex (report : Report input budget observations) (compliant : report.compliant = true)
    (finding : Finding input) (member : finding ∈ report.findings)
    (evidence : NetworkEvidence input finding.result.before) (payload : finding.result.payload = .network evidence)
    (served : Protocol.SafeHandoff.PacketResult) (stored : evidence.model.served = some served)
    (state : StatefulACL.CTState) (header : Header)
    (covered : ∃ requirement ∈ input.requirements, requirement.test.Holds header) :
    StatefulACL.Policy.evaluate served.configuration.pipeline.forwardDefault served.configuration.pipeline.forward state header = .permit ↔
      Examples.CampusDirect.Duplex (Examples.CampusDirect.network input.authentication.context
        (SessionInstallation.current input.authentication finding.result.before.authentication) input.application finding.result.before.deployment.withdrawn) := by
  have matched := report.finding_matches compliant finding member
  change finding.result.payload.Matches at matched
  rw [payload] at matched
  exact evidence.forward_iff_duplex matched served stored state header covered

theorem CheckedReport.finding_checks (report : CheckedReport input budget observations)
    (compliant : report.compliant = true) (finding : Finding input)
    (member : finding ∈ report.execution.findings) :
    finding.result.payload.topologyMatches = true ∧ finding.result.payload.applicationMatches = true := by
  have checked : report.execution.findings.all (fun finding =>
      finding.result.payload.topologyMatches && finding.result.payload.applicationMatches) = true :=
    (Bool.and_eq_true_iff.mp compliant).2
  exact Bool.and_eq_true_iff.mp ((List.all_eq_true.mp checked) finding member)

theorem NetworkEvidence.served_class_route (evidence : NetworkEvidence input before)
    (topology : evidence.topologyMatches = true) (application : evidence.applicationMatches = true)
    (served : Protocol.SafeHandoff.PacketResult) (stored : evidence.model.served = some served) :
    ∃ requirement ∈ input.requirements, requirement.test.Holds served.outcome.afterDestination ∧
      served.outcome.nextHop = some (match served.ticket.value.direction with
        | .original => "server" | .reply => "client") := by
  have routed : served.outcome.nextHop = some (match served.ticket.value.direction with
      | .original => "server" | .reply => "client") := by
    cases direction : served.ticket.value.direction <;>
      simpa only [NetworkEvidence.topologyMatches, stored, direction, decide_eq_true_eq] using topology
  have covered : input.requirements.any (fun requirement => requirement.test.accepts served.outcome.afterDestination) = true := by
    simpa only [NetworkEvidence.applicationMatches, stored] using application
  obtain ⟨requirement, member, matched⟩ := List.any_eq_true.mp covered
  exact ⟨requirement, member, (Match.accepts_iff _ _).mp matched, routed⟩

theorem CheckedReport.served_class_route (report : CheckedReport input budget observations)
    (compliant : report.compliant = true) (finding : Finding input) (member : finding ∈ report.execution.findings)
    (evidence : NetworkEvidence input finding.result.before) (payload : finding.result.payload = .network evidence)
    (served : Protocol.SafeHandoff.PacketResult) (stored : evidence.model.served = some served) :
    ∃ requirement ∈ input.requirements, requirement.test.Holds served.outcome.afterDestination ∧
      served.outcome.nextHop = some (match served.ticket.value.direction with
        | .original => "server" | .reply => "client") := by
  obtain ⟨topology, application⟩ := report.finding_checks compliant finding member
  rw [payload] at topology application
  exact evidence.served_class_route topology application served stored

theorem CheckedReport.served_forward_iff_duplex (report : CheckedReport input budget observations)
    (compliant : report.compliant = true) (finding : Finding input) (member : finding ∈ report.execution.findings)
    (evidence : NetworkEvidence input finding.result.before) (payload : finding.result.payload = .network evidence)
    (served : Protocol.SafeHandoff.PacketResult) (stored : evidence.model.served = some served) :
    StatefulACL.Policy.evaluate served.configuration.pipeline.forwardDefault served.configuration.pipeline.forward
      served.outcome.attachment.classification served.outcome.afterDestination = .permit ↔
      Examples.CampusDirect.Duplex (Examples.CampusDirect.network input.authentication.context
        (SessionInstallation.current input.authentication finding.result.before.authentication) input.application finding.result.before.deployment.withdrawn) := by
  obtain ⟨requirement, source, covered, _⟩ := report.served_class_route compliant finding member evidence payload served stored
  have matched := report.finding_matches compliant finding member
  rw [payload] at matched
  exact evidence.forward_iff_duplex matched served stored served.outcome.attachment.classification
    served.outcome.afterDestination ⟨requirement, source, covered⟩

end Netlib.Check.CampusDeployment
