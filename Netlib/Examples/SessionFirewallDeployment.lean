import Netlib.Check.SessionFirewall
import Netlib.Protocol.BufferedLifecycle

/-!
# Session policy at tracked forwarding

The installed forward filter must equal the policy for the current session snapshot.
Requirements bind that session's principal and scope to packet classes after destination NAT.
That binding and synchronous installation are deployment assumptions.
Cached tracking entries supply no permission of their own.
The buffer theorem concerns new admissions; earlier queued packets can still be served.
-/

namespace Netlib.Examples.SessionFirewallDeployment

open Packet Protocol

variable {context : Context} {session : EAPSession.State} {requirements : List Compile.SessionFirewall.Intent}

def pipeline (compiled : Compile.SessionFirewall.Certified context session requirements)
    (routes : List (Routing.Entry String)) (late : StatefulACL.Policy := [])
    (lateDefault : Action := .permit) : ConntrackLifecycle.Pipeline :=
  { routes, forward := compiled.statefulSnapshot.compile, late, lateDefault }

def snapshotPipeline (snapshot : Import.NftablesStateful.Snapshot)
    (routes : List (Routing.Entry String)) (late : StatefulACL.Policy := [])
    (lateDefault : Action := .permit) : ConntrackLifecycle.Pipeline :=
  { routes, forward := snapshot.compile, late, lateDefault }

def ForwardEquivalent (active : ConntrackLifecycle.Pipeline)
    (compiled : Compile.SessionFirewall.Certified context session requirements) : Prop :=
  ∀ state header, StatefulACL.Policy.evaluate active.forwardDefault active.forward state header =
    compiled.statefulSnapshot.evaluate state header

theorem pipeline_equivalent (compiled : Compile.SessionFirewall.Certified context session requirements)
    (routes : List (Routing.Entry String)) (late : StatefulACL.Policy) (lateDefault : Action) :
    ForwardEquivalent (pipeline compiled routes late lateDefault) compiled := by
  intro state header
  exact compiled.statefulSnapshot.compile_evaluate .deny state header

theorem finding_forward_equivalent {input : Check.SessionFirewall.Input}
    (finding : Check.SessionFirewall.Finding input) (passed : finding.passed = true)
    (routes : List (Routing.Entry String)) (late : StatefulACL.Policy) (lateDefault : Action) :
    ForwardEquivalent (snapshotPipeline finding.checkpoint.firewall routes late lateDefault) finding.compiled := by
  intro state header
  change StatefulACL.Policy.evaluate .deny finding.checkpoint.firewall.compile state header = _
  rw [finding.checkpoint.firewall.compile_evaluate]
  have same : finding.checkpoint.firewall.permits state header = finding.compiled.statefulSnapshot.permits state header :=
    (finding.correct.mp passed state header).trans (finding.compiled.statefulSnapshot_permits state header).symm
  cases native : finding.checkpoint.firewall.evaluate state header <;>
    cases generated : finding.compiled.statefulSnapshot.evaluate state header <;>
      simp_all [Import.NftablesStateful.Snapshot.permits]

theorem output_compiled_permit (compiled : Compile.SessionFirewall.Certified context session requirements)
    (active : ConntrackLifecycle.Pipeline) (installed : ForwardEquivalent active compiled)
    (tracker : ConntrackLifecycle.State) (input : ConntrackLifecycle.Input)
    (outcome : ConntrackLifecycle.Outcome) (wire : Header)
    (accepted : ConntrackLifecycle.step active tracker input = .ok outcome) (forwarded : outcome.output = some wire) :
    compiled.snapshot.permits outcome.afterDestination = true := by
  have allowed := (ConntrackLifecycle.step_filters active tracker input outcome wire accepted forwarded).2.1
  have native : compiled.statefulSnapshot.evaluate outcome.attachment.classification outcome.afterDestination = .permit :=
    (installed outcome.attachment.classification outcome.afterDestination).symm.trans allowed
  rw [← compiled.statefulSnapshot_permits outcome.attachment.classification outcome.afterDestination]
  simp [Import.NftablesStateful.Snapshot.permits, native]

theorem output_current_permission (compiled : Compile.SessionFirewall.Certified context session requirements)
    (safe : session.Safe context) (active : ConntrackLifecycle.Pipeline) (installed : ForwardEquivalent active compiled)
    (tracker : ConntrackLifecycle.State) (input : ConntrackLifecycle.Input) (outcome : ConntrackLifecycle.Outcome) (wire : Header)
    (accepted : ConntrackLifecycle.step active tracker input = .ok outcome) (forwarded : outcome.output = some wire) :
    ∃ requirement ∈ requirements, requirement.test.Holds outcome.afterDestination ∧
      Session.Valid context session.session requirement.scope ∧
      EAPAuth.State.Ready (EAPSession.authContext context) session.auth := by
  exact compiled.permitted_valid safe outcome.afterDestination
    (output_compiled_permit compiled active installed tracker input outcome wire accepted forwarded)

theorem output_matching_scope_valid (compiled : Compile.SessionFirewall.Certified context session requirements)
    (safe : session.Safe context) (active : ConntrackLifecycle.Pipeline) (installed : ForwardEquivalent active compiled)
    (tracker : ConntrackLifecycle.State) (input : ConntrackLifecycle.Input)
    (outcome : ConntrackLifecycle.Outcome) (wire : Header)
    (accepted : ConntrackLifecycle.step active tracker input = .ok outcome) (forwarded : outcome.output = some wire)
    (requirement : Compile.SessionFirewall.Intent) (member : requirement ∈ requirements)
    (matched : requirement.test.Holds outcome.afterDestination) :
    Session.Valid context session.session requirement.scope ∧
      EAPAuth.State.Ready (EAPSession.authContext context) session.auth := by
  have permitted := output_compiled_permit compiled active installed tracker input outcome wire accepted forwarded
  cases allowed : session.session.permits context requirement.scope with
  | false =>
    have denied := compiled.denied_requirement requirement member allowed outcome.afterDestination matched
    simp [denied] at permitted
  | true =>
    have valid := (Session.permits_iff _ _ _).mp allowed
    exact ⟨valid, safe.1 (safe.2.1.symm.trans valid.1)⟩

theorem output_generated_permission (compiled : Compile.SessionFirewall.Certified context session requirements)
    (safe : session.Safe context) (routes : List (Routing.Entry String))
    (late : StatefulACL.Policy) (lateDefault : Action)
    (tracker : ConntrackLifecycle.State) (input : ConntrackLifecycle.Input) (outcome : ConntrackLifecycle.Outcome) (wire : Header)
    (accepted : ConntrackLifecycle.step (pipeline compiled routes late lateDefault) tracker input = .ok outcome)
    (forwarded : outcome.output = some wire) :
    ∃ requirement ∈ requirements, requirement.test.Holds outcome.afterDestination ∧
      Session.Valid context session.session requirement.scope ∧
      EAPAuth.State.Ready (EAPSession.authContext context) session.auth :=
  output_current_permission compiled safe _ (pipeline_equivalent compiled routes late lateDefault)
    tracker input outcome wire accepted forwarded

theorem checked_output_current_permission {input : Check.SessionFirewall.Input}
    (report : Check.SessionFirewall.Report input) (compliant : report.compliant = true)
    (finding : Check.SessionFirewall.Finding input) (member : finding ∈ report.findings)
    (routes : List (Routing.Entry String)) (late : StatefulACL.Policy) (lateDefault : Action)
    (tracker : ConntrackLifecycle.State) (packet : ConntrackLifecycle.Input)
    (outcome : ConntrackLifecycle.Outcome) (wire : Header)
    (accepted : ConntrackLifecycle.step (snapshotPipeline finding.checkpoint.firewall routes late lateDefault)
      tracker packet = .ok outcome) (forwarded : outcome.output = some wire) :
    ∃ requirement ∈ input.requirements, requirement.test.Holds outcome.afterDestination ∧
      Session.Valid input.authentication.context
        (Check.SessionFirewall.stateAt input.authentication finding.checkpoint.after).session requirement.scope ∧
      EAPAuth.State.Ready (EAPSession.authContext input.authentication.context)
        (Check.SessionFirewall.stateAt input.authentication finding.checkpoint.after).auth :=
  output_current_permission finding.compiled (Check.SessionFirewall.stateAt_safe _ _) _
    (finding_forward_equivalent finding (report.finding_passed compliant finding member) routes late lateDefault)
    tracker packet outcome wire accepted forwarded

theorem output_none_of_denied (compiled : Compile.SessionFirewall.Certified context session requirements)
    (safe : session.Safe context) (active : ConntrackLifecycle.Pipeline) (installed : ForwardEquivalent active compiled)
    (denied : ∀ requirement ∈ requirements, session.session.permits context requirement.scope = false)
    (tracker : ConntrackLifecycle.State) (input : ConntrackLifecycle.Input) (outcome : ConntrackLifecycle.Outcome)
    (accepted : ConntrackLifecycle.step active tracker input = .ok outcome) : outcome.output = none := by
  cases output : outcome.output with
  | none => rfl
  | some wire =>
    obtain ⟨requirement, member, _, valid, _⟩ :=
      output_current_permission compiled safe active installed tracker input outcome wire accepted output
    have allowed := (Session.permits_iff _ _ _).mpr valid
    simp [denied requirement member] at allowed

theorem output_none_of_unauthorized (compiled : Compile.SessionFirewall.Certified context session requirements)
    (safe : session.Safe context) (active : ConntrackLifecycle.Pipeline) (installed : ForwardEquivalent active compiled)
    (unauthorized : session.auth.authorized = false)
    (tracker : ConntrackLifecycle.State) (input : ConntrackLifecycle.Input) (outcome : ConntrackLifecycle.Outcome)
    (accepted : ConntrackLifecycle.step active tracker input = .ok outcome) : outcome.output = none :=
  output_none_of_denied compiled safe active installed
    (fun requirement _ => EAPSession.unauthorized_denied context session requirement.scope safe.2.1 unauthorized)
    tracker input outcome accepted

theorem output_none_without_credential (compiled : Compile.SessionFirewall.Certified context session requirements)
    (safe : session.Safe context) (active : ConntrackLifecycle.Pipeline) (installed : ForwardEquivalent active compiled)
    (missing : session.session.credential = none)
    (tracker : ConntrackLifecycle.State) (input : ConntrackLifecycle.Input) (outcome : ConntrackLifecycle.Outcome)
    (accepted : ConntrackLifecycle.step active tracker input = .ok outcome) : outcome.output = none := by
  apply output_none_of_denied compiled safe active installed _ tracker input outcome accepted
  intro requirement _
  simp [Session.permits, Session.claims, missing]

theorem postlogoff_output_none (context : Context) (before : EAPSession.State) (safe : before.Safe context)
    (compiled : Compile.SessionFirewall.Certified context (EAPSession.step context before (.authentication .logoff)) requirements)
    (active : ConntrackLifecycle.Pipeline) (installed : ForwardEquivalent active compiled)
    (tracker : ConntrackLifecycle.State) (input : ConntrackLifecycle.Input) (outcome : ConntrackLifecycle.Outcome)
    (accepted : ConntrackLifecycle.step active tracker input = .ok outcome) : outcome.output = none :=
  output_none_of_unauthorized compiled (EAPSession.step_safe _ _ _ safe) active installed rfl tracker input outcome accepted

theorem postclose_output_none (context : Context) (before : EAPSession.State) (safe : before.Safe context)
    (compiled : Compile.SessionFirewall.Certified context (EAPSession.step context before .close) requirements)
    (active : ConntrackLifecycle.Pipeline) (installed : ForwardEquivalent active compiled)
    (tracker : ConntrackLifecycle.State) (input : ConntrackLifecycle.Input) (outcome : ConntrackLifecycle.Outcome)
    (accepted : ConntrackLifecycle.step active tracker input = .ok outcome) : outcome.output = none :=
  output_none_of_unauthorized compiled (EAPSession.step_safe _ _ _ safe) active installed rfl tracker input outcome accepted

theorem postrevoke_output_none (context : Context) (before : EAPSession.State) (safe : before.Safe context)
    (compiled : Compile.SessionFirewall.Certified context (EAPSession.step context before (.application .revoke)) requirements)
    (active : ConntrackLifecycle.Pipeline) (installed : ForwardEquivalent active compiled)
    (tracker : ConntrackLifecycle.State) (input : ConntrackLifecycle.Input) (outcome : ConntrackLifecycle.Outcome)
    (accepted : ConntrackLifecycle.step active tracker input = .ok outcome) : outcome.output = none :=
  output_none_without_credential compiled (EAPSession.step_safe _ _ _ safe) active installed rfl tracker input outcome accepted

private theorem packet_operation (tracker : ConntrackLifecycle.State) (call : ConntrackLifecycle.Call)
    (result : ConntrackLifecycle.Operations.Result)
    (accepted : ConntrackLifecycle.Operations.step tracker (.packet call) = .ok result) :
    ∃ outcome, ConntrackLifecycle.step call.pipeline tracker call.input = .ok outcome ∧ result.packet = some outcome := by
  cases found : ConntrackLifecycle.step call.pipeline tracker call.input with
  | error error => simp [ConntrackLifecycle.Operations.step, found, bind, Except.bind] at accepted
  | ok outcome =>
    simp [ConntrackLifecycle.Operations.step, found, bind, Except.bind, pure] at accepted
    cases accepted
    exact ⟨outcome, rfl, rfl⟩

theorem buffered_admission_current_permission (compiled : Compile.SessionFirewall.Certified context session requirements)
    (safe : session.Safe context) (active : ConntrackLifecycle.Pipeline) (installed : ForwardEquivalent active compiled)
    (before : BufferedLifecycle.State) (input : ConntrackLifecycle.Input) (result : BufferedLifecycle.Result) (wire : Header)
    (accepted : BufferedLifecycle.step before (.operation (.packet ⟨active, input⟩)) = .ok result)
    (admitted : wire ∈ result.admitted) :
    ∃ outcome, ConntrackLifecycle.step active before.tracker input = .ok outcome ∧ outcome.output = some wire ∧
      ∃ requirement ∈ requirements, requirement.test.Holds outcome.afterDestination ∧
        Session.Valid context session.session requirement.scope ∧
        EAPAuth.State.Ready (EAPSession.authContext context) session.auth := by
  obtain ⟨operation, computed, stored, _⟩ := BufferedLifecycle.step_operation before _ result accepted
  obtain ⟨outcome, processed, packet⟩ := packet_operation before.tracker _ operation computed
  have output : outcome.output = some wire := by
    simpa [BufferedLifecycle.Result.admitted, stored, BufferedLifecycle.operationOutput, packet] using admitted
  exact ⟨outcome, processed, output,
    output_current_permission compiled safe active installed before.tracker input outcome wire processed output⟩

theorem buffered_admissions_empty_of_denied (compiled : Compile.SessionFirewall.Certified context session requirements)
    (safe : session.Safe context) (active : ConntrackLifecycle.Pipeline) (installed : ForwardEquivalent active compiled)
    (denied : ∀ requirement ∈ requirements, session.session.permits context requirement.scope = false)
    (before : BufferedLifecycle.State) (input : ConntrackLifecycle.Input) (result : BufferedLifecycle.Result)
    (accepted : BufferedLifecycle.step before (.operation (.packet ⟨active, input⟩)) = .ok result) :
    result.admitted = [] := by
  cases arrivals : result.admitted with
  | nil => rfl
  | cons wire rest =>
    have member : wire ∈ result.admitted := by simp [arrivals]
    obtain ⟨_, _, _, requirement, belongs, _, valid, _⟩ :=
      buffered_admission_current_permission compiled safe active installed before input result wire accepted member
    have allowed := (Session.permits_iff _ _ _).mpr valid
    simp [denied requirement belongs] at allowed

end Netlib.Examples.SessionFirewallDeployment
