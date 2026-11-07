import Netlib.Check.CampusTCPPrimaryTransport
import Netlib.Check.CampusTCPStartupAlignment
import Netlib.Check.CampusTCPStartupBasis

/-!
# Mixed startup services in their actual order

The chain retains every stored service, including early drops and no-output
processing. Each service starts at the preceding actual transport state.
-/

namespace Netlib.Check.CampusTCPRecoveryStartupTransport

open Protocol Protocol.TCP CampusTCPModel

namespace P
export CampusTCPPrimaryTransport (afterService serviceTransport)
end P

variable {input : Input}

def beforeTransport (served : Served input) : Checkpoint.Gateway :=
  ⟨served.before.tracker, served.before.admission⟩

def afterTransport (served : Served input) : Checkpoint.Gateway :=
  ⟨served.evidence.tracker, served.evidence.admission⟩

inductive ServiceChain : Checkpoint.Gateway → List (Served input) → Checkpoint.Gateway → Prop where
  | nil (current : Checkpoint.Gateway) : ServiceChain current [] current
  | cons (served : Served input) (primary : served.ticket.value.gateway = .primary)
      (before : beforeTransport served = current) (rest : ServiceChain (afterTransport served) tail final) :
      ServiceChain current (served :: tail) final

theorem ServiceChain.append (first : ServiceChain initial left middle) (second : ServiceChain middle right final) :
    ServiceChain initial (left ++ right) final := by
  induction first with
  | nil => exact second
  | cons served primary before rest ih => exact .cons served primary before (ih second)

theorem ServiceChain.fold (history : ServiceChain initial services final) : final = P.serviceTransport initial services := by
  induction history with
  | nil => rfl
  | cons served primary before rest ih =>
    simpa only [P.serviceTransport, List.foldl_cons, P.afterService, primary, afterTransport] using ih

theorem Step.before_transport (actual : Step input) (served : Served input)
    (recorded : actual.result.service = some served) (primary : served.ticket.value.gateway = .primary) :
    beforeTransport served = actual.before.primary.transport := by
  obtain ⟨_, _, _, _, _, _, before, _⟩ := CampusTCPOrigins.service_origin actual served recorded
  rw [beforeTransport, before, primary]
  rfl

theorem Step.service_chain (actual : Step input)
    (primary : ∀ served, actual.result.service = some served → served.ticket.value.gateway = .primary) :
    ServiceChain actual.before.primary.transport actual.result.service.toList actual.result.state.primary.transport := by
  have transport := CampusTCPPrimaryTransport.Step.primary_transport actual
  cases selected : actual.result.service with
  | none =>
    rw [selected] at transport
    rw [transport]
    exact .nil _
  | some served =>
    have atPrimary := primary served selected
    rw [selected] at transport
    simp only [Option.toList_some, P.serviceTransport, List.foldl_cons, List.foldl_nil,
      P.afterService, atPrimary] at transport
    rw [transport]
    exact .cons served atPrimary (Step.before_transport actual served selected atPrimary) (.nil _)

theorem Trace.service_chain (trace : Trace input initial events steps final remaining)
    (primary : ∀ served ∈ steps.filterMap (·.result.service), served.ticket.value.gateway = .primary) :
    ServiceChain initial.primary.transport (steps.filterMap (·.result.service)) final.primary.transport := by
  induction trace with
  | done state => exact .nil _
  | stop head blocked rest =>
    have chain := Step.service_chain head (fun served selected => primary served
      (by simp only [List.filterMap_cons, List.filterMap_nil, selected, List.mem_cons, List.not_mem_nil, or_false]))
    cases selected : head.result.service <;> simpa only [selected, List.filterMap_cons, List.filterMap_nil, Option.toList] using chain
  | next head supported rest ih =>
    have first := Step.service_chain head (fun served selected => primary served
      (by simp only [List.filterMap_cons, selected, List.mem_cons, true_or]))
    have second := ih (fun served member => primary served (by
      cases selected : head.result.service <;> simp only [List.filterMap_cons, selected]
      · exact member
      · exact List.mem_cons_of_mem _ member))
    have combined := first.append second
    cases selected : head.result.service <;> simpa only [selected, Option.toList, List.filterMap_cons, List.nil_append,
      List.cons_append] using combined

def PrimaryServices (report : Report input events) : Prop :=
  ∀ served ∈ report.steps.filterMap (·.result.service), served.ticket.value.gateway = .primary

theorem Report.service_chain (report : Report input events) (primary : PrimaryServices report) :
    ServiceChain .initial (report.steps.filterMap (·.result.service)) report.final.primary.transport :=
  Trace.service_chain report.trace primary

def phaseRank : Admission.Phase → Nat
  | .empty => 0
  | .syn .. => 1
  | .synAck .. => 2
  | .data .. => 3

private theorem legacy_phase_rank (phase : Admission.Phase) (attachment : ConntrackLifecycle.Attachment)
    (segment : Segment) (allowed : Admission.Allowed phase attachment segment observations) :
    phaseRank phase ≤ phaseRank (Admission.nextPhase phase attachment segment allowed) := by
  cases phase with
  | empty => simp [Admission.nextPhase, phaseRank]
  | syn entry iss window mss => simp [Admission.nextPhase, phaseRank]
  | synAck entry clientISS clientWindow serverISS serverWindow clientMSS serverMSS => simp [Admission.nextPhase, phaseRank]
  | data session =>
    simp only [Admission.nextPhase]
    split <;> split <;> exact Nat.le_refl _

theorem admission_phase_rank (value : AdmissionExecution.Result mode before packet lifecycle prepared) :
    phaseRank before.phase ≤ phaseRank (AdmissionExecution.Result.state value).phase := by
  rw [AdmissionExecution.Result.phase]
  cases mode with
  | ordinary => exact legacy_phase_rank _ _ _ _
  | startupRecovery =>
    simp only [AdmissionExecution.nextPhase, AdmissionStartupRecovery.nextPhase]
    split
    · exact legacy_phase_rank _ _ _ _
    · exact Nat.le_refl _

theorem Processing.phase_rank (value : CampusTCPService.Processing context before source zone mode) :
    phaseRank before.admission.phase ≤ phaseRank value.nextAdmission.phase := by
  rcases AdmissionExecution.commit_cases value.admitted value.outcome.state _ value.committed with
    kept | reset
  · rw [kept.1]
    exact admission_phase_rank value.admitted
  · have empty := AdmissionExecution.Result.fresh_phase value.admitted reset.2.1
    rw [empty]
    exact Nat.zero_le _

theorem Evidence.phase_rank (value : CampusTCPService.Evidence context before source zone ingress mode) :
    phaseRank before.admission.phase ≤ phaseRank value.admission.phase := by
  cases value with
  | mk checks operation =>
    cases operation with
    | earlyDrop denied => exact Nat.le_refl _
    | processed permitted processing => exact Processing.phase_rank processing

theorem ServiceChain.phase_rank (history : ServiceChain initial services final) :
    phaseRank initial.admission.phase ≤ phaseRank final.admission.phase := by
  induction history with
  | nil => exact Nat.le_refl _
  | cons served primary before rest ih =>
    have prior := Evidence.phase_rank served.evidence
    have same := congrArg Checkpoint.Gateway.admission before
    change served.before.admission = _ at same
    change phaseRank (afterTransport served).admission.phase ≤ _ at ih
    rw [same] at prior
    exact Nat.le_trans prior ih

variable {entry : NetfilterNAT.Entry}

private theorem legacy_before_entry (allowed : Admission.Allowed phase attachment segment observations)
    (selected : phase.entry = some entry) : attachment.entry = entry := by
  cases phase with
  | empty => cases selected
  | syn prior iss window mss | synAck prior iss window serverISS serverWindow mss serverMSS =>
    have same := Option.some.inj selected
    exact allowed.1.trans same
  | data session =>
    have same := Option.some.inj selected
    exact allowed.1.trans same

theorem admission_before_entry (value : AdmissionExecution.Result mode before packet lifecycle prepared)
    (selected : before.phase.entry = some entry) : prepared.attachment.entry = entry := by
  rcases AdmissionExecution.Result.legacy_or_stutter value with legacy | ⟨_, stutter⟩
  · exact legacy_before_entry legacy selected
  · exact Option.some.inj (stutter.entry.symm.trans selected)

theorem admission_existing (value : AdmissionExecution.Result mode before packet lifecycle prepared)
    (selected : before.phase.entry = some entry) : prepared.attachment.fresh = false := by
  cases fresh : prepared.attachment.fresh with
  | false => rfl
  | true =>
    have empty := AdmissionExecution.Result.fresh_phase value fresh
    rw [empty] at selected
    cases selected

theorem Processing.entry_preserved (value : CampusTCPService.Processing context before source zone mode)
    (selected : before.admission.phase.entry = some entry) : value.nextAdmission.phase.entry = some entry := by
  have committed := AdmissionExecution.Result.existing_committed value.admitted value.outcome.state
    (admission_existing value.admitted selected) value.nextAdmission value.committed
  rw [committed.1, AdmissionExecution.Result.selected_entry]
  exact congrArg some (admission_before_entry value.admitted selected)

theorem Evidence.entry_preserved (value : CampusTCPService.Evidence context before source zone ingress mode)
    (selected : before.admission.phase.entry = some entry) : value.admission.phase.entry = some entry := by
  cases value with
  | mk checks operation =>
    cases operation with
    | earlyDrop denied => exact selected
    | processed permitted processing => exact Processing.entry_preserved processing selected

theorem ServiceChain.entry_preserved (history : ServiceChain initial services final)
    (selected : initial.admission.phase.entry = some entry) : final.admission.phase.entry = some entry := by
  induction history with
  | nil => exact selected
  | cons served primary before rest ih =>
    apply ih
    have current : served.before.admission.phase.entry = some entry := by
      change (beforeTransport served).admission.phase.entry = some entry
      rw [before]
      exact selected
    exact Evidence.entry_preserved served.evidence current

def TrackerLinked (gateway : Checkpoint.Gateway) : Prop :=
  ∀ entry, gateway.admission.phase.entry = some entry →
    ∃ record ∈ gateway.tracker.records, record.entry = entry

theorem TrackerLinked.initial : TrackerLinked .initial := by
  intro entry selected
  cases selected

theorem Processing.tracker_linked (value : CampusTCPService.Processing context before source zone mode) :
    TrackerLinked ⟨value.outcome.state, value.nextAdmission⟩ := by
  intro entry selected
  rcases AdmissionExecution.commit_cases value.admitted value.outcome.state _ value.committed with
    kept | reset
  · have same : value.prepared.attachment.entry = entry := by
      rw [kept.1, AdmissionExecution.Result.selected_entry] at selected
      exact Option.some.inj selected
    rw [← same]
    exact (Admission.confirmed_correct _ _).mp kept.2
  · rw [reset.1] at selected
    cases selected

theorem Evidence.tracker_linked (value : CampusTCPService.Evidence context before source zone ingress mode)
    (prior : TrackerLinked ⟨before.tracker, before.admission⟩) :
    TrackerLinked ⟨value.tracker, value.admission⟩ := by
  cases value with
  | mk checks operation =>
    cases operation with
    | earlyDrop denied => exact prior
    | processed permitted processing => exact Processing.tracker_linked processing

theorem ServiceChain.tracker_linked (history : ServiceChain initial services final)
    (prior : TrackerLinked initial) : TrackerLinked final := by
  induction history with
  | nil => exact prior
  | cons served primary before rest ih =>
    apply ih
    apply Evidence.tracker_linked served.evidence
    change TrackerLinked (beforeTransport served)
    rw [before]
    exact prior

theorem Report.tracker_linked (report : Report input events) (primary : PrimaryServices report) :
    TrackerLinked report.final.primary.transport :=
  (Report.service_chain report primary).tracker_linked TrackerLinked.initial

theorem Report.confirmed_entry (report : Report input events) (primary : PrimaryServices report)
    (selected : report.final.primary.transport.admission.phase.entry = some entry) :
    Admission.confirmed entry report.final.primary.transport.tracker = true :=
  (Admission.confirmed_correct _ _).mpr (Report.tracker_linked report primary entry selected)

end Netlib.Check.CampusTCPRecoveryStartupTransport
