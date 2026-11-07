import Netlib.Check.CampusTCPRecoveryStartupCurrentEntry

/-!
# The tracker while startup admission remains empty

A failed fresh service keeps the preceding tracker. Confirming a fresh
record also keeps its nonempty admission state.
-/

namespace Netlib.Check.CampusTCPRecoveryStartupEmptyTracker

open Protocol Protocol.TCP CampusTCPModel
open CampusTCPRecoveryStartupTransport (ServiceChain beforeTransport afterTransport)
open CampusTCPRecoveryStartupCurrentEntry (History)

variable {input : Input}

private theorem finish_state_cases (computed : TCP.WireForwarding.finish pipeline packet valid prepared = .ok outcome) :
    outcome.state = prepared.state ∨ outcome.state.records = prepared.state.records ++ [⟨prepared.attachment.entry, false⟩] := by
  obtain ⟨model, processed, same⟩ := TCP.WireForwarding.finish_realizes _ _ _ _ _ computed
  rw [same]
  change model.state = prepared.state ∨ model.state.records = _
  rcases ConntrackLifecycle.process_state _ _ _ processed with unchanged | ⟨_, _, records⟩
  · exact Or.inl unchanged
  · exact Or.inr records

private theorem process_state_cases (computed : TCP.WireForwarding.process pipeline packet valid prepared = .ok outcome) :
    outcome.state = prepared.state ∨ outcome.state.records = prepared.state.records ++ [⟨prepared.attachment.entry, false⟩] := by
  unfold TCP.WireForwarding.process at computed
  split at computed
  · exact finish_state_cases computed
  · split at computed
    · cases computed
      exact Or.inl rfl
    · exact finish_state_cases computed

theorem Processing.empty_tracker (value : CampusTCPService.Processing context before source zone mode)
    (empty : value.nextAdmission.phase = .empty) :
    before.admission.phase = .empty ∧ value.outcome.state = before.tracker := by
  rcases AdmissionExecution.commit_cases value.admitted value.outcome.state _ value.committed with kept | reset
  · have selected := AdmissionExecution.Result.selected_entry value.admitted
    rw [← kept.1, empty] at selected
    cases selected
  · have prior := AdmissionExecution.Result.fresh_phase value.admitted reset.2.1
    refine ⟨prior, ?_⟩
    have start := (ConntrackLifecycle.prepare_fresh before.tracker _ value.prepared value.attached reset.2.1).1
    rcases process_state_cases value.computed with unchanged | records
    · exact unchanged.trans start
    · have confirmed : Admission.confirmed value.prepared.attachment.entry value.outcome.state = true := by
        apply (Admission.confirmed_correct _ _).mpr
        refine ⟨⟨value.prepared.attachment.entry, false⟩, ?_, rfl⟩
        rw [records]
        exact List.mem_append_right _ (List.mem_singleton_self _)
      rw [confirmed] at reset
      cases reset.2.2

theorem Evidence.empty_tracker (value : CampusTCPService.Evidence context before source zone ingress mode)
    (empty : value.admission.phase = .empty) : before.admission.phase = .empty ∧ value.tracker = before.tracker := by
  cases value with
  | mk checks operation =>
    cases operation with
    | earlyDrop denied => exact ⟨empty, rfl⟩
    | processed permitted processing => exact Processing.empty_tracker processing empty

theorem ServiceChain.empty_tracker (chain : ServiceChain initial services final) (empty : final.admission.phase = .empty) :
    initial.admission.phase = .empty ∧ final.tracker = initial.tracker := by
  induction chain with
  | nil => exact ⟨empty, rfl⟩
  | cons served primary before rest ih =>
    obtain ⟨afterEmpty, finalTracker⟩ := ih empty
    obtain ⟨beforeEmpty, afterTracker⟩ := Evidence.empty_tracker served.evidence afterEmpty
    have admission := congrArg (fun state : Checkpoint.Gateway => state.admission.phase) before
    have tracker := congrArg Checkpoint.Gateway.tracker before
    refine ⟨admission.symm.trans beforeEmpty, ?_⟩
    exact finalTracker.trans (afterTracker.trans tracker)

theorem History.fresh_keys (history : History base report)
    (profile : CampusTCPStartupNative.Profile (input.contextFor .primary) (beforeService input base.final .primary) input.zone header)
    (empty : report.final.primary.transport.admission.phase = .empty) :
    ConntrackLifecycle.FreshKeys report.final.primary.transport.tracker profile.entry := by
  have trackers := (ServiceChain.empty_tracker
    (CampusTCPRecoveryStartupTransport.Trace.service_chain history.trace history.primary) empty).2
  rw [trackers]
  exact profile.freshKeys

end Netlib.Check.CampusTCPRecoveryStartupEmptyTracker
