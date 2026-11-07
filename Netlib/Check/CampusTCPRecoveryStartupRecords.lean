import Netlib.Check.CampusTCPRecoveryStartupTransport

/-!
# Actual reply records across startup service

Reply preparation marks the selected real record. Later service retains a
record already marked as having seen a reply, including no-output service.
-/

namespace Netlib.Check.CampusTCPRecoveryStartupRecords

open Protocol Protocol.TCP CampusTCPModel
open CampusTCPRecoveryStartupTransport (ServiceChain beforeTransport afterTransport)

variable {input : Input}

private theorem mark_fixed (record : ConntrackLifecycle.Record) (seen : record.seenReply = true) :
    ConntrackLifecycle.State.markRecord flow record = record := by
  unfold ConntrackLifecycle.State.markRecord
  split
  · cases record with
    | mk entry reply => simp only at seen; subst reply; rfl
  · rfl

private theorem mark_member (state : ConntrackLifecycle.State) (record : ConntrackLifecycle.Record)
    (member : record ∈ state.records) (seen : record.seenReply = true) :
    record ∈ (state.markReply flow).records :=
  List.mem_map.mpr ⟨record, member, mark_fixed record seen⟩

private theorem prepare_member (prepared : ConntrackLifecycle.Prepared packet)
    (computed : ConntrackLifecycle.prepare state packet = .ok prepared)
    (record : ConntrackLifecycle.Record) (member : record ∈ state.records) (seen : record.seenReply = true) :
    record ∈ prepared.state.records := by
  cases fresh : prepared.attachment.fresh with
  | true => rw [(ConntrackLifecycle.prepare_fresh _ _ _ computed fresh).1]; exact member
  | false =>
    cases direction : prepared.attachment.direction with
    | original =>
      obtain ⟨_, _, _, _, same⟩ := ConntrackLifecycle.prepare_existing_original _ _ _ computed fresh direction
      rw [same]
      exact member
    | reply =>
      rw [(ConntrackLifecycle.prepare_reply _ _ _ computed direction).2.2]
      exact mark_member state record member seen

private theorem finish_member (computed : TCP.WireForwarding.finish pipeline packet valid prepared = .ok outcome)
    (record : ConntrackLifecycle.Record) (member : record ∈ prepared.state.records) : record ∈ outcome.state.records := by
  obtain ⟨model, processed, same⟩ := TCP.WireForwarding.finish_realizes _ _ _ _ _ computed
  rw [same]
  change record ∈ model.state.records
  rcases ConntrackLifecycle.process_state _ _ _ processed with same | ⟨_, _, records⟩
  · rw [same]; exact member
  · rw [records]; exact List.mem_append_left _ member

private theorem process_member (computed : TCP.WireForwarding.process pipeline packet valid prepared = .ok outcome)
    (record : ConntrackLifecycle.Record) (member : record ∈ prepared.state.records) : record ∈ outcome.state.records := by
  unfold TCP.WireForwarding.process at computed
  split at computed
  · exact finish_member computed record member
  · split at computed
    · cases computed; exact member
    · exact finish_member computed record member

theorem Processing.retains_reply (value : CampusTCPService.Processing context before source zone mode)
    (record : ConntrackLifecycle.Record) (member : record ∈ before.tracker.records) (seen : record.seenReply = true) :
    record ∈ value.outcome.state.records :=
  process_member value.computed record (prepare_member value.prepared value.attached record member seen)

theorem Evidence.retains_reply (value : CampusTCPService.Evidence context before source zone ingress mode)
    (record : ConntrackLifecycle.Record) (member : record ∈ before.tracker.records) (seen : record.seenReply = true) :
    record ∈ value.tracker.records := by
  cases value with
  | mk checks operation =>
    cases operation with
    | earlyDrop denied => exact member
    | processed permitted processing => exact Processing.retains_reply processing record member seen

theorem ServiceChain.retains_reply (history : ServiceChain initial services final) (record : ConntrackLifecycle.Record)
    (member : record ∈ initial.tracker.records) (seen : record.seenReply = true) : record ∈ final.tracker.records := by
  induction history with
  | nil => exact member
  | cons served primary before rest ih =>
    apply ih
    apply Evidence.retains_reply served.evidence record _ seen
    change record ∈ (beforeTransport served).tracker.records
    rw [before]
    exact member

private theorem marked_entry_seen (state : ConntrackLifecycle.State) (record : ConntrackLifecycle.Record)
    (member : record ∈ (state.markReply entry.flow).records) (selected : record.entry = entry) : record.seenReply = true := by
  obtain ⟨prior, _, same⟩ := List.mem_map.mp member
  have picked : prior.entry = entry := by
    rw [← same, ConntrackLifecycle.State.markRecord_entry] at selected
    exact selected
  rw [← same]
  simp only [ConntrackLifecycle.State.markRecord, picked, ite_true]

theorem Processing.reply_record (value : CampusTCPService.Processing context before source zone mode)
    (reply : value.prepared.attachment.direction = .reply) :
    ∃ record ∈ value.outcome.state.records, record.entry = value.prepared.attachment.entry ∧ record.seenReply = true := by
  obtain ⟨_, existing, marked⟩ := ConntrackLifecycle.prepare_reply _ _ _ value.attached reply
  have current := value.existing_state existing
  have committed := AdmissionExecution.Result.existing_committed value.admitted value.outcome.state existing
    value.nextAdmission value.committed
  obtain ⟨record, member, selected⟩ := committed.2.1
  refine ⟨record, member, selected, marked_entry_seen before.tracker record ?_ selected⟩
  rw [current, marked] at member
  exact member

theorem ServiceChain.after_reply_record (history : ServiceChain initial services final) (served : Served input)
    (member : served ∈ services) (record : ConntrackLifecycle.Record)
    (recorded : record ∈ (afterTransport served).tracker.records) (seen : record.seenReply = true) :
    record ∈ final.tracker.records := by
  induction history with
  | nil => cases member
  | cons head primary before rest ih =>
    rcases List.mem_cons.mp member with same | later
    · subst served
      exact ServiceChain.retains_reply rest record recorded seen
    · exact ih later

theorem ServiceChain.reply_record (history : ServiceChain initial services final) (served : Served input)
    (member : served ∈ services)
    (processing : CampusTCPService.Processing (input.contextFor served.ticket.value.gateway) served.before
      served.ticket.value.source input.zone served.mode) (selected : served.evidence.processing = some processing)
    (reply : processing.prepared.attachment.direction = .reply) :
    ∃ record ∈ final.tracker.records, record.entry = processing.prepared.attachment.entry ∧ record.seenReply = true := by
  obtain ⟨record, present, entry, seen⟩ := Processing.reply_record processing reply
  have states := served.evidence.processing_states processing selected
  refine ⟨record, ServiceChain.after_reply_record history served member record ?_ seen, entry, seen⟩
  change record ∈ served.evidence.tracker.records
  rw [states.1]
  exact present

end Netlib.Check.CampusTCPRecoveryStartupRecords
