import Netlib.Protocol.TCP.Checkpoint

/-!
# Sources of committed gateway observations

Each source is an operation in the same reachable checkpoint history.
An unconfirmed fresh drop contributes no committed observation.
-/

namespace Netlib.Protocol.TCP.Checkpoint

inductive History.Occurs : {final : Gateway} → History final →
    {before : Gateway} → History before → {mode : X.Mode} → Transition before mode → Prop where
  | current (prior : History before) (transition : Transition before mode) :
      Occurs (.advance prior transition) prior transition
  | past {final : Gateway} {history : History final} {before : Gateway}
      {prior : History before} {transition : Transition before mode}
      (present : Occurs history prior transition) (later : Transition final laterMode) :
      Occurs (.advance history later) prior transition

theorem History.Occurs.earlier (present : History.Occurs history prior transition) :
    prior.length < history.length := by
  induction present with
  | current prior transition => simp only [History.length]; omega
  | past present later ih => simp only [History.length]; omega

structure ObservationOrigin (history : History gateway) (index : Nat) (seen : Admission.Seen) where
  before : Gateway
  prior : History before
  mode : X.Mode
  transition : Transition before mode
  member : history.Occurs prior transition
  position : index = before.admission.observations.length
  actual : seen = Admission.observe transition.request.source transition.request.wire.lifecycle transition.prepared

theorem ObservationOrigin.earlier (origin : ObservationOrigin history index seen) :
    origin.prior.length < history.length := origin.member.earlier

theorem ObservationOrigin.bytes (origin : ObservationOrigin history index seen) :
    seen.bytes = origin.transition.request.source.bytes := congrArg Admission.Seen.bytes origin.actual

theorem ObservationOrigin.segment (origin : ObservationOrigin history index seen) :
    seen.segment = origin.transition.request.source.packet.segment := congrArg Admission.Seen.segment origin.actual

theorem ObservationOrigin.attachment (origin : ObservationOrigin history index seen) :
    seen.attachment = origin.transition.prepared.attachment := congrArg Admission.Seen.attachment origin.actual

theorem History.observation_origin (history : History gateway) (index : Nat) (seen : Admission.Seen)
    (selected : gateway.admission.observations[index]? = some seen) :
    Nonempty (ObservationOrigin history index seen) := by
  induction history with
  | initial => simp [Gateway.initial, Admission.State.initial] at selected
  | @advance before mode prior transition ih =>
    rcases AdmissionExecution.commit_cases transition.admitted transition.outcome.state transition.nextAdmission transition.committed with
      committed | discarded
    · have observations : transition.after.admission.observations =
          before.admission.observations ++
            [Admission.observe transition.request.source transition.request.wire.lifecycle transition.prepared] := by
        change transition.nextAdmission.observations = _
        rw [committed.1, AdmissionExecution.Result.ledger transition.admitted]
      rw [observations] at selected
      by_cases earlier : index < before.admission.observations.length
      · rw [List.getElem?_append_left earlier] at selected
        obtain ⟨origin⟩ := ih selected
        exact ⟨⟨origin.before, origin.prior, origin.mode, origin.transition, .past origin.member transition,
          origin.position, origin.actual⟩⟩
      · have bound := (List.getElem?_eq_some_iff.mp selected).1
        simp only [List.length_append, List.length_cons, List.length_nil] at bound
        have same : index = before.admission.observations.length := by omega
        subst index
        rw [List.getElem?_append_right (Nat.le_refl before.admission.observations.length)] at selected
        simp only [Nat.sub_self, List.getElem?_cons_zero, Option.some.injEq] at selected
        exact ⟨⟨before, prior, mode, transition, .current prior transition, rfl, selected.symm⟩⟩
    · have empty : transition.after.admission.observations = [] := by
        change transition.nextAdmission.observations = []
        rw [discarded.1]
        rfl
      simp only [empty, List.getElem?_nil] at selected
      cases selected

def History.observationOrigin (history : History gateway) (index : Nat) (seen : Admission.Seen)
    (selected : gateway.admission.observations[index]? = some seen) : ObservationOrigin history index seen :=
  match history with
  | .initial => by simp [Gateway.initial, Admission.State.initial] at selected
  | @History.advance before mode prior transition =>
    if confirmed : Admission.confirmed transition.prepared.attachment.entry transition.outcome.state = true then
      have committed : transition.nextAdmission = AdmissionExecution.Result.state transition.admitted := by
        rcases AdmissionExecution.commit_cases transition.admitted transition.outcome.state transition.nextAdmission transition.committed with
          committed | discarded
        · exact committed.1
        · rw [confirmed] at discarded
          cases discarded.2.2
      have observations : transition.after.admission.observations =
          before.admission.observations ++
            [Admission.observe transition.request.source transition.request.wire.lifecycle transition.prepared] := by
        change transition.nextAdmission.observations = _
        rw [committed, AdmissionExecution.Result.ledger transition.admitted]
      if earlier : index < before.admission.observations.length then
        have preceding : before.admission.observations[index]? = some seen := by
          rw [observations, List.getElem?_append_left earlier] at selected
          exact selected
        let origin := prior.observationOrigin index seen preceding
        ⟨origin.before, origin.prior, origin.mode, origin.transition, .past origin.member transition, origin.position, origin.actual⟩
      else by
        have appended := selected
        rw [observations] at appended
        have bound := (List.getElem?_eq_some_iff.mp appended).1
        have position : index = before.admission.observations.length := by
          simp only [List.length_append, List.length_cons, List.length_nil] at bound
          omega
        have actual : seen = Admission.observe transition.request.source transition.request.wire.lifecycle transition.prepared := by
          rw [position, List.getElem?_append_right (Nat.le_refl before.admission.observations.length)] at appended
          simp only [Nat.sub_self, List.getElem?_cons_zero, Option.some.injEq] at appended
          exact appended.symm
        exact ⟨before, prior, mode, transition, .current prior transition, position, actual⟩
    else by
      have empty : transition.after.admission.observations = [] := by
        change transition.nextAdmission.observations = []
        rcases AdmissionExecution.commit_cases transition.admitted transition.outcome.state transition.nextAdmission transition.committed with
          committed | discarded
        · exact False.elim (confirmed committed.2)
        · rw [discarded.1]
          rfl
      simp only [empty, List.getElem?_nil] at selected
      cases selected

end Netlib.Protocol.TCP.Checkpoint
