import Netlib.Protocol.TCP.Admission

/-!
# Gateway admission for retained startup controls

Legacy admission keeps priority, including data ACK window updates.
An exact duplicate control cites a preceding observation as its template.
Its current input remains a separate appended observation.
Bare startup reply ACKs preserve the phase without learning missing server fields.
-/

namespace Netlib.Protocol.TCP.AdmissionStartupRecovery

open Admission

namespace A
export Admission (Allowed Result step nextPhase commit)
end A

def KnownControl (observations : List Seen) (entry : Entry) (direction : Direction) (segment : Segment) : Prop :=
  ∃ seen ∈ observations, seen.attachment.entry = entry ∧ seen.attachment.direction = direction ∧
    seen.zone = entry.flow.zone direction ∧ seen.header = entry.flow.input direction ∧ seen.segment = segment

instance (observations : List Seen) (entry : Entry) (direction : Direction) (segment : Segment) :
    Decidable (KnownControl observations entry direction segment) := by
  unfold KnownControl
  infer_instance

private instance (options : List UInt8) (offer : MSS.Offer) :
    Decidable (MSS.readStartup options = .ok offer) := by
  cases computed : MSS.readStartup options with
  | error reason => exact .isFalse (by intro impossible; cases impossible)
  | ok selected => exact decidable_of_iff (selected = offer) (by simp only [Except.ok.injEq])

theorem KnownControl.of_observe (input : Input) (lifecycle : ConntrackLifecycle.Input)
    (prepared : ConntrackLifecycle.Prepared lifecycle) (same : lifecycle.packet = input.packet.header)
    (member : observe input lifecycle prepared ∈ observations) :
    KnownControl observations prepared.attachment.entry prepared.attachment.direction input.packet.segment := by
  have key : prepared.attachment.entry.flow.key prepared.attachment.direction = (lifecycle.zone, input.packet.header) := by
    simpa only [same] using prepared.attached
  exact ⟨observe input lifecycle prepared, member, rfl, rfl,
    (congrArg Prod.fst key).symm, (congrArg Prod.snd key).symm, rfl⟩

theorem KnownControl.append (known : KnownControl observations entry direction segment) (extra : List Seen) :
    KnownControl (observations ++ extra) entry direction segment := by
  obtain ⟨seen, member, facts⟩ := known
  exact ⟨seen, List.mem_append_left _ member, facts⟩

def ExactSyn (observations : List Seen) (entry : Entry) (clientISS : Seq) (clientMSS : MSS.Offer)
    (segment : Segment) : Prop :=
  Startup segment 2 ∧ segment.sequence = clientISS ∧ MSS.readStartup segment.options = .ok clientMSS ∧
    KnownControl observations entry .original segment

def ExactSynAck (observations : List Seen) (entry : Entry) (clientISS serverISS : Seq) (serverMSS : MSS.Offer)
    (segment : Segment) : Prop :=
  Startup segment 18 ∧ segment.sequence = serverISS ∧ segment.acknowledgment = clientISS.add 1 ∧
    MSS.readStartup segment.options = .ok serverMSS ∧ KnownControl observations entry .reply segment

def BareReply (clientISS : Seq) (segment : Segment) : Prop :=
  Startup segment 16 ∧ segment.acknowledgment = clientISS.add 1

def StutterAllowed (phase : Phase) (attachment : ConntrackLifecycle.Attachment) (segment : Segment)
    (observations : List Seen) : Prop :=
  match phase with
  | .empty => False
  | .syn entry clientISS clientWindow clientMSS =>
    attachment.entry = entry ∧ attachment.fresh = false ∧
      ((attachment.direction = .original ∧ ExactSyn observations entry clientISS clientMSS segment ∧
          segment.window = clientWindow) ∨
        (attachment.direction = .reply ∧ BareReply clientISS segment))
  | .synAck entry clientISS clientWindow serverISS serverWindow clientMSS serverMSS =>
    attachment.entry = entry ∧ attachment.fresh = false ∧
      ((attachment.direction = .original ∧ ExactSyn observations entry clientISS clientMSS segment ∧
          segment.window = clientWindow) ∨
        (attachment.direction = .reply ∧
          ((ExactSynAck observations entry clientISS serverISS serverMSS segment ∧ segment.window = serverWindow) ∨
            (BareReply clientISS segment ∧ segment.sequence = serverISS.add 1 ∧ segment.window = serverWindow))))
  | .data session =>
    attachment.entry = session.entry ∧ attachment.fresh = false ∧
      ((attachment.direction = .original ∧
          ExactSyn observations session.entry session.original.controlOrigin session.clientMSS segment) ∨
        (attachment.direction = .reply ∧
          ExactSynAck observations session.entry session.original.controlOrigin session.reply.controlOrigin
            session.serverMSS segment))

instance (phase : Phase) (attachment : ConntrackLifecycle.Attachment) (segment : Segment) (observations : List Seen) :
    Decidable (StutterAllowed phase attachment segment observations) := by
  unfold StutterAllowed ExactSyn ExactSynAck BareReply
  cases phase <;> infer_instance

def Allowed (phase : Phase) (attachment : ConntrackLifecycle.Attachment) (segment : Segment)
    (observations : List Seen) : Prop :=
  A.Allowed phase attachment segment observations ∨ StutterAllowed phase attachment segment observations

instance (phase : Phase) (attachment : ConntrackLifecycle.Attachment) (segment : Segment) (observations : List Seen) :
    Decidable (Allowed phase attachment segment observations) := by
  unfold Allowed
  infer_instance

def nextPhase (phase : Phase) (attachment : ConntrackLifecycle.Attachment) (segment : Segment)
    (observations : List Seen) (_allowed : Allowed phase attachment segment observations) : Phase :=
  if legacy : A.Allowed phase attachment segment observations then A.nextPhase phase attachment segment legacy else phase

theorem nextPhase_legacy (legacy : A.Allowed phase attachment segment observations)
    (allowed : Allowed phase attachment segment observations) :
    nextPhase phase attachment segment observations allowed = A.nextPhase phase attachment segment legacy := by
  simp only [nextPhase, legacy, dite_true]

theorem StutterAllowed.existing (allowed : StutterAllowed phase attachment segment observations) :
    attachment.fresh = false := by
  cases phase <;> first | exact False.elim allowed | exact allowed.2.1

theorem StutterAllowed.entry (allowed : StutterAllowed phase attachment segment observations) :
    phase.entry = some attachment.entry := by
  cases phase <;> first | exact False.elim allowed | exact congrArg some allowed.1.symm

private theorem startup_not_data (profile : Startup segment flags) (notAck : flags ≠ 16) (notPush : flags ≠ 24) :
    ¬DataProfile segment := by
  rintro ⟨ack | push, _⟩
  · exact notAck (profile.1.symm.trans ack)
  · exact notPush (profile.1.symm.trans push)

theorem StutterAllowed.not_legacy (allowed : StutterAllowed phase attachment segment observations) :
    ¬A.Allowed phase attachment segment observations := by
  intro legacy
  cases phase with
  | empty => exact False.elim allowed
  | syn entry clientISS clientWindow clientMSS =>
    rcases allowed.2.2 with ⟨direction, control, _⟩ | ⟨direction, reply⟩
    · have impossible := direction.symm.trans legacy.2.2.1
      cases impossible
    · exact (by decide : (16 : UInt8) ≠ 18) (reply.1.1.symm.trans legacy.2.2.2.1.1)
  | synAck entry clientISS clientWindow serverISS serverWindow clientMSS serverMSS =>
    rcases allowed.2.2 with ⟨direction, control, _⟩ | ⟨direction, reply⟩
    · exact (by decide : (2 : UInt8) ≠ 16) (control.1.1.symm.trans legacy.2.2.2.1.1)
    · have impossible := direction.symm.trans legacy.2.2.1
      cases impossible
  | data session =>
    rcases allowed.2.2 with ⟨direction, control⟩ | ⟨direction, control⟩
    · have outside := startup_not_data control.1 (by decide) (by decide)
      have selected := legacy.2.2
      rw [direction] at selected
      exact selected.elim (fun fresh => outside fresh.1) (fun repeated => outside repeated.1)
    · have outside := startup_not_data control.1 (by decide) (by decide)
      have selected := legacy.2.2
      rw [direction] at selected
      exact selected.elim (fun fresh => outside fresh.1) (fun repeated => outside repeated.1)

theorem nextPhase_stutter (stutter : StutterAllowed phase attachment segment observations)
    (allowed : Allowed phase attachment segment observations) :
    nextPhase phase attachment segment observations allowed = phase := by
  simp only [nextPhase, stutter.not_legacy, dite_false]

theorem StutterAllowed.source_or_bare (allowed : StutterAllowed phase attachment segment observations) :
    KnownControl observations attachment.entry attachment.direction segment ∨ Startup segment 16 := by
  cases phase with
  | empty => exact False.elim allowed
  | syn entry clientISS clientWindow clientMSS =>
    rcases allowed.2.2 with ⟨direction, control, _⟩ | ⟨_, reply⟩
    · exact Or.inl (by rw [allowed.1, direction]; exact control.2.2.2)
    · exact Or.inr reply.1
  | synAck entry clientISS clientWindow serverISS serverWindow clientMSS serverMSS =>
    rcases allowed.2.2 with ⟨direction, control, _⟩ | ⟨direction, reply⟩
    · exact Or.inl (by rw [allowed.1, direction]; exact control.2.2.2)
    · rcases reply with ⟨control, _⟩ | ⟨bare, _, _⟩
      · exact Or.inl (by rw [allowed.1, direction]; exact control.2.2.2.2)
      · exact Or.inr bare.1
  | data session =>
    rcases allowed.2.2 with ⟨direction, control⟩ | ⟨direction, control⟩
    · exact Or.inl (by rw [allowed.1, direction]; exact control.2.2.2)
    · exact Or.inl (by rw [allowed.1, direction]; exact control.2.2.2.2)

theorem StutterAllowed.control_template (allowed : StutterAllowed phase attachment segment observations)
    (control : segment.flags = 2 ∨ segment.flags = 18) :
    KnownControl observations attachment.entry attachment.direction segment := by
  rcases allowed.source_or_bare with known | bare
  · exact known
  · rcases control with syn | synAck
    · exact False.elim ((by decide : (2 : UInt8) ≠ 16) (syn.symm.trans bare.1))
    · exact False.elim ((by decide : (18 : UInt8) ≠ 16) (synAck.symm.trans bare.1))

theorem StutterAllowed.data_not_profile (allowed : StutterAllowed (.data session) attachment segment observations) :
    ¬DataProfile segment := by
  rcases allowed.2.2 with ⟨_, control⟩ | ⟨_, control⟩
  · exact startup_not_data control.1 (by decide) (by decide)
  · exact startup_not_data control.1 (by decide) (by decide)

theorem Allowed.bare_syn (entryEq : attachment.entry = entry) (existing : attachment.fresh = false)
    (direction : attachment.direction = .reply) (profile : Startup segment 16)
    (acknowledgment : segment.acknowledgment = clientISS.add 1) :
    Allowed (.syn entry clientISS clientWindow clientMSS) attachment segment observations :=
  Or.inr ⟨entryEq, existing, Or.inr ⟨direction, profile, acknowledgment⟩⟩

theorem Allowed.bare_synAck (entryEq : attachment.entry = entry) (existing : attachment.fresh = false)
    (direction : attachment.direction = .reply) (profile : Startup segment 16)
    (acknowledgment : segment.acknowledgment = clientISS.add 1)
    (sequence : segment.sequence = serverISS.add 1) (window : segment.window = serverWindow) :
    Allowed (.synAck entry clientISS clientWindow serverISS serverWindow clientMSS serverMSS)
      attachment segment observations :=
  Or.inr ⟨entryEq, existing, Or.inr ⟨direction, Or.inr ⟨⟨profile, acknowledgment⟩, sequence, window⟩⟩⟩

structure Result (before : State) (input : Input) (lifecycle : ConntrackLifecycle.Input)
    (prepared : ConntrackLifecycle.Prepared lifecycle) where
  state : State
  admitted : Allowed before.phase prepared.attachment input.packet.segment before.observations
  phase : state.phase = nextPhase before.phase prepared.attachment input.packet.segment before.observations admitted
  ledger : state.observations = before.observations ++ [observe input lifecycle prepared]
  selectedKey : prepared.attachment.entry.flow.key prepared.attachment.direction = (lifecycle.zone, input.packet.header)

def step (before : State) (input : Input) (lifecycle : ConntrackLifecycle.Input)
    (prepared : ConntrackLifecycle.Prepared lifecycle) (same : lifecycle.packet = input.packet.header) :
    Except Error (Result before input lifecycle prepared) :=
  if allowed : Allowed before.phase prepared.attachment input.packet.segment before.observations then
    .ok ⟨⟨nextPhase before.phase prepared.attachment input.packet.segment before.observations allowed,
        before.observations ++ [observe input lifecycle prepared]⟩, allowed, rfl, rfl,
      by simpa only [same] using prepared.attached⟩
  else .error (.unsupported (reason before.phase prepared.attachment input.packet.segment before.observations))

theorem step_exists (before : State) (input : Input) (lifecycle : ConntrackLifecycle.Input)
    (prepared : ConntrackLifecycle.Prepared lifecycle) (same : lifecycle.packet = input.packet.header)
    (allowed : Allowed before.phase prepared.attachment input.packet.segment before.observations) :
    ∃ result, step before input lifecycle prepared same = .ok result := by
  simp only [step, allowed, dite_true]
  exact ⟨_, rfl⟩

def Result.ofLegacy (value : A.Result before input lifecycle prepared) : Result before input lifecycle prepared where
  state := value.state
  admitted := Or.inl value.admitted
  phase := value.phase.trans (nextPhase_legacy value.admitted _).symm
  ledger := value.ledger
  selectedKey := value.selectedKey

def Result.asLegacy (value : Result before input lifecycle prepared)
    (legacy : A.Allowed before.phase prepared.attachment input.packet.segment before.observations) :
    A.Result before input lifecycle prepared where
  state := value.state
  admitted := legacy
  phase := value.phase.trans (nextPhase_legacy legacy _)
  ledger := value.ledger
  selectedKey := value.selectedKey

theorem Result.data_legacy (value : Result before input lifecycle prepared)
    (phase : before.phase = .data session) (profile : DataProfile input.packet.segment) :
    A.Allowed before.phase prepared.attachment input.packet.segment before.observations := by
  rcases value.admitted with legacy | extra
  · exact legacy
  · rw [phase] at extra
    exact False.elim (extra.data_not_profile profile)

theorem Result.eq_of_state (left right : Result before input lifecycle prepared) (same : left.state = right.state) :
    left = right := by
  cases left
  cases right
  cases same
  rfl

theorem step_eq (value : Result before input lifecycle prepared) (same : lifecycle.packet = input.packet.header) :
    step before input lifecycle prepared same = .ok value := by
  simp only [step, value.admitted, dite_true]
  apply congrArg Except.ok
  apply Result.eq_of_state
  cases value with
  | mk state admitted phase ledger key =>
    cases state
    simp only at phase ledger
    cases phase
    cases ledger
    rfl

theorem step_legacy (value : A.Result before input lifecycle prepared) (same : lifecycle.packet = input.packet.header) :
    step before input lifecycle prepared same = .ok (Result.ofLegacy value) :=
  step_eq _ same

theorem step_eq_legacy (before : State) (input : Input) (lifecycle : ConntrackLifecycle.Input)
    (prepared : ConntrackLifecycle.Prepared lifecycle) (same : lifecycle.packet = input.packet.header)
    (noExtension : ¬StutterAllowed before.phase prepared.attachment input.packet.segment before.observations) :
    (step before input lifecycle prepared same).map Result.state =
      (A.step before input lifecycle prepared same).map (fun value => value.state) := by
  by_cases legacy : A.Allowed before.phase prepared.attachment input.packet.segment before.observations
  · obtain ⟨value, computed⟩ := Admission.step_exists before input lifecycle prepared same legacy
    rw [step_legacy value same, computed]
    rfl
  · have blocked : ¬Allowed before.phase prepared.attachment input.packet.segment before.observations := by
      intro admitted
      exact admitted.elim legacy noExtension
    simp only [step, blocked, dite_false, Admission.step, legacy, Except.map]

theorem Result.stutter (result : Result before input lifecycle prepared)
    (stutter : StutterAllowed before.phase prepared.attachment input.packet.segment before.observations) :
    result.state.phase = before.phase :=
  result.phase.trans (nextPhase_stutter stutter _)

theorem Result.selected_entry (result : Result before input lifecycle prepared) :
    result.state.phase.entry = some prepared.attachment.entry := by
  by_cases legacy : A.Allowed before.phase prepared.attachment input.packet.segment before.observations
  · exact (result.asLegacy legacy).selected_entry
  · have stutter := result.admitted.resolve_left legacy
    rw [result.stutter stutter]
    exact stutter.entry

theorem Result.fresh_phase (result : Result before input lifecycle prepared)
    (fresh : prepared.attachment.fresh = true) : before.phase = .empty := by
  rcases result.admitted with legacy | stutter
  · exact (result.asLegacy legacy).fresh_phase fresh
  · have impossible := stutter.existing
    rw [fresh] at impossible
    cases impossible

def commit (result : Result before input lifecycle prepared) (tracker : ConntrackLifecycle.State) : Except Error State :=
  if confirmed prepared.attachment.entry tracker then .ok result.state
  else if prepared.attachment.fresh then .ok State.initial
  else .error (.unsupported .historyLost)

theorem Result.legacy_commit (value : A.Result before input lifecycle prepared) (tracker : ConntrackLifecycle.State) :
    commit (Result.ofLegacy value) tracker = A.commit value tracker := rfl

theorem Result.asLegacy_commit (value : Result before input lifecycle prepared)
    (legacy : A.Allowed before.phase prepared.attachment input.packet.segment before.observations)
    (tracker : ConntrackLifecycle.State) : commit value tracker = A.commit (value.asLegacy legacy) tracker := rfl

theorem Result.confirmed_keeps (result : Result before input lifecycle prepared) (tracker : ConntrackLifecycle.State)
    (present : confirmed prepared.attachment.entry tracker = true) : commit result tracker = .ok result.state := by
  simp only [commit, present, ite_true]

theorem Result.fresh_unconfirmed (result : Result before input lifecycle prepared) (tracker : ConntrackLifecycle.State)
    (absent : confirmed prepared.attachment.entry tracker = false) (fresh : prepared.attachment.fresh = true) :
    commit result tracker = .ok State.initial := by
  simp only [commit, absent, Bool.false_eq_true, ite_false, fresh, ite_true]

theorem Result.existing_missing (result : Result before input lifecycle prepared) (tracker : ConntrackLifecycle.State)
    (absent : confirmed prepared.attachment.entry tracker = false) (fresh : prepared.attachment.fresh = false) :
    commit result tracker = .error (.unsupported .historyLost) := by
  simp only [commit, absent, fresh, Bool.false_eq_true, ite_false]

theorem commit_cases (result : Result before input lifecycle prepared) (tracker : ConntrackLifecycle.State)
    (after : State) (accepted : commit result tracker = .ok after) :
    (after = result.state ∧ confirmed prepared.attachment.entry tracker = true) ∨
      (after = State.initial ∧ prepared.attachment.fresh = true ∧ confirmed prepared.attachment.entry tracker = false) := by
  unfold commit at accepted
  split at accepted
  · rename_i present
    cases accepted
    exact Or.inl ⟨rfl, present⟩
  · rename_i absent
    have missing : confirmed prepared.attachment.entry tracker = false := by
      cases selected : confirmed prepared.attachment.entry tracker <;> simp_all
    split at accepted
    · rename_i fresh
      cases accepted
      exact Or.inr ⟨rfl, fresh, missing⟩
    · cases accepted

theorem Result.existing_committed (result : Result before input lifecycle prepared) (tracker : ConntrackLifecycle.State)
    (fresh : prepared.attachment.fresh = false) (after : State) (accepted : commit result tracker = .ok after) :
    after = result.state ∧ (∃ record ∈ tracker.records, record.entry = prepared.attachment.entry) ∧
      after.observations = before.observations ++ [observe input lifecycle prepared] := by
  rcases commit_cases result tracker after accepted with ⟨same, present⟩ | ⟨_, newer, _⟩
  · exact ⟨same, (confirmed_correct _ _).mp present, same ▸ result.ledger⟩
  · simp only [fresh, Bool.false_eq_true] at newer

theorem Result.actual_bytes (result : Result before input lifecycle prepared) :
    result.state.observations = before.observations ++ [observe input lifecycle prepared] ∧
      (observe input lifecycle prepared).bytes = input.bytes :=
  ⟨result.ledger, rfl⟩

theorem Result.observations_prefix (result : Result before input lifecycle prepared) :
    before.observations <+: result.state.observations :=
  ⟨[observe input lifecycle prepared], result.ledger.symm⟩

theorem Result.current_observation (result : Result before input lifecycle prepared) :
    result.state.observations[before.observations.length]? = some (observe input lifecycle prepared) := by
  rw [result.ledger]
  simp

theorem Result.source_key (result : Result before input lifecycle prepared) :
    prepared.attachment.entry.flow.key prepared.attachment.direction = (lifecycle.zone, input.packet.header) := result.selectedKey

theorem Result.checked_source (_result : Result before input lifecycle prepared) :
    decodeIPv4 input.bytes = .ok input.packet := input.checked

end Netlib.Protocol.TCP.AdmissionStartupRecovery
