import Netlib.Protocol.TCP.AdmissionStartupRecovery

/-!
# Admission execution with an explicit mode

Ordinary execution reduces to the existing admission type and operations.
Recovery execution retains its own result and duplicate-control rules.
Common projections preserve actual observations, selected keys, and commit guards.
-/

namespace Netlib.Protocol.TCP.AdmissionExecution

open Admission

inductive Mode where
  | ordinary
  | startupRecovery
  deriving Repr, BEq, DecidableEq

abbrev Result (mode : Mode) (before : State) (input : Input) (lifecycle : ConntrackLifecycle.Input)
    (prepared : ConntrackLifecycle.Prepared lifecycle) : Type :=
  match mode with
  | .ordinary => Admission.Result before input lifecycle prepared
  | .startupRecovery => AdmissionStartupRecovery.Result before input lifecycle prepared

def Allowed (mode : Mode) (phase : Phase) (attachment : ConntrackLifecycle.Attachment) (segment : Segment)
    (observations : List Seen) : Prop :=
  match mode with
  | .ordinary => Admission.Allowed phase attachment segment observations
  | .startupRecovery => AdmissionStartupRecovery.Allowed phase attachment segment observations

instance (mode : Mode) (phase : Phase) (attachment : ConntrackLifecycle.Attachment) (segment : Segment)
    (observations : List Seen) : Decidable (Allowed mode phase attachment segment observations) := by
  cases mode <;> unfold Allowed <;> infer_instance

def nextPhase (mode : Mode) (phase : Phase) (attachment : ConntrackLifecycle.Attachment) (segment : Segment)
    (observations : List Seen) (allowed : Allowed mode phase attachment segment observations) : Phase :=
  match mode, allowed with
  | .ordinary, allowed => Admission.nextPhase phase attachment segment allowed
  | .startupRecovery, allowed => AdmissionStartupRecovery.nextPhase phase attachment segment observations allowed

def Result.state {mode : Mode} (value : Result mode before input lifecycle prepared) : State :=
  match mode, value with
  | .ordinary, value => Admission.Result.state value
  | .startupRecovery, value => AdmissionStartupRecovery.Result.state value

theorem Result.admitted (value : Result mode before input lifecycle prepared) :
    Allowed mode before.phase prepared.attachment input.packet.segment before.observations := by
  cases mode with
  | ordinary => exact Admission.Result.admitted value
  | startupRecovery => exact AdmissionStartupRecovery.Result.admitted value

theorem Result.phase (value : Result mode before input lifecycle prepared) :
    (Result.state value).phase = nextPhase mode before.phase prepared.attachment input.packet.segment
      before.observations (Result.admitted value) := by
  cases mode with
  | ordinary => exact Admission.Result.phase value
  | startupRecovery => exact AdmissionStartupRecovery.Result.phase value

theorem Result.ledger (value : Result mode before input lifecycle prepared) :
    (Result.state value).observations = before.observations ++ [observe input lifecycle prepared] := by
  cases mode with
  | ordinary => exact Admission.Result.ledger value
  | startupRecovery => exact AdmissionStartupRecovery.Result.ledger value

theorem Result.selectedKey (value : Result mode before input lifecycle prepared) :
    prepared.attachment.entry.flow.key prepared.attachment.direction = (lifecycle.zone, input.packet.header) := by
  cases mode with
  | ordinary => exact Admission.Result.selectedKey value
  | startupRecovery => exact AdmissionStartupRecovery.Result.selectedKey value

def step (mode : Mode) (before : State) (input : Input) (lifecycle : ConntrackLifecycle.Input)
    (prepared : ConntrackLifecycle.Prepared lifecycle) (same : lifecycle.packet = input.packet.header) :
    Except Error (Result mode before input lifecycle prepared) :=
  match mode with
  | .ordinary => Admission.step before input lifecycle prepared same
  | .startupRecovery => AdmissionStartupRecovery.step before input lifecycle prepared same

def commit {mode : Mode} (value : Result mode before input lifecycle prepared)
    (tracker : ConntrackLifecycle.State) : Except Error State :=
  match mode, value with
  | .ordinary, value => Admission.commit value tracker
  | .startupRecovery, value => AdmissionStartupRecovery.commit value tracker

theorem result_ordinary : Result .ordinary before input lifecycle prepared =
    Admission.Result before input lifecycle prepared := rfl

theorem step_ordinary (before : State) (input : Input) (lifecycle : ConntrackLifecycle.Input)
    (prepared : ConntrackLifecycle.Prepared lifecycle) (same : lifecycle.packet = input.packet.header) :
    step .ordinary before input lifecycle prepared same = Admission.step before input lifecycle prepared same := rfl

theorem commit_ordinary (value : Admission.Result before input lifecycle prepared) (tracker : ConntrackLifecycle.State) :
    commit (mode := .ordinary) value tracker = Admission.commit value tracker := rfl

theorem step_exists (mode : Mode) (before : State) (input : Input) (lifecycle : ConntrackLifecycle.Input)
    (prepared : ConntrackLifecycle.Prepared lifecycle) (same : lifecycle.packet = input.packet.header)
    (allowed : Allowed mode before.phase prepared.attachment input.packet.segment before.observations) :
    ∃ value, step mode before input lifecycle prepared same = .ok value := by
  cases mode with
  | ordinary => exact Admission.step_exists before input lifecycle prepared same allowed
  | startupRecovery => exact AdmissionStartupRecovery.step_exists before input lifecycle prepared same allowed

def Result.ofLegacy (mode : Mode) (value : Admission.Result before input lifecycle prepared) :
    Result mode before input lifecycle prepared :=
  match mode with
  | .ordinary => value
  | .startupRecovery => AdmissionStartupRecovery.Result.ofLegacy value

def Result.asLegacy (value : Result mode before input lifecycle prepared)
    (legacy : Admission.Allowed before.phase prepared.attachment input.packet.segment before.observations) :
    Admission.Result before input lifecycle prepared :=
  match mode, value with
  | .ordinary, value => value
  | .startupRecovery, value => AdmissionStartupRecovery.Result.asLegacy value legacy

theorem Result.ofLegacy_state (mode : Mode) (value : Admission.Result before input lifecycle prepared) :
    Result.state (Result.ofLegacy mode value) = value.state := by cases mode <;> rfl

theorem Result.asLegacy_state (value : Result mode before input lifecycle prepared)
    (legacy : Admission.Allowed before.phase prepared.attachment input.packet.segment before.observations) :
    (Result.asLegacy value legacy).state = Result.state value := by cases mode <;> rfl

theorem Result.legacy_commit (mode : Mode) (value : Admission.Result before input lifecycle prepared)
    (tracker : ConntrackLifecycle.State) :
    commit (Result.ofLegacy mode value) tracker = Admission.commit value tracker := by cases mode <;> rfl

theorem Result.asLegacy_commit (value : Result mode before input lifecycle prepared)
    (legacy : Admission.Allowed before.phase prepared.attachment input.packet.segment before.observations)
    (tracker : ConntrackLifecycle.State) :
    commit value tracker = Admission.commit (Result.asLegacy value legacy) tracker := by cases mode <;> rfl

theorem Result.legacy_or_stutter (value : Result mode before input lifecycle prepared) :
    Admission.Allowed before.phase prepared.attachment input.packet.segment before.observations ∨
      (mode = .startupRecovery ∧
        AdmissionStartupRecovery.StutterAllowed before.phase prepared.attachment input.packet.segment before.observations) := by
  cases mode with
  | ordinary => exact Or.inl (Admission.Result.admitted value)
  | startupRecovery =>
    rcases AdmissionStartupRecovery.Result.admitted value with legacy | stutter
    · exact Or.inl legacy
    · exact Or.inr ⟨rfl, stutter⟩

theorem Result.data_legacy (value : Result mode before input lifecycle prepared)
    (phase : before.phase = .data session) (profile : DataProfile input.packet.segment) :
    Admission.Allowed before.phase prepared.attachment input.packet.segment before.observations := by
  cases mode with
  | ordinary => exact Admission.Result.admitted value
  | startupRecovery => exact AdmissionStartupRecovery.Result.data_legacy value phase profile

def Result.dataLegacy (value : Result mode before input lifecycle prepared)
    (phase : before.phase = .data session) (profile : DataProfile input.packet.segment) :
    Admission.Result before input lifecycle prepared :=
  Result.asLegacy value (Result.data_legacy value phase profile)

theorem Result.dataLegacy_state (value : Result mode before input lifecycle prepared)
    (phase : before.phase = .data session) (profile : DataProfile input.packet.segment) :
    (Result.dataLegacy value phase profile).state = Result.state value :=
  Result.asLegacy_state value _

theorem Result.dataLegacy_commit (value : Result mode before input lifecycle prepared)
    (phase : before.phase = .data session) (profile : DataProfile input.packet.segment)
    (tracker : ConntrackLifecycle.State) :
    commit value tracker = Admission.commit (Result.dataLegacy value phase profile) tracker :=
  Result.asLegacy_commit value _ tracker

theorem Result.selected_entry (value : Result mode before input lifecycle prepared) :
    (Result.state value).phase.entry = some prepared.attachment.entry := by
  cases mode with
  | ordinary => exact Admission.Result.selected_entry value
  | startupRecovery => exact AdmissionStartupRecovery.Result.selected_entry value

theorem Result.fresh_phase (value : Result mode before input lifecycle prepared)
    (fresh : prepared.attachment.fresh = true) : before.phase = .empty := by
  cases mode with
  | ordinary => exact Admission.Result.fresh_phase value fresh
  | startupRecovery => exact AdmissionStartupRecovery.Result.fresh_phase value fresh

theorem Result.actual_bytes (value : Result mode before input lifecycle prepared) :
    (Result.state value).observations = before.observations ++ [observe input lifecycle prepared] ∧
      (observe input lifecycle prepared).bytes = input.bytes :=
  ⟨Result.ledger value, rfl⟩

theorem Result.observations_prefix (value : Result mode before input lifecycle prepared) :
    before.observations <+: (Result.state value).observations :=
  ⟨[observe input lifecycle prepared], (Result.ledger value).symm⟩

theorem Result.current_observation (value : Result mode before input lifecycle prepared) :
    (Result.state value).observations[before.observations.length]? = some (observe input lifecycle prepared) := by
  rw [Result.ledger value]
  simp

theorem Result.source_key (value : Result mode before input lifecycle prepared) :
    prepared.attachment.entry.flow.key prepared.attachment.direction = (lifecycle.zone, input.packet.header) :=
  Result.selectedKey value

theorem Result.checked_source (_value : Result mode before input lifecycle prepared) :
    decodeIPv4 input.bytes = .ok input.packet := input.checked

theorem commit_cases (value : Result mode before input lifecycle prepared) (tracker : ConntrackLifecycle.State)
    (after : State) (accepted : commit value tracker = .ok after) :
    (after = Result.state value ∧ confirmed prepared.attachment.entry tracker = true) ∨
      (after = State.initial ∧ prepared.attachment.fresh = true ∧ confirmed prepared.attachment.entry tracker = false) := by
  cases mode with
  | ordinary => exact Admission.commit_cases value tracker after accepted
  | startupRecovery => exact AdmissionStartupRecovery.commit_cases value tracker after accepted

theorem Result.confirmed_keeps (value : Result mode before input lifecycle prepared) (tracker : ConntrackLifecycle.State)
    (present : confirmed prepared.attachment.entry tracker = true) : commit value tracker = .ok (Result.state value) := by
  cases mode with
  | ordinary => exact Admission.Result.confirmed_keeps value tracker present
  | startupRecovery => exact AdmissionStartupRecovery.Result.confirmed_keeps value tracker present

theorem Result.fresh_unconfirmed (value : Result mode before input lifecycle prepared) (tracker : ConntrackLifecycle.State)
    (absent : confirmed prepared.attachment.entry tracker = false) (fresh : prepared.attachment.fresh = true) :
    commit value tracker = .ok State.initial := by
  cases mode with
  | ordinary => exact Admission.Result.fresh_unconfirmed value tracker absent fresh
  | startupRecovery => exact AdmissionStartupRecovery.Result.fresh_unconfirmed value tracker absent fresh

theorem Result.existing_missing (value : Result mode before input lifecycle prepared) (tracker : ConntrackLifecycle.State)
    (absent : confirmed prepared.attachment.entry tracker = false) (fresh : prepared.attachment.fresh = false) :
    commit value tracker = .error (.unsupported .historyLost) := by
  cases mode with
  | ordinary => exact Admission.Result.existing_missing value tracker absent fresh
  | startupRecovery => exact AdmissionStartupRecovery.Result.existing_missing value tracker absent fresh

theorem Result.existing_committed (value : Result mode before input lifecycle prepared) (tracker : ConntrackLifecycle.State)
    (fresh : prepared.attachment.fresh = false) (after : State) (accepted : commit value tracker = .ok after) :
    after = Result.state value ∧ (∃ record ∈ tracker.records, record.entry = prepared.attachment.entry) ∧
      after.observations = before.observations ++ [observe input lifecycle prepared] := by
  cases mode with
  | ordinary => exact Admission.Result.existing_committed value tracker fresh after accepted
  | startupRecovery => exact AdmissionStartupRecovery.Result.existing_committed value tracker fresh after accepted

export Netlib.Protocol.TCP.AdmissionExecution.Result (state admitted phase ledger selectedKey)

end Netlib.Protocol.TCP.AdmissionExecution
