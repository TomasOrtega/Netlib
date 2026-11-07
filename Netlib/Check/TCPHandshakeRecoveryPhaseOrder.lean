import Netlib.Check.TCPHandshakeRecovery

/-!
# Event order of current startup milestones

The last event bounds the latest milestone.
Retry occurrence indices do not replace the retained milestone times.
-/

namespace Netlib.Check.TCPHandshakeRecovery

def Phase.OrderedAt (phase : Phase active passive) (last : Nat) : Prop :=
  match phase with
  | .idle => True
  | .opened value => value.index ≤ last
  | .answered value => value.opened.index < value.index ∧ value.index ≤ last
  | .acknowledged value _ =>
      value.answered.opened.index < value.answered.index ∧
        value.answered.index < value.index ∧ value.index ≤ last
  | .complete value _ _ =>
      value.input.times.Valid ∧ value.input.times.ackReceived ≤ last

def PhaseOrder (state : State active passive) : Prop :=
  match state.last with
  | none => state.phase = .idle
  | some last => state.phase.OrderedAt last

variable {active passive : H.Local} {before after : State active passive}
variable {phase : Phase active passive} {first last : Nat}

theorem Phase.OrderedAt.mono (prior : phase.OrderedAt first) (order : first ≤ last) :
    phase.OrderedAt last := by
  cases phase with
  | idle => trivial
  | opened value => exact Nat.le_trans prior order
  | answered value => exact ⟨prior.1, Nat.le_trans prior.2 order⟩
  | acknowledged value client => exact ⟨prior.1, prior.2.1, Nat.le_trans prior.2.2 order⟩
  | complete value client server => exact ⟨prior.1, Nat.le_trans prior.2 order⟩

theorem PhaseOrder.initial : PhaseOrder (State.initial : State active passive) := rfl

theorem PhaseOrder.at (prior : PhaseOrder before) (last : before.last = some index) :
    before.phase.OrderedAt index := by
  simpa only [PhaseOrder, last] using prior

theorem PhaseOrder.frame (prior : PhaseOrder before)
    (phase : after.phase = before.phase) (last : after.last = before.last) : PhaseOrder after := by
  simpa only [PhaseOrder, phase, last] using prior

theorem PhaseOrder.restamp (prior : PhaseOrder before)
    (fresh : ∀ old, before.last = some old → old < index) :
    PhaseOrder { before with last := some index } := by
  change before.phase.OrderedAt index
  cases last : before.last with
  | none =>
    have phase : before.phase = .idle := by simpa only [PhaseOrder, last] using prior
    rw [phase]
    trivial
  | some old => exact Phase.OrderedAt.mono (prior.at last) (Nat.le_of_lt (fresh old last))

theorem PhaseOrder.withTimer (prior : PhaseOrder before) (actor : Side)
    (timer : T.State) (valid : timer.Valid) : PhaseOrder (before.withTimer actor timer valid) := by
  cases actor <;> exact prior

theorem PhaseOrder.publish (prior : PhaseOrder before) (output : Emission) :
    PhaseOrder (publish before output).state := prior

theorem PhaseOrder.retainReceipt (prior : PhaseOrder effect.state) (receipt : Receipt) :
    PhaseOrder (retainReceipt effect receipt).state := prior

theorem PhaseOrder.opened_before (prior : PhaseOrder before) (phase : before.phase = .opened value)
    (fresh : ∀ old, before.last = some old → old < index) : value.index < index := by
  cases last : before.last with
  | none =>
    have idle : before.phase = .idle := by simpa only [PhaseOrder, last] using prior
    rw [phase] at idle
    cases idle
  | some old =>
    have bound := prior.at last
    simp only [phase, Phase.OrderedAt] at bound
    exact Nat.lt_of_le_of_lt bound (fresh old last)

theorem PhaseOrder.answered_before (prior : PhaseOrder before) (phase : before.phase = .answered value)
    (fresh : ∀ old, before.last = some old → old < index) :
    value.opened.index < value.index ∧ value.index < index := by
  cases last : before.last with
  | none =>
    have idle : before.phase = .idle := by simpa only [PhaseOrder, last] using prior
    rw [phase] at idle
    cases idle
  | some old =>
    have bound := prior.at last
    simp only [phase, Phase.OrderedAt] at bound
    exact ⟨bound.1, Nat.lt_of_le_of_lt bound.2 (fresh old last)⟩

theorem PhaseOrder.acknowledged_before (prior : PhaseOrder before)
    (phase : before.phase = .acknowledged value client)
    (fresh : ∀ old, before.last = some old → old < index) :
    value.answered.opened.index < value.answered.index ∧
      value.answered.index < value.index ∧ value.index < index := by
  cases last : before.last with
  | none =>
    have idle : before.phase = .idle := by simpa only [PhaseOrder, last] using prior
    rw [phase] at idle
    cases idle
  | some old =>
    have bound := prior.at last
    simp only [phase, Phase.OrderedAt] at bound
    exact ⟨bound.1, bound.2.1, Nat.lt_of_le_of_lt bound.2.2 (fresh old last)⟩

theorem PhaseOrder.complete_before (prior : PhaseOrder before)
    (phase : before.phase = .complete value client server)
    (fresh : ∀ old, before.last = some old → old < index) :
    value.input.times.Valid ∧ value.input.times.ackReceived < index := by
  cases last : before.last with
  | none =>
    have idle : before.phase = .idle := by simpa only [PhaseOrder, last] using prior
    rw [phase] at idle
    cases idle
  | some old =>
    have bound := prior.at last
    simp only [phase, Phase.OrderedAt] at bound
    exact ⟨bound.1, Nat.lt_of_le_of_lt bound.2 (fresh old last)⟩

end Netlib.Check.TCPHandshakeRecovery
