import Netlib.Protocol.TCP.Recovery

/-!
# Upper bound on an armed recovery deadline

The bound follows from the actual timer transformations.
It does not bound the RTO or assume future delivery.
-/

namespace Netlib.Protocol.TCP.RecoveryDeadline

def Bound (state : Recovery.State) : Prop :=
  ∀ deadline, state.deadline = some deadline → deadline ≤ state.now + state.rto

theorem of_none (state : Recovery.State) (none : state.deadline = none) : Bound state := by
  intro deadline present
  rw [none] at present
  cases present

theorem sent (state : Recovery.State) (count : Nat) (prior : Bound state) : Bound (Recovery.sent state count) := by
  intro deadline present
  cases timer : state.deadline with
  | none =>
    have same : state.now + state.rto = deadline := by simpa only [Recovery.sent, timer, Option.some.injEq] using present
    exact same ▸ Nat.le_refl _
  | some stored =>
    have same : stored = deadline := by simpa only [Recovery.sent, timer, Option.some.injEq] using present
    exact same ▸ prior stored timer

theorem acknowledge (state : Recovery.State) (count : Nat) (prior : Bound state) : Bound (Recovery.acknowledgeState state count) := by
  by_cases zero : count = 0
  · simpa only [Recovery.acknowledgeState, zero, ite_true] using prior
  · intro deadline present
    simp only [Recovery.acknowledgeState, zero, ite_false] at present ⊢
    split at present
    · cases present
    · exact (Option.some.inj present) ▸ Nat.le_refl _

theorem positive_ack (state : Recovery.State) (count : Nat) (positive : 0 < count) : Bound (Recovery.acknowledgeState state count) := by
  intro deadline present
  simp only [Recovery.acknowledgeState, Nat.ne_of_gt positive, ite_false] at present ⊢
  split at present
  · cases present
  · exact (Option.some.inj present) ▸ Nat.le_refl _

theorem timeout (state : Recovery.State) (head : Recovery.Outstanding) (rest : List Recovery.Outstanding) :
    Bound (Recovery.timeoutState state head rest) := by
  intro deadline present
  exact (Option.some.inj present) ▸ Nat.le_refl _

theorem advance (state : Recovery.State) (millis : Nat) (prior : Bound state) (monotone : state.now ≤ millis) :
    Bound { state with now := millis } := by
  intro deadline present
  exact Nat.le_trans (prior deadline present) (Nat.add_le_add_right monotone state.rto)

end Netlib.Protocol.TCP.RecoveryDeadline
