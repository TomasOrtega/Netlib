import Netlib.Protocol.TCP.RecoveryReceipt

/-!
# Enabled recovery operations

The conditions refer to the stored clock, timer, and outstanding ranges.
They do not assume a successful operation result.
-/

namespace Netlib.Protocol.TCP.Recovery

def State.SentBy (state : State) (time : Nat) : Prop :=
  ∀ entry ∈ state.outstanding, entry.sentAt ≤ time

def State.Clocked (state : State) : Prop :=
  ∀ entry ∈ state.outstanding, entry.sentAt ≤ entry.lastAt ∧ entry.lastAt ≤ state.now

instance (state : State) (time : Nat) : Decidable (state.SentBy time) := by
  unfold State.SentBy
  infer_instance

instance (state : State) : Decidable state.Clocked := by
  unfold State.Clocked
  infer_instance

def State.Positive (state : State) : Prop := ∀ entry ∈ state.outstanding, 0 < entry.count

instance (state : State) : Decidable state.Positive := by
  unfold State.Positive
  infer_instance

theorem initial_positive (smss : Nat) : (initial smss).Positive := by simp [State.Positive, initial]

theorem sent_positive (state : State) (count : Nat) (prior : state.Positive) (positive : 0 < count) :
    (sent state count).Positive := by
  intro entry member
  simp only [sent, List.mem_append, List.mem_singleton] at member
  rcases member with old | current
  · exact prior entry old
  · cases current
    exact positive

theorem retire_positive (entries : List Outstanding) (count : Nat)
    (prior : ∀ entry ∈ entries, 0 < entry.count) : ∀ entry ∈ retire count entries, 0 < entry.count := by
  induction entries generalizing count with
  | nil => simp [retire]
  | cons head tail ih =>
    unfold retire
    split
    · exact prior
    · split
      · exact ih _ (fun entry member => prior entry (List.mem_cons_of_mem _ member))
      · intro entry member
        rcases List.mem_cons.mp member with same | inside
        · subst entry
          simp only
          omega
        · exact prior entry (List.mem_cons_of_mem _ inside)

theorem acknowledgeState_positive (state : State) (count : Nat) (prior : state.Positive) :
    (acknowledgeState state count).Positive := by
  unfold acknowledgeState
  split
  · exact prior
  · exact retire_positive state.outstanding count prior

theorem retire_all (entries : List Outstanding) (positive : ∀ entry ∈ entries, 0 < entry.count) :
    retire (entries.map (·.count)).sum entries = [] := by
  induction entries with
  | nil => rfl
  | cons head tail ih =>
    have first := positive head (by simp)
    have nonzero : head.count + (tail.map (·.count)).sum ≠ 0 := by omega
    have bounded : head.count ≤ head.count + (tail.map (·.count)).sum := Nat.le_add_right _ _
    simp only [List.map_cons, List.sum_cons, retire, nonzero, ite_false, bounded, ite_true, Nat.add_sub_cancel_left]
    exact ih (fun entry member => positive entry (by simp [member]))

theorem acknowledgeState_full (state : State) (positive : state.Positive) (nonempty : 0 < flight state) :
    (acknowledgeState state (flight state)).outstanding = [] ∧
      (acknowledgeState state (flight state)).deadline = none ∧
      (acknowledgeState state (flight state)).lastTimedOut = none ∧
      (acknowledgeState state (flight state)).timeoutCount = 0 := by
  have cleared : retire (flight state) state.outstanding = [] := retire_all state.outstanding positive
  have count : flight state ≠ 0 := Nat.ne_of_gt nonempty
  simp only [acknowledgeState, count, ite_false, cleared, List.isEmpty_nil, ite_true, and_self]

theorem State.Clocked.sentBy (state : State) (clocked : state.Clocked) : state.SentBy state.now := by
  intro entry member
  exact Nat.le_trans (clocked entry member).1 (clocked entry member).2

theorem advance_of_monotone (state : State) (time : Nat) (monotone : state.now ≤ time) :
    advance state time = .ok { state with now := time } := by
  simp only [advance, Nat.not_lt.mpr monotone, ite_false]

theorem acknowledge_of_bounded (state : State) (count : Nat) (bounded : count ≤ flight state) :
    acknowledge state count = .ok (acknowledgeState state count) := by
  simp only [acknowledge, Nat.not_lt.mpr bounded, ite_false]

theorem duplicate_of_bounded (state : State) (bounded : state.duplicateAcks + 1 < 3) :
    duplicate state = .ok { state with duplicateAcks := state.duplicateAcks + 1 } := by
  simp only [duplicate, Nat.not_le.mpr bounded, ite_false]

theorem timeout_of_due (state : State) (entry : Outstanding) (rest : List Outstanding) (deadline : Nat)
    (source : state.outstanding = entry :: rest) (timer : state.deadline = some deadline)
    (positive : 0 < entry.count) (due : deadline ≤ state.now) (elapsed : entry.lastAt + state.rto ≤ state.now)
    (remaining : state.lastTimedOut = some entry.id → state.timeoutCount < 2) :
    timeout state = .ok (entry.count, timeoutState state entry rest) := by
  simp only [timeout, source, timer, Nat.ne_of_gt positive, ite_false,
    Nat.not_lt.mpr due, Nat.not_lt.mpr elapsed, false_or]
  have allowed : ¬(state.lastTimedOut = some entry.id ∧ state.timeoutCount ≥ 2) := by
    intro exhausted
    have limit := remaining exhausted.1
    omega
  simp only [allowed, ite_false]

theorem touched_subset (count : Nat) (entries : List Outstanding) :
    ∀ entry ∈ touched count entries, entry ∈ entries := by
  induction entries generalizing count with
  | nil => simp [touched]
  | cons head tail ih =>
    unfold touched
    split
    · simp
    · intro entry member
      rcases List.mem_cons.mp member with same | member
      · exact List.mem_cons.mpr (.inl same)
      · split at member
        · exact List.mem_cons.mpr (.inr (ih _ entry member))
        · simp at member

theorem acknowledgeAt_of_bounded (state : State) (count receivedAt : Nat)
    (past : receivedAt ≤ state.now) (bounded : count ≤ flight state)
    (sent : ∀ entry ∈ touched count state.outstanding, entry.sentAt ≤ receivedAt) :
    acknowledgeAt state count receivedAt =
      .ok (acknowledgeAtState state (acknowledgeState { state with now := receivedAt } count) count) := by
  have validTimes : (touched count state.outstanding).any
      (fun entry => decide (receivedAt < entry.sentAt)) = false := by
    apply Bool.eq_false_iff.mpr
    intro invalid
    obtain ⟨entry, member, late⟩ := List.any_eq_true.mp invalid
    have before := sent entry member
    simp only [decide_eq_true_eq] at late
    omega
  have accepted := acknowledge_of_bounded { state with now := receivedAt } count
    (show count ≤ flight { state with now := receivedAt } from bounded)
  simp only [acknowledgeAt, Nat.not_lt.mpr past, ite_false, validTimes,
    Bool.false_eq_true, accepted, Except.map]

theorem acknowledgeAt_now_of_bounded (state : State) (count : Nat)
    (bounded : count ≤ flight state) (sent : state.SentBy state.now) :
    acknowledgeAt state count state.now =
      .ok (acknowledgeAtState state (acknowledgeState state count) count) := by
  simpa only using acknowledgeAt_of_bounded state count state.now (Nat.le_refl _) bounded
    (fun entry member => sent entry (touched_subset _ _ entry member))

theorem acknowledgeAtState_same_time (state : State) (count : Nat) :
    acknowledgeAtState state (acknowledgeState state count) count = acknowledgeState state count := by
  by_cases empty : count = 0
  · simp [acknowledgeAtState, acknowledgeState, empty]
  · simp only [acknowledgeAtState, acknowledgeState, empty, ite_false]

theorem acknowledgeAt_current_of_bounded (state : State) (count : Nat)
    (bounded : count ≤ flight state) (sent : state.SentBy state.now) :
    acknowledgeAt state count state.now = .ok (acknowledgeState state count) := by
  rw [acknowledgeAt_now_of_bounded state count bounded sent, acknowledgeAtState_same_time]

theorem acknowledgeState_now (state : State) (count : Nat) : (acknowledgeState state count).now = state.now := by
  unfold acknowledgeState
  split <;> rfl

theorem acknowledgeAt_current_success (state : State) (count : Nat) (valid : state.Valid)
    (bounded : count ≤ flight state) (sent : state.SentBy state.now) :
    ∃ after, acknowledgeAt state count state.now = .ok after ∧ after.Valid ∧
      after.smss = state.smss ∧ flight after = flight state - count ∧ after.now = state.now := by
  exact ⟨acknowledgeState state count, acknowledgeAt_current_of_bounded state count bounded sent,
    acknowledgeState_valid state count valid, acknowledgeState_smss state count,
    acknowledgeState_flight state count, acknowledgeState_now state count⟩

theorem acknowledge_full_success (state : State) (valid : state.Valid) (positive : state.Positive)
    (nonempty : 0 < flight state) :
    ∃ after, acknowledge state (flight state) = .ok after ∧ after.Valid ∧ after.smss = state.smss ∧
      flight after = 0 ∧ after.now = state.now ∧ after.outstanding = [] ∧ after.deadline = none ∧
      after.lastTimedOut = none ∧ after.timeoutCount = 0 := by
  have cleared := acknowledgeState_full state positive nonempty
  refine ⟨acknowledgeState state (flight state), acknowledge_of_bounded state _ (Nat.le_refl _),
    acknowledgeState_valid state _ valid, acknowledgeState_smss state _, ?_, acknowledgeState_now state _,
    cleared.1, cleared.2.1, cleared.2.2.1, cleared.2.2.2⟩
  rw [acknowledgeState_flight, Nat.sub_self]

theorem initial_clocked (smss : Nat) : (initial smss).Clocked := by
  simp [State.Clocked, initial]

theorem sent_clocked (state : State) (count : Nat) (prior : state.Clocked) : (sent state count).Clocked := by
  intro entry member
  simp only [sent, List.mem_append, List.mem_singleton] at member
  rcases member with old | current
  · exact prior entry old
  · subst entry
    exact ⟨Nat.le_refl _, Nat.le_refl _⟩

theorem advance_clocked (state : State) (time : Nat) (prior : state.Clocked) (monotone : state.now ≤ time) :
    ({ state with now := time } : State).Clocked := by
  intro entry member
  exact ⟨(prior entry member).1, Nat.le_trans (prior entry member).2 monotone⟩

private theorem retire_clocked (count : Nat) (entries : List Outstanding) (time : Nat)
    (prior : ∀ entry ∈ entries, entry.sentAt ≤ entry.lastAt ∧ entry.lastAt ≤ time) :
    ∀ entry ∈ retire count entries, entry.sentAt ≤ entry.lastAt ∧ entry.lastAt ≤ time := by
  induction entries generalizing count with
  | nil => simp [retire]
  | cons head tail ih =>
    unfold retire
    split
    · exact prior
    · split
      · exact ih _ (fun entry member => prior entry (List.mem_cons_of_mem _ member))
      · intro entry member
        rcases List.mem_cons.mp member with same | member
        · subst entry
          exact prior head (by simp)
        · exact prior entry (List.mem_cons_of_mem _ member)

theorem acknowledgeState_clocked (state : State) (count : Nat) (prior : state.Clocked) :
    (acknowledgeState state count).Clocked := by
  unfold acknowledgeState
  split
  · exact prior
  · exact retire_clocked _ _ _ prior

theorem acknowledgeAtState_clocked (state sampled : State) (count : Nat)
    (prior : sampled.Clocked) (past : sampled.now ≤ state.now) :
    (acknowledgeAtState state sampled count).Clocked := by
  intro entry member
  exact ⟨(prior entry member).1, Nat.le_trans (prior entry member).2 past⟩

theorem timeoutState_clocked (state : State) (entry : Outstanding) (rest : List Outstanding)
    (source : state.outstanding = entry :: rest) (prior : state.Clocked) :
    (timeoutState state entry rest).Clocked := by
  intro selected member
  rcases List.mem_cons.mp member with same | member
  · subst selected
    exact ⟨Nat.le_trans (prior entry (by simp [source])).1 (prior entry (by simp [source])).2, Nat.le_refl _⟩
  · exact prior selected (by simp [source, member])

theorem advance_positive (state : State) (time : Nat) (prior : state.Positive) :
    ({ state with now := time } : State).Positive := prior

theorem timeoutState_positive (state : State) (entry : Outstanding) (rest : List Outstanding)
    (source : state.outstanding = entry :: rest) (prior : state.Positive) :
    (timeoutState state entry rest).Positive := by
  intro selected member
  rcases List.mem_cons.mp member with same | inside
  · subst selected
    exact prior entry (by simp [source])
  · exact prior selected (by simp [source, inside])

theorem acknowledgeAt_positive (state : State) (count receivedAt : Nat) (after : State)
    (prior : state.Positive) (accepted : acknowledgeAt state count receivedAt = .ok after) : after.Positive := by
  obtain ⟨_, sampled, computed, changed⟩ := acknowledgeAt_fields state count receivedAt after accepted
  have sampledPositive := acknowledgeState_positive { state with now := receivedAt } count prior
  rw [(acknowledge_fields { state with now := receivedAt } count sampled computed).2] at *
  rw [changed]
  exact sampledPositive

theorem acknowledgeAt_clocked (state : State) (count receivedAt : Nat) (after : State)
    (prior : state.Clocked) (accepted : acknowledgeAt state count receivedAt = .ok after) : after.Clocked := by
  obtain ⟨_, sampled, computed, changed⟩ := acknowledgeAt_fields state count receivedAt after accepted
  have remaining : ∀ entry ∈ sampled.outstanding, entry.sentAt ≤ entry.lastAt ∧ entry.lastAt ≤ state.now := by
    rw [(acknowledge_fields { state with now := receivedAt } count sampled computed).2]
    unfold acknowledgeState
    split
    · exact prior
    · exact retire_clocked count state.outstanding state.now prior
  rw [changed]
  exact remaining

end Netlib.Protocol.TCP.Recovery
