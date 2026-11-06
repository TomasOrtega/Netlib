import Netlib.Protocol.TCP.AckReaction

/-!
# ACK actions from preceding state conditions

Pending causes retain their proposed right edge until output.
Time, coverage, and response credit are checked before the action.
-/

namespace Netlib.Theory.TimedReaction

theorem checkTime_of_fields (state : State Domain Demand Output) (now : Nat)
    (timely : ∀ cause ∈ state.pending, cause.issuedAt ≤ now ∧ now ≤ cause.due) :
    checkTime state now = .ok () := by
  have early : state.pending.any (fun cause => decide (now < cause.issuedAt)) = false := by
    apply List.any_eq_false.mpr
    intro cause member
    simp only [decide_eq_true_eq]
    have bound := (timely cause member).1
    omega
  have late : state.pending.any (fun cause => decide (cause.due < now)) = false := by
    apply List.any_eq_false.mpr
    intro cause member
    simp only [decide_eq_true_eq]
    have bound := (timely cause member).2
    omega
  simp only [checkTime, early, late, Bool.false_eq_true, ite_false]

theorem checkTime_iff_fields (state : State Domain Demand Output) (now : Nat) :
    checkTime state now = .ok () ↔
      ∀ cause ∈ state.pending, cause.issuedAt ≤ now ∧ now ≤ cause.due :=
  ⟨checkTime_fields state now, checkTime_of_fields state now⟩

theorem issue_time_fields (state : State Domain Demand Output) (now : Nat) (demand : Demand) (delay : Nat)
    (timely : ∀ cause ∈ state.pending, cause.issuedAt ≤ now ∧ now ≤ cause.due) :
    ∀ cause ∈ (issue state now demand delay).pending, cause.issuedAt ≤ now ∧ now ≤ cause.due := by
  intro cause member
  rw [issue_pending] at member
  rcases List.mem_append.mp member with old | current
  · exact timely cause old
  · have same := List.mem_singleton.mp current
    subst cause
    exact ⟨Nat.le_refl _, Nat.le_add_right _ _⟩

end Netlib.Theory.TimedReaction

namespace Netlib.Protocol.TCP.ReceiveAdvertisement

theorem candidate_mono_free (state : State) (capacity before after outgoingMSS : Nat)
    (room : state.window ≤ before) (growth : before ≤ after) :
    candidate state capacity before outgoingMSS ≤ candidate state capacity after outgoingMSS := by
  unfold candidate
  split <;> split <;> omega

theorem candidate_consume (state : State) (capacity free outgoingMSS count : Nat)
    (valid : state.Valid free) (fits : count ≤ state.window) :
    candidate (consume state count) capacity (free - count) outgoingMSS =
      candidate state capacity free outgoingMSS - count := by
  have room := valid.2
  have gap : free - count - (state.window - count) = free - state.window := by omega
  simp only [candidate, consume_window, gap]
  split <;> rfl

theorem candidate_edge_consume (state : State) (capacity free outgoingMSS count : Nat)
    (valid : state.Valid free) (fits : count ≤ state.window) :
    (consume state count).frontier + candidate (consume state count) capacity (free - count) outgoingMSS =
      state.frontier + candidate state capacity free outgoingMSS := by
  rw [candidate_consume state capacity free outgoingMSS count valid fits]
  have room := (candidate_bounds state capacity free outgoingMSS valid).1
  change state.frontier + count + (candidate state capacity free outgoingMSS - count) = _
  omega

end Netlib.Protocol.TCP.ReceiveAdvertisement

namespace Netlib.Protocol.TCP.AckReaction

def State.WithinTime (state : State) (now : Nat) : Prop :=
  ∀ cause ∈ state.work.pending, cause.issuedAt ≤ now ∧ now ≤ cause.due

def State.Covered (state : State) (capacity free outgoingMSS : Nat) : Prop :=
  ∀ cause ∈ state.work.pending,
    cause.demand.position ≤ state.advertisement.frontier ∧
      cause.demand.minimumEdge ≤ state.advertisement.frontier + candidate state capacity free outgoingMSS

instance (state : State) (now : Nat) : Decidable (state.WithinTime now) := by
  unfold State.WithinTime
  infer_instance

instance (state : State) (capacity free outgoingMSS : Nat) : Decidable (state.Covered capacity free outgoingMSS) := by
  unfold State.Covered
  infer_instance

theorem checkTime_of_within (state : State) (now : Nat) (timely : state.WithinTime now) :
    checkTime state now = .ok () := by
  rw [checkTime, Netlib.Theory.TimedReaction.checkTime_of_fields state.work now timely]
  rfl

theorem initial_covered (cursor : Seq) (capacity rmss outgoingMSS : Nat) :
    (initial cursor capacity rmss).Covered capacity capacity outgoingMSS := by
  simp [State.Covered, initial, T.initial, Netlib.Theory.TimedReaction.initial]

theorem initial_within (cursor : Seq) (capacity rmss now : Nat) :
    (initial cursor capacity rmss).WithinTime now := by
  simp [State.WithinTime, initial, T.initial, Netlib.Theory.TimedReaction.initial]

theorem outputReady_of_covered (state : State) (now : Nat) (cursor : Seq) (capacity free outgoingMSS : Nat)
    (timely : state.WithinTime now) (covered : state.Covered capacity free outgoingMSS) :
    outputReady state now cursor capacity free outgoingMSS = .ok () := by
  have all : state.work.pending.all (fun cause => covers cause.demand (acknowledgment state cursor capacity free outgoingMSS)) = true := by
    apply List.all_eq_true.mpr
    intro cause member
    exact decide_eq_true (covered cause member)
  simp only [outputReady, checkTime_of_within state now timely, all, bind, Except.bind,
    pure, Except.pure, ite_true]

theorem responseReady_of_credit (state : State) (now : Nat) (dueOnly : Bool)
    (timely : state.WithinTime now) (credit : state.work.pending ≠ [])
    (due : dueOnly = true → ∃ deadline, state.due = some deadline ∧ deadline ≤ now) :
    responseReady state now dueOnly = .ok () := by
  have pending : state.work.pending.isEmpty = false := List.isEmpty_eq_false_iff.mpr credit
  simp only [responseReady, checkTime_of_within state now timely, pending, Bool.false_eq_true,
    bind, Except.bind, ite_false]
  cases dueOnly with
  | false => rfl
  | true =>
    obtain ⟨deadline, selected, ready⟩ := due rfl
    simp only [ite_true, selected, Nat.not_lt.mpr ready, ite_false]
    rfl

theorem Covered.more_free (state : State) (capacity before after outgoingMSS : Nat)
    (covered : state.Covered capacity before outgoingMSS) (valid : state.advertisement.Valid before)
    (growth : before ≤ after) : state.Covered capacity after outgoingMSS := by
  intro cause member
  have prior := covered cause member
  have window := ReceiveAdvertisement.candidate_mono_free state.advertisement capacity before after outgoingMSS valid.2 growth
  exact ⟨prior.1, Nat.le_trans prior.2 (Nat.add_le_add_left window _)⟩

theorem receiveSequence_covered (state : State) (now : Nat) (cursor : Seq) (capacity free outgoingMSS : Nat)
    (covered : state.Covered capacity free outgoingMSS) :
    (receiveSequence state now cursor).Covered capacity free outgoingMSS := by
  intro cause member
  change cause ∈ state.work.pending ++ [Netlib.Theory.TimedReaction.fresh state.work now (demand state .sequence cursor 0 0) 0] at member
  rcases List.mem_append.mp member with old | current
  · exact covered cause old
  · have same := List.mem_singleton.mp current
    subst cause
    exact ⟨Nat.le_refl _, Nat.zero_le _⟩

theorem receiveRelease_covered (state : State) (now : Nat) (cursor : Seq) (novel released : Nat)
    (immediate : Bool) (capacity free outgoingMSS : Nat)
    (covered : state.Covered capacity free outgoingMSS) (valid : state.advertisement.Valid free)
    (fits : released ≤ state.window) :
    (receiveRelease state now cursor novel released immediate).Covered capacity (free - released) outgoingMSS := by
  intro cause member
  simp only [receiveRelease, T.issue, Netlib.Theory.TimedReaction.issue] at member ⊢
  rcases List.mem_append.mp member with old | current
  · have prior := covered cause old
    constructor
    · change cause.demand.position ≤ state.advertisement.frontier + released
      omega
    · change cause.demand.minimumEdge ≤ (ReceiveAdvertisement.consume state.advertisement released).frontier +
        ReceiveAdvertisement.candidate (ReceiveAdvertisement.consume state.advertisement released) capacity (free - released) outgoingMSS
      rw [ReceiveAdvertisement.candidate_edge_consume _ _ _ _ _ valid fits]
      exact prior.2
  · have same := List.mem_singleton.mp current
    subst cause
    exact ⟨Nat.le_refl _, Nat.zero_le _⟩

theorem read_covered (state : State) (now : Nat) (cursor : Seq) (capacity before after outgoingMSS : Nat)
    (covered : state.Covered capacity before outgoingMSS) (valid : state.advertisement.Valid before)
    (growth : before ≤ after) : (read state now cursor capacity before after outgoingMSS).Covered capacity after outgoingMSS := by
  have retained := Covered.more_free state capacity before after outgoingMSS covered valid growth
  unfold read
  dsimp only
  split
  · intro cause member
    change cause ∈ state.work.pending ++ [_] at member
    rcases List.mem_append.mp member with old | current
    · exact retained cause old
    · have same := List.mem_singleton.mp current
      subst cause
      exact ⟨Nat.le_refl _, Nat.le_refl _⟩
  · exact retained

theorem outputState_covered (state : State) (now : Nat) (cursor : Seq) (capacity free outgoingMSS : Nat) :
    (outputState state now cursor capacity free outgoingMSS).Covered capacity free outgoingMSS := by
  intro cause member
  unfold outputState at member
  split at member
  · have empty : state.work.pending = [] := List.isEmpty_iff.mp (by assumption)
    simp [empty] at member
  · simp [T.completedState, Netlib.Theory.TimedReaction.completedState] at member

theorem receiveSequence_coherent (state : State) (now : Nat) (cursor : Seq) (free rmss : Nat)
    (coherent : state.Coherent cursor free rmss) :
    (receiveSequence state now cursor).Coherent cursor free rmss := by
  refine ⟨coherent.1, coherent.2.1, coherent.2.2.1, coherent.2.2.2.1, ?_⟩
  intro cause member
  change cause ∈ state.work.pending ++ [_] at member
  rcases List.mem_append.mp member with old | current
  · exact coherent.2.2.2.2 cause old
  · have same := List.mem_singleton.mp current
    subst cause
    exact ⟨Nat.le_refl _, coherent.2.1.symm⟩

theorem receiveRelease_coherent (state : State) (now : Nat) (cursor : Seq) (novel released : Nat)
    (immediate : Bool) (free rmss : Nat) (coherent : state.Coherent cursor free rmss)
    (fits : released ≤ state.window) :
    (receiveRelease state now (cursor.add released) novel released immediate).Coherent
      (cursor.add released) (free - released) rmss := by
  refine ⟨ReceiveAdvertisement.consume_valid _ _ _ coherent.1 fits, ?_, coherent.2.2.1, coherent.2.2.2.1, ?_⟩
  · change state.origin.add (state.advertisement.frontier + released) = cursor.add released
    rw [← Seq.add_add, coherent.2.1]
  · intro cause member
    change cause ∈ state.work.pending ++ [_] at member
    rcases List.mem_append.mp member with old | current
    · have prior := coherent.2.2.2.2 cause old
      exact ⟨Nat.le_trans prior.1 (Nat.le_add_right _ _), prior.2⟩
    · have same := List.mem_singleton.mp current
      subst cause
      constructor
      · exact Nat.le_refl _
      · change cursor.add released = state.origin.add (state.advertisement.frontier + released)
        rw [← Seq.add_add, coherent.2.1]

theorem receiveSequence_within (state : State) (now : Nat) (cursor : Seq) (timely : state.WithinTime now) :
    (receiveSequence state now cursor).WithinTime now :=
  Netlib.Theory.TimedReaction.issue_time_fields _ _ _ _ timely

theorem receiveRelease_within (state : State) (now : Nat) (cursor : Seq) (novel released : Nat)
    (immediate : Bool) (timely : state.WithinTime now) :
    (receiveRelease state now cursor novel released immediate).WithinTime now :=
  Netlib.Theory.TimedReaction.issue_time_fields _ _ _ _ timely

theorem read_within (state : State) (now : Nat) (cursor : Seq) (capacity before after outgoingMSS : Nat)
    (timely : state.WithinTime now) : (read state now cursor capacity before after outgoingMSS).WithinTime now := by
  unfold read
  dsimp only
  split
  · exact Netlib.Theory.TimedReaction.issue_time_fields _ _ _ _ timely
  · exact timely

theorem read_coherent (state : State) (now : Nat) (cursor : Seq) (capacity before after outgoingMSS rmss : Nat)
    (coherent : state.Coherent cursor before rmss) (growth : before ≤ after) :
    (read state now cursor capacity before after outgoingMSS).Coherent cursor after rmss := by
  have valid := ReceiveAdvertisement.more_free_valid _ before after coherent.1 growth
  unfold read
  dsimp only
  split
  · refine ⟨valid, coherent.2.1, coherent.2.2.1, coherent.2.2.2.1, ?_⟩
    intro cause member
    change cause ∈ state.work.pending ++ [_] at member
    rcases List.mem_append.mp member with old | current
    · exact coherent.2.2.2.2 cause old
    · have same := List.mem_singleton.mp current
      subst cause
      exact ⟨Nat.le_refl _, coherent.2.1.symm⟩
  · exact ⟨valid, coherent.2⟩

theorem outputState_pending (state : State) (now : Nat) (cursor : Seq) (capacity free outgoingMSS : Nat) :
    (outputState state now cursor capacity free outgoingMSS).work.pending = [] := by
  unfold outputState
  split
  · exact List.isEmpty_iff.mp (by assumption)
  · rfl

theorem outputState_within (state : State) (now : Nat) (cursor : Seq) (capacity free outgoingMSS time : Nat) :
    (outputState state now cursor capacity free outgoingMSS).WithinTime time := by
  simp only [State.WithinTime, outputState_pending, List.not_mem_nil, false_implies, implies_true]

theorem outputState_coherent (state : State) (now : Nat) (cursor : Seq) (capacity free outgoingMSS rmss : Nat)
    (coherent : state.Coherent cursor free rmss) :
    (outputState state now cursor capacity free outgoingMSS).Coherent cursor free rmss := by
  refine ⟨ReceiveAdvertisement.commit_valid _ _ _ _ coherent.1, coherent.2.1,
    coherent.2.2.1, coherent.2.2.2.1, ?_⟩
  intro cause member
  rw [outputState_pending] at member
  contradiction

theorem receiveData_eq_release (state : State) (now : Nat) (cursor : Seq) (count : Nat) :
    receiveData state now cursor count = receiveRelease state now cursor count count false := by
  simp [receiveData, receiveRelease]

end Netlib.Protocol.TCP.AckReaction
