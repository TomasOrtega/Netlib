import Std

namespace Netlib.Packet.Interval

/-- Choose the greatest boundary at or below a value. -/
def floor : List Nat → Nat → Nat
  | [], _ => 0
  | boundary :: boundaries, value =>
    if boundary ≤ value then max boundary (floor boundaries value)
    else floor boundaries value

theorem floor_le (boundaries : List Nat) (value : Nat) : floor boundaries value ≤ value := by
  induction boundaries with
  | nil => simp [floor]
  | cons boundary boundaries ih =>
    simp only [floor]
    split
    · exact Nat.max_le.mpr ⟨by assumption, ih⟩
    · exact ih

theorem boundary_le_floor (boundaries : List Nat) (value boundary : Nat)
    (member : boundary ∈ boundaries) (below : boundary ≤ value) :
    boundary ≤ floor boundaries value := by
  induction boundaries with
  | nil => simp at member
  | cons first rest ih =>
    rcases List.mem_cons.mp member with rfl | member
    · simp only [floor, below, ite_true]
      exact Nat.le_max_left _ _
    · have tail := ih member
      simp only [floor]
      split
      · exact Nat.le_trans tail (Nat.le_max_right _ _)
      · exact tail

theorem boundary_le_floor_iff (boundaries : List Nat) (value boundary : Nat)
    (member : boundary ∈ boundaries) :
    boundary ≤ floor boundaries value ↔ boundary ≤ value :=
  ⟨fun below => Nat.le_trans below (floor_le _ _), boundary_le_floor _ _ _ member⟩

theorem floor_mem (boundaries : List Nat) (value : Nat) :
    floor boundaries value = 0 ∨ floor boundaries value ∈ boundaries := by
  induction boundaries with
  | nil => exact .inl rfl
  | cons boundary boundaries ih =>
    simp only [floor]
    split
    · by_cases larger : floor boundaries value ≤ boundary
      · exact .inr (by simp [Nat.max_eq_left larger])
      · rw [Nat.max_eq_right (by omega)]
        rcases ih with zero | member
        · exact .inl zero
        · exact .inr (List.mem_cons_of_mem _ member)
    · rcases ih with zero | member
      · exact .inl zero
      · exact .inr (List.mem_cons_of_mem _ member)

/-- Representatives depend on the boundaries, not the numeric field width. -/
def points (size : Nat) [NeZero size] (boundaries : List Nat) : List (Fin size) :=
  (((0 :: boundaries).filter (fun value => value < size)).map (Fin.ofNat size)).eraseDups

def representative (boundaries : List Nat) (value : Fin size) : Fin size :=
  ⟨floor boundaries value.val, Nat.lt_of_le_of_lt (floor_le _ _) value.isLt⟩

theorem representative_mem_points [NeZero size] (boundaries : List Nat) (value : Fin size) :
    representative boundaries value ∈ points size boundaries := by
  apply List.mem_eraseDups.mpr
  apply List.mem_map.mpr
  refine ⟨floor boundaries value.val, List.mem_filter.mpr ⟨?_, ?_⟩, ?_⟩
  · rcases floor_mem boundaries value.val with zero | member
    · simp [zero]
    · exact List.mem_cons_of_mem _ member
  · exact decide_eq_true (Nat.lt_of_le_of_lt (floor_le _ _) value.isLt)
  · apply Fin.ext
    exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (floor_le _ _) value.isLt)

theorem representative_le_iff (boundaries : List Nat) (value : Fin size) (boundary : Nat)
    (member : boundary ∈ boundaries) :
    boundary ≤ (representative boundaries value).val ↔ boundary ≤ value.val :=
  boundary_le_floor_iff _ _ _ member

theorem representative_lt_iff (boundaries : List Nat) (value : Fin size) (boundary : Nat)
    (member : boundary ∈ boundaries) :
    (representative boundaries value).val < boundary ↔ value.val < boundary := by
  have := representative_le_iff boundaries value boundary member
  omega

end Netlib.Packet.Interval
