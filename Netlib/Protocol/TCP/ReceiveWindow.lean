import Netlib.Protocol.TCP.Segment
import Netlib.Protocol.TCP.SequenceSpace

/-!
# TCP receive-window tests

This module gives the four sequence tests in [RFC 9293, section 3.4](https://www.rfc-editor.org/rfc/rfc9293.html#section-3.4).
The positive-length test requires the first or last occupied position inside the window.
This module does not process ACK, RST, URG, or connection state.
An endpoint must also obey the zero-window rules for control fields.
Short-window laws state their bounds explicitly.
-/

namespace Netlib.Protocol.TCP.ReceiveWindow

def Acceptable (next : Seq) (window : Nat) (sequence : Seq) (length : Nat) : Prop :=
  (length = 0 ∧ window = 0 ∧ sequence = next) ∨
    (length = 0 ∧ 0 < window ∧ Seq.InInterval next window sequence) ∨
    (0 < length ∧ 0 < window ∧
      (Seq.InInterval next window sequence ∨ Seq.InInterval next window (sequence.add (length - 1))))

instance (next : Seq) (window : Nat) (sequence : Seq) (length : Nat) :
    Decidable (Acceptable next window sequence length) := by
  unfold Acceptable
  infer_instance

def accepts (next : Seq) (window : Nat) (sequence : Seq) (length : Nat) : Bool :=
  if length = 0 then
    if window = 0 then decide (sequence = next)
    else Seq.inInterval next window sequence
  else if window = 0 then false
  else Seq.inInterval next window sequence || Seq.inInterval next window (sequence.add (length - 1))

theorem accepts_correct (next : Seq) (window : Nat) (sequence : Seq) (length : Nat) :
    accepts next window sequence length = true ↔ Acceptable next window sequence length := by
  by_cases empty : length = 0 <;> by_cases closed : window = 0 <;>
    simp [accepts, Acceptable, empty, closed, Nat.pos_iff_ne_zero]

@[simp] theorem zero_length_zero_window (next sequence : Seq) :
    accepts next 0 sequence 0 = true ↔ sequence = next := by simp [accepts]

theorem zero_length_positive_window (next sequence : Seq) (window : Nat) (positive : 0 < window) :
    accepts next window sequence 0 = true ↔ Seq.InInterval next window sequence := by
  simp [accepts, Nat.ne_of_gt positive]

@[simp] theorem positive_length_zero_window (next sequence : Seq) (length : Nat) (positive : 0 < length) :
    accepts next 0 sequence length = false := by simp [accepts, Nat.ne_of_gt positive]

theorem zero_window (next sequence : Seq) (length : Nat) :
    accepts next 0 sequence length = true ↔ length = 0 ∧ sequence = next := by
  by_cases empty : length = 0 <;> simp [accepts, empty]

theorem first_or_last (next sequence : Seq) (window length : Nat)
    (positiveWindow : 0 < window) (positiveLength : 0 < length) :
    accepts next window sequence length = true ↔
      Seq.InInterval next window sequence ∨ Seq.InInterval next window (sequence.add (length - 1)) := by
  simp [accepts, Nat.ne_of_gt positiveWindow, Nat.ne_of_gt positiveLength]

theorem first_inside (next sequence : Seq) (window length : Nat)
    (positiveWindow : 0 < window) (positiveLength : 0 < length)
    (inside : Seq.InInterval next window sequence) : accepts next window sequence length = true :=
  (first_or_last next sequence window length positiveWindow positiveLength).mpr (Or.inl inside)

theorem last_inside (next sequence : Seq) (window length : Nat)
    (positiveWindow : 0 < window) (positiveLength : 0 < length)
    (inside : Seq.InInterval next window (sequence.add (length - 1))) :
    accepts next window sequence length = true :=
  (first_or_last next sequence window length positiveWindow positiveLength).mpr (Or.inr inside)

theorem neither_endpoint (next sequence : Seq) (window length : Nat)
    (positiveWindow : 0 < window) (positiveLength : 0 < length)
    (firstOutside : ¬Seq.InInterval next window sequence)
    (lastOutside : ¬Seq.InInterval next window (sequence.add (length - 1))) :
    accepts next window sequence length = false := by
  cases result : accepts next window sequence length
  · rfl
  · have selected := (first_or_last next sequence window length positiveWindow positiveLength).mp result
    exact False.elim (selected.elim firstOutside lastOutside)

theorem at_next (next : Seq) (window length : Nat) :
    accepts next window next length = true ↔ length = 0 ∨ 0 < window := by
  by_cases empty : length = 0 <;> by_cases closed : window = 0 <;>
    simp [accepts, empty, closed, Seq.InInterval, Nat.pos_iff_ne_zero]

theorem left_edge (next : Seq) (window length : Nat) (positive : 0 < window) :
    accepts next window next length = true := (at_next next window length).mpr (Or.inr positive)

theorem in_order_fits (next : Seq) (window length : Nat) (fits : length ≤ window) :
    accepts next window next length = true := by
  apply (at_next next window length).mpr
  omega

theorem single_position (next sequence : Seq) (window : Nat) :
    accepts next window sequence 1 = true ↔ Seq.InInterval next window sequence := by
  by_cases closed : window = 0
  · simp [accepts, closed, Seq.InInterval]
  · simp [accepts, closed]

theorem window_mono (next sequence : Seq) (small large length : Nat) (ordered : small ≤ large)
    (accepted : accepts next small sequence length = true) : accepts next large sequence length = true := by
  rw [accepts_correct] at accepted ⊢
  rcases accepted with ⟨empty, closed, rfl⟩ | ⟨empty, positive, inside⟩ | ⟨positive, positiveWindow, first | last⟩
  · subst length
    by_cases zero : large = 0
    · exact Or.inl ⟨rfl, zero, rfl⟩
    · exact Or.inr (Or.inl ⟨rfl, by omega, by simpa [Seq.InInterval] using Nat.pos_of_ne_zero zero⟩)
  · exact Or.inr (Or.inl ⟨empty, by omega, Nat.lt_of_lt_of_le inside ordered⟩)
  · exact Or.inr (Or.inr ⟨positive, by omega, Or.inl (Nat.lt_of_lt_of_le first ordered)⟩)
  · exact Or.inr (Or.inr ⟨positive, by omega, Or.inr (Nat.lt_of_lt_of_le last ordered)⟩)

theorem zero_length_coordinate (next : Seq) (window offset : Nat)
    (bounded : offset < Seq.modulus) :
    accepts next window (next.add offset) 0 = true ↔
      (window = 0 ∧ offset = 0) ∨ (0 < window ∧ offset < window) := by
  have distance := Seq.distance_add next offset
  rw [Nat.mod_eq_of_lt bounded] at distance
  have same : next.add offset = next ↔ offset = 0 := by
    constructor
    · intro equal
      rw [equal, Seq.distance_self] at distance
      exact distance.symm
    · rintro rfl
      exact Seq.add_zero next
  by_cases closed : window = 0
  · simp [accepts, closed, same]
  · simp [accepts, closed, Seq.InInterval, distance, Nat.pos_iff_ne_zero]

theorem right_edge_empty_rejected (next : Seq) (window : Nat)
    (positive : 0 < window) (short : window < Seq.halfSpace) :
    accepts next window (next.add window) 0 = false := by
  have bounded : window < Seq.modulus := by unfold Seq.modulus Seq.halfSpace at *; omega
  have selected := zero_length_coordinate next window window bounded
  have notAccepted : accepts next window (next.add window) 0 ≠ true := by
    intro accepted
    have := selected.mp accepted
    omega
  cases result : accepts next window (next.add window) 0
  · rfl
  · exact False.elim (notAccepted result)

theorem coordinate_positive (next : Seq) (window offset length : Nat)
    (positiveWindow : 0 < window) (positiveLength : 0 < length) :
    accepts next window (next.add offset) length = true ↔
      offset % Seq.modulus < window ∨ (offset + (length - 1)) % Seq.modulus < window := by
  rw [first_or_last next (next.add offset) window length positiveWindow positiveLength]
  simp only [Seq.InInterval, Seq.add_add, Seq.distance_add]

theorem acceptable_translate (next sequence : Seq) (window length offset : Nat) :
    Acceptable (next.add offset) window (sequence.add offset) length ↔
      Acceptable next window sequence length := by
  have same : sequence.add offset = next.add offset ↔ sequence = next := by
    constructor
    · intro equal
      exact Seq.add_injective offset equal
    · exact congrArg (fun value : Seq => value.add offset)
  have last : (sequence.add offset).add (length - 1) = (sequence.add (length - 1)).add offset := by
    rw [Seq.add_add, Seq.add_add, Nat.add_comm offset]
  simp only [Acceptable, same, last, Seq.interval_translate]

theorem accepts_translate (next sequence : Seq) (window length offset : Nat) :
    accepts (next.add offset) window (sequence.add offset) length = accepts next window sequence length := by
  have same := acceptable_translate next sequence window length offset
  rw [← accepts_correct, ← accepts_correct] at same
  cases first : accepts (next.add offset) window (sequence.add offset) length <;>
    cases second : accepts next window sequence length <;> simp_all

@[simp] theorem sequence_add_modulus (next sequence : Seq) (window length : Nat) :
    accepts next window (sequence.add Seq.modulus) length = accepts next window sequence length := by
  rw [Seq.add_modulus]

theorem covered_window_rejected (next : Seq) (window : Nat)
    (positive : 0 < window) (short : window < Seq.halfSpace) :
    accepts next window (next.add (Seq.modulus - 1)) (window + 2) = false := by
  have bounded : window < Seq.modulus := by unfold Seq.modulus Seq.halfSpace at *; omega
  have firstDistance : Seq.distance next (next.add (Seq.modulus - 1)) = Seq.modulus - 1 := by
    rw [Seq.distance_add, Nat.mod_eq_of_lt (by decide)]
  have final : (next.add (Seq.modulus - 1)).add (window + 2 - 1) = next.add window := by
    rw [Seq.add_add]
    have sum : Seq.modulus - 1 + (window + 2 - 1) = Seq.modulus + window := by
      unfold Seq.modulus
      omega
    rw [sum, ← Seq.add_add, Seq.add_modulus]
  apply neither_endpoint next _ window (window + 2) positive (by omega)
  · unfold Seq.InInterval
    rw [firstDistance]
    unfold Seq.modulus Seq.halfSpace at *
    omega
  · rw [final]
    unfold Seq.InInterval
    rw [Seq.distance_add, Nat.mod_eq_of_lt bounded]
    omega

theorem covered_window_contains (next : Seq) (window offset : Nat)
    (short : window < Seq.halfSpace) (inside : offset < window) :
    Seq.InInterval (next.add (Seq.modulus - 1)) (window + 2) (next.add offset) := by
  have bounded : offset + 1 < Seq.modulus := by unfold Seq.modulus Seq.halfSpace at *; omega
  have selected : (next.add (Seq.modulus - 1)).add (offset + 1) = next.add offset := by
    rw [Seq.add_add]
    have sum : Seq.modulus - 1 + (offset + 1) = Seq.modulus + offset := by
      unfold Seq.modulus
      omega
    rw [sum, ← Seq.add_add, Seq.add_modulus]
  rw [← selected]
  unfold Seq.InInterval
  rw [Seq.distance_add, Nat.mod_eq_of_lt bounded]
  omega

theorem covered_window_counterexample (next : Seq) (window : Nat)
    (positive : 0 < window) (short : window < Seq.halfSpace) :
    (∀ position, Seq.InInterval next window position →
      Seq.InInterval (next.add (Seq.modulus - 1)) (window + 2) position) ∧
      accepts next window (next.add (Seq.modulus - 1)) (window + 2) = false := by
  constructor
  · intro position inside
    obtain ⟨offset, bounded, rfl⟩ := (Seq.interval_coordinates next position window short).mp inside
    exact covered_window_contains next window offset short bounded
  · exact covered_window_rejected next window positive short

def acceptsUnscaled (next : Seq) (window : InternetChecksum.Word) (sequence : Seq) (length : Nat) : Bool :=
  accepts next window.val sequence length

theorem short_of_unscaled_bound (window : Nat) (bounded : window ≤ 65535) : window < Seq.halfSpace := by
  unfold Seq.halfSpace
  omega

theorem unscaled_short (window : InternetChecksum.Word) : window.val < Seq.halfSpace := by
  exact short_of_unscaled_bound window.val (by have := window.isLt; omega)

theorem acceptsUnscaled_correct (next sequence : Seq) (window : InternetChecksum.Word) (length : Nat) :
    acceptsUnscaled next window sequence length = true ↔ Acceptable next window.val sequence length :=
  accepts_correct next window.val sequence length

def segmentLength (segment : Segment) : Nat := occupiedLength segment.payload.length segment.flags

def acceptsSegment (next : Seq) (window : Nat) (segment : Segment) : Bool :=
  accepts next window segment.sequence (segmentLength segment)

theorem acceptsSegment_correct (next : Seq) (window : Nat) (segment : Segment) :
    acceptsSegment next window segment = true ↔
      Acceptable next window segment.sequence (occupiedLength segment.payload.length segment.flags) :=
  accepts_correct next window segment.sequence (segmentLength segment)

theorem segmentLength_bounds (segment : Segment) :
    segment.payload.length ≤ segmentLength segment ∧ segmentLength segment ≤ segment.payload.length + 2 :=
  occupiedLength_bounds segment.payload.length segment.flags

theorem segmentLength_zero (segment : Segment) :
    segmentLength segment = 0 ↔
      segment.payload = [] ∧ Flags.syn segment.flags = false ∧ Flags.fin segment.flags = false := by
  simp [segmentLength, occupiedLength_zero_iff]

theorem segmentLength_no_control (segment : Segment)
    (noSyn : Flags.syn segment.flags = false) (noFin : Flags.fin segment.flags = false) :
    segmentLength segment = segment.payload.length :=
  occupiedLength_no_control segment.payload.length segment.flags noSyn noFin

theorem segmentLength_short (segment : Segment) (bounded : segment.Encodable) :
    segmentLength segment < Seq.halfSpace := by
  have payload := bounded.2.2.2
  have occupied := segmentLength_bounds segment
  unfold Segment.wireLength Segment.headerLength at payload
  unfold Seq.halfSpace
  omega

theorem acceptsSegment_zero_window (next : Seq) (segment : Segment) :
    acceptsSegment next 0 segment = true ↔
      segment.payload = [] ∧ Flags.syn segment.flags = false ∧ Flags.fin segment.flags = false ∧
        segment.sequence = next := by
  rw [acceptsSegment, zero_window, segmentLength_zero]
  simp only [and_assoc]

end Netlib.Protocol.TCP.ReceiveWindow
