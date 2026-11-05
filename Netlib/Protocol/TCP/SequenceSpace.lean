import Netlib.Protocol.TCP.Basic

/-!
# Cyclic TCP sequence arithmetic

Comparison uses an open half-space without a global ordering instance.
Common-arc order laws require a span below half the sequence space.
[Sequence numbers](https://www.rfc-editor.org/rfc/rfc9293.html#section-3.4)
and [serial comparisons](https://www.rfc-editor.org/rfc/rfc7323.html#section-5.2) define the arithmetic.
[Window scaling](https://www.rfc-editor.org/rfc/rfc7323.html#section-2.3) motivates the bounded spans.
-/

namespace Netlib.Protocol.TCP

namespace Seq

def modulus : Nat := 4294967296
def halfSpace : Nat := 2147483648

def add (value : Seq) (offset : Nat) : Seq := ofNat (value.val + offset)

def distance (start stop : Seq) : Nat := (stop.val + modulus - start.val) % modulus

def Before (first second : Seq) : Prop := 0 < distance first second ∧ distance first second < halfSpace

instance (first second : Seq) : Decidable (Before first second) := by unfold Before; infer_instance

def before (first second : Seq) : Bool := decide (Before first second)

def InInterval (start : Seq) (length : Nat) (value : Seq) : Prop := distance start value < length

instance (start : Seq) (length : Nat) (value : Seq) : Decidable (InInterval start length value) := by
  unfold InInterval
  infer_instance

def inInterval (start : Seq) (length : Nat) (value : Seq) : Bool := decide (InInterval start length value)

@[simp] theorem before_correct (first second : Seq) : before first second = true ↔ Before first second := by simp [before]
@[simp] theorem inInterval_correct (start : Seq) (length : Nat) (value : Seq) :
    inInterval start length value = true ↔ InInterval start length value := by simp [inInterval]

@[simp] theorem val_ofNat (value : Nat) : (ofNat value).val = value % modulus := rfl
@[simp] theorem val_add (value : Seq) (offset : Nat) : (value.add offset).val = (value.val + offset) % modulus := rfl

theorem distance_lt (start stop : Seq) : distance start stop < modulus := Nat.mod_lt _ (by decide)

theorem distance_cases (start stop : Seq) : distance start stop =
    if start.val ≤ stop.val then stop.val - start.val else modulus + stop.val - start.val := by
  have first := start.val_lt
  have second := stop.val_lt
  unfold distance modulus
  split <;> omega

@[simp] theorem distance_self (value : Seq) : distance value value = 0 := by rw [distance_cases]; simp

theorem distance_eq_zero (first second : Seq) : distance first second = 0 ↔ first = second := by
  have firstBound := first.val_lt
  have secondBound := second.val_lt
  rw [distance_cases]
  constructor
  · intro zero
    apply Seq.ext
    split at zero
    · omega
    · unfold modulus at zero
      omega
  · rintro rfl
    simp

@[simp] theorem add_zero (value : Seq) : value.add 0 = value := by
  apply Seq.ext
  rw [val_add, Nat.add_zero]
  exact Nat.mod_eq_of_lt value.val_lt

theorem add_add (value : Seq) (first second : Nat) : (value.add first).add second = value.add (first + second) := by
  apply Seq.ext
  simp only [val_add, Nat.mod_add_mod, Nat.add_assoc]

theorem add_distance (start stop : Seq) : start.add (distance start stop) = stop := by
  apply Seq.ext
  have first := start.val_lt
  have second := stop.val_lt
  rw [val_add, distance_cases]
  split <;> simp only [modulus] <;> omega

theorem distance_add (start : Seq) (offset : Nat) : distance start (start.add offset) = offset % modulus := by
  have first := start.val_lt
  simp only [distance, val_add, modulus]
  omega

theorem distance_translate (first second : Seq) (offset : Nat) :
    distance (first.add offset) (second.add offset) = distance first second := by
  have firstBound := first.val_lt
  have secondBound := second.val_lt
  simp only [distance, val_add, modulus]
  omega

theorem distance_triangle_mod (first middle last : Seq) :
    distance first last = (distance first middle + distance middle last) % modulus := by
  have firstBound := first.val_lt
  have middleBound := middle.val_lt
  have lastBound := last.val_lt
  simp only [distance, modulus]
  omega

theorem distance_reverse (first second : Seq) (different : first ≠ second) :
    distance first second + distance second first = modulus := by
  have firstBound := first.val_lt
  have secondBound := second.val_lt
  have values : first.val ≠ second.val := fun same => different (Seq.ext same)
  rw [distance_cases, distance_cases]
  split <;> split <;> unfold modulus <;> omega

theorem add_injective (offset : Nat) : Function.Injective (fun value : Seq => value.add offset) := by
  intro first second same
  change first.add offset = second.add offset at same
  apply (distance_eq_zero first second).mp
  rw [← distance_translate first second offset, same, distance_self]

@[simp] theorem add_modulus (value : Seq) : value.add modulus = value := by
  apply Seq.ext
  rw [val_add, Nat.add_mod_right]
  exact Nat.mod_eq_of_lt value.val_lt

theorem before_translate (first second : Seq) (offset : Nat) :
    Before (first.add offset) (second.add offset) ↔ Before first second := by
  simp only [Before, distance_translate]

theorem interval_translate (start value : Seq) (length offset : Nat) :
    InInterval (start.add offset) length (value.add offset) ↔ InInterval start length value := by
  simp only [InInterval, distance_translate]

theorem before_irrefl (value : Seq) : ¬Before value value := by simp [Before]

theorem before_asymm (first second : Seq) (ordered : Before first second) : ¬Before second first := by
  have different : first ≠ second := by rintro rfl; exact before_irrefl _ ordered
  have total := distance_reverse first second different
  unfold Before halfSpace at ordered ⊢
  unfold modulus at total
  omega

theorem halfSpace_incomparable (first second : Seq) (opposite : distance first second = halfSpace) :
    ¬Before first second ∧ ¬Before second first := by
  have different : first ≠ second := by
    rintro rfl
    rw [distance_self] at opposite
    cases opposite
  have total := distance_reverse first second different
  unfold halfSpace at opposite
  unfold Before halfSpace
  unfold modulus at total
  omega

theorem before_or_reverse (first second : Seq) (different : first ≠ second)
    (notOpposite : distance first second ≠ halfSpace) : Before first second ∨ Before second first := by
  have total := distance_reverse first second different
  have nonzero : distance first second ≠ 0 := fun zero => different ((distance_eq_zero _ _).mp zero)
  have reverseNonzero : distance second first ≠ 0 := fun zero => different ((distance_eq_zero _ _).mp zero).symm
  unfold halfSpace at notOpposite
  unfold Before halfSpace
  unfold modulus at total
  omega

theorem before_trans_of_sum_lt_halfSpace (first middle last : Seq) (firstStep : Before first middle)
    (secondStep : Before middle last) (span : distance first middle + distance middle last < halfSpace) :
    Before first last := by
  have total := distance_triangle_mod first middle last
  have bounded : distance first middle + distance middle last < modulus := by
    unfold modulus halfSpace at *
    omega
  rw [Nat.mod_eq_of_lt bounded] at total
  unfold Before at firstStep secondStep ⊢
  omega

theorem common_arc_distance (origin first second : Seq) (length : Nat) (short : length < halfSpace)
    (firstInside : InInterval origin length first) (_secondInside : InInterval origin length second)
    (ordered : distance origin first ≤ distance origin second) :
    distance first second = distance origin second - distance origin first := by
  have total := distance_triangle_mod origin first second
  have bounded := distance_lt first second
  unfold InInterval at firstInside _secondInside
  unfold modulus halfSpace at *
  omega

theorem common_arc_before (origin first second : Seq) (length : Nat) (short : length < halfSpace)
    (firstInside : InInterval origin length first) (secondInside : InInterval origin length second) :
    Before first second ↔ distance origin first < distance origin second := by
  have total := distance_triangle_mod origin first second
  have bounded := distance_lt first second
  unfold Before InInterval halfSpace modulus at *
  omega

theorem common_arc_trans (origin first middle last : Seq) (length : Nat) (short : length < halfSpace)
    (firstInside : InInterval origin length first) (middleInside : InInterval origin length middle)
    (lastInside : InInterval origin length last) (firstStep : Before first middle) (secondStep : Before middle last) :
    Before first last := by
  rw [common_arc_before origin first last length short firstInside lastInside]
  exact Nat.lt_trans ((common_arc_before origin first middle length short firstInside middleInside).mp firstStep)
    ((common_arc_before origin middle last length short middleInside lastInside).mp secondStep)

theorem interval_coordinates (start value : Seq) (length : Nat) (short : length < halfSpace) :
    InInterval start length value ↔ ∃ offset, offset < length ∧ start.add offset = value := by
  constructor
  · intro inside
    exact ⟨distance start value, inside, add_distance start value⟩
  · rintro ⟨offset, bounded, rfl⟩
    have small : offset < modulus := by unfold halfSpace modulus at *; omega
    unfold InInterval
    rw [distance_add, Nat.mod_eq_of_lt small]
    exact bounded

theorem interval_coordinate_unique (start value : Seq) (length : Nat) (short : length < halfSpace)
    (first second : Nat) (firstInside : first < length) (secondInside : second < length)
    (firstValue : start.add first = value) (secondValue : start.add second = value) : first = second := by
  have firstBound : first < modulus := by unfold halfSpace modulus at *; omega
  have secondBound : second < modulus := by unfold halfSpace modulus at *; omega
  have selected := congrArg (distance start) (firstValue.trans secondValue.symm)
  rw [distance_add, distance_add, Nat.mod_eq_of_lt firstBound, Nat.mod_eq_of_lt secondBound] at selected
  exact selected

end Seq

def occupiedLength (payloadLength : Nat) (flags : UInt8) : Nat :=
  payloadLength + (if Flags.syn flags then 1 else 0) + (if Flags.fin flags then 1 else 0)

def nextSequence (start : Seq) (payloadLength : Nat) (flags : UInt8) : Seq :=
  start.add (occupiedLength payloadLength flags)

theorem occupiedLength_bounds (payloadLength : Nat) (flags : UInt8) :
    payloadLength ≤ occupiedLength payloadLength flags ∧ occupiedLength payloadLength flags ≤ payloadLength + 2 := by
  unfold occupiedLength
  split <;> split <;> omega

theorem occupiedLength_no_control (payloadLength : Nat) (flags : UInt8)
    (noSyn : Flags.syn flags = false) (noFin : Flags.fin flags = false) :
    occupiedLength payloadLength flags = payloadLength := by simp [occupiedLength, noSyn, noFin]

theorem occupiedLength_zero_iff (payloadLength : Nat) (flags : UInt8) :
    occupiedLength payloadLength flags = 0 ↔ payloadLength = 0 ∧ Flags.syn flags = false ∧ Flags.fin flags = false := by
  cases syn : Flags.syn flags <;> cases fin : Flags.fin flags <;> simp [occupiedLength, syn, fin]

theorem nextSequence_distance (start : Seq) (payloadLength : Nat) (flags : UInt8)
    (bounded : occupiedLength payloadLength flags < Seq.modulus) :
    Seq.distance start (nextSequence start payloadLength flags) = occupiedLength payloadLength flags := by
  rw [nextSequence, Seq.distance_add, Nat.mod_eq_of_lt bounded]

end Netlib.Protocol.TCP
