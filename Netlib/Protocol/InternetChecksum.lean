import Std

/-!
# Internet checksum

Adjacent bytes form network-order words; a final odd byte has a zero low byte.
End-around carry retains both one's-complement representations of zero.
-/

namespace Netlib.Protocol.InternetChecksum

abbrev Word := Fin 65536

def highByte (value : Word) : UInt8 := UInt8.ofNat (value.val / 256)
def lowByte (value : Word) : UInt8 := UInt8.ofNat value.val

def read16 (high low : UInt8) : Word :=
  ⟨high.toNat * 256 + low.toNat, by have := high.toNat_lt; have := low.toNat_lt; omega⟩

def wordBytes (value : Word) : List UInt8 := [highByte value, lowByte value]

@[simp] theorem wordBytes_length (value : Word) : (wordBytes value).length = 2 := rfl

@[simp] theorem wordBytes_zero : wordBytes (0 : Word) = [0, 0] := rfl

theorem read16_bytes (value : Word) : read16 (highByte value) (lowByte value) = value := by
  apply Fin.ext
  have bounded := value.isLt
  have high : value.val / 256 < 256 := by omega
  simp only [read16, highByte, lowByte, UInt8.toNat_ofNat']
  change value.val / 256 % 256 * 256 + value.val % 256 = value.val
  rw [Nat.mod_eq_of_lt high]
  omega

@[simp] theorem highByte_read16 (high low : UInt8) : highByte (read16 high low) = high := by
  have lower := low.toNat_lt
  have quotient : (read16 high low).val / 256 = high.toNat := by
    change (high.toNat * 256 + low.toNat) / 256 = high.toNat
    omega
  simp [highByte, quotient]

@[simp] theorem lowByte_read16 (high low : UInt8) : lowByte (read16 high low) = low := by
  apply UInt8.toNat_inj.mp
  have lower := low.toNat_lt
  simp only [lowByte, read16, UInt8.toNat_ofNat']
  change (high.toNat * 256 + low.toNat) % 256 = low.toNat
  omega

def total : List UInt8 → Nat
  | [] => 0
  | [high] => high.toNat * 256
  | high :: low :: rest => (read16 high low).val + total rest

def fold (value : Nat) : Word :=
  ⟨if value = 0 then 0 else (value - 1) % 65535 + 1, by
    split
    · omega
    · have := Nat.mod_lt (value - 1) (by decide : 0 < 65535)
      omega⟩

def sum (bytes : List UInt8) : Word := fold (total bytes)

def checksum (bytes : List UInt8) : Word :=
  ⟨65535 - (sum bytes).val, by have := (sum bytes).isLt; omega⟩

def valid (bytes : List UInt8) : Bool := (sum bytes).val == 65535

theorem valid_iff (bytes : List UInt8) : valid bytes = true ↔ (sum bytes).val = 65535 := by
  simp [valid]

theorem fold_small (value : Word) : fold value.val = value := by
  apply Fin.ext
  have bounded := value.isLt
  simp only [fold]
  split
  · omega
  · rw [Nat.mod_eq_of_lt (by omega)]
    omega

theorem fold_mod (value : Nat) : (fold value).val % 65535 = value % 65535 := by
  by_cases zero : value = 0
  · simp [fold, zero]
  · have positive : 0 < value := by omega
    have same : value - 1 + 1 = value := by omega
    simp only [fold, ite_eq_right zero]
    change ((value - 1) % 65535 + 1 % 65535) % 65535 = value % 65535
    rw [← Nat.add_mod, same]

theorem fold_positive (value : Nat) (positive : 0 < value) : 0 < (fold value).val := by
  have nonzero : value ≠ 0 := by omega
  simp only [fold, ite_eq_right nonzero]
  omega

theorem fold_eq_of_mod (first second : Nat) (zeros : first = 0 ↔ second = 0)
    (residue : first % 65535 = second % 65535) : fold first = fold second := by
  by_cases empty : first = 0
  · rw [empty, zeros.mp empty]
  · have other : second ≠ 0 := fun zero => empty (zeros.mpr zero)
    apply Fin.ext
    have firstPositive := fold_positive first (by omega)
    have secondPositive := fold_positive second (by omega)
    have firstBound := (fold first).isLt
    have secondBound := (fold second).isLt
    have same := (fold_mod first).trans (residue.trans (fold_mod second).symm)
    omega

theorem fold_endAround (value : Nat) : fold value = fold (value / 65536 + value % 65536) := by
  have division := Nat.mod_add_div value 65536
  apply fold_eq_of_mod
  · omega
  · have same : value = value / 65536 * 65536 + value % 65536 := by omega
    calc
      value % 65535 = (value / 65536 * 65536 + value % 65536) % 65535 := congrArg (· % 65535) same
      _ = (value / 65536 + value % 65536) % 65535 := by rw [Nat.add_mod, Nat.mul_mod]; simp [Nat.add_mod]

theorem fold_complement (value : Nat) :
    fold (value + (65535 - (fold value).val)) = (65535 : Word) := by
  apply Fin.ext
  by_cases zero : value = 0
  · subst value
    rfl
  · have residue := Nat.mod_lt (value - 1) (by decide : 0 < 65535)
    have division := Nat.mod_add_div (value - 1) 65535
    have folded : (fold value).val = (value - 1) % 65535 + 1 := by simp [fold, zero]
    have positive : 0 < value + (65535 - (fold value).val) := by omega
    have same : value + (65535 - (fold value).val) - 1 =
        65535 * ((value - 1) / 65535) + 65534 := by omega
    change (if value + (65535 - (fold value).val) = 0 then 0
      else (value + (65535 - (fold value).val) - 1) % 65535 + 1) = 65535
    rw [ite_eq_right (by omega : value + (65535 - (fold value).val) ≠ 0)]
    rw [same, Nat.add_mod]
    simp

theorem total_append_even : ∀ (first rest : List UInt8), first.length % 2 = 0 →
    total (first ++ rest) = total first + total rest
  | [], rest, _ => by simp [total]
  | [high], _, even => by simp at even
  | high :: low :: first, rest, even => by
    have tailEven : first.length % 2 = 0 := by simp only [List.length_cons] at even; omega
    simp only [List.cons_append, total]
    rw [total_append_even first rest tailEven]
    omega

theorem total_word (word : Word) : total (wordBytes word) = word.val := by
  simp only [wordBytes, total, Nat.add_zero, read16_bytes]

theorem total_insert (first rest : List UInt8) (word : Word) (even : first.length % 2 = 0) :
    total (first ++ wordBytes word ++ rest) = total (first ++ rest) + word.val := by
  rw [List.append_assoc, total_append_even first _ even, total_append_even (wordBytes word) rest (by simp),
    total_word, total_append_even first rest even]
  omega

theorem total_insert_zero (first rest : List UInt8) (even : first.length % 2 = 0) :
    total (first ++ [0, 0] ++ rest) = total (first ++ rest) := by
  have same := total_insert first rest (0 : Word) even
  simpa [wordBytes, highByte, lowByte] using same

theorem synthesize_valid (first rest : List UInt8) (even : first.length % 2 = 0) :
    valid (first ++ wordBytes (checksum (first ++ [0, 0] ++ rest)) ++ rest) = true := by
  rw [valid_iff]
  unfold sum
  rw [total_insert first rest _ even]
  simp only [checksum, sum, total_insert_zero first rest even]
  rw [fold_complement]
  rfl

theorem fold_add_period (value : Nat) (positive : 0 < value) : fold (value + 65535) = fold value := by
  apply Fin.ext
  have notZero : value ≠ 0 := by omega
  have combined : value + 65535 ≠ 0 := by omega
  have same : value + 65535 - 1 = (value - 1) + 65535 := by omega
  change (if value + 65535 = 0 then 0 else (value + 65535 - 1) % 65535 + 1) =
    (if value = 0 then 0 else (value - 1) % 65535 + 1)
  rw [ite_eq_right combined, ite_eq_right notZero, same, Nat.add_mod]
  simp

def transmittedChecksum (bytes : List UInt8) : Word :=
  if checksum bytes = 0 then 65535 else checksum bytes

theorem transmittedChecksum_nonzero (bytes : List UInt8) : transmittedChecksum bytes ≠ 0 := by
  unfold transmittedChecksum
  split
  · decide
  · assumption

theorem synthesize_nonzero_valid (first rest : List UInt8) (even : first.length % 2 = 0) :
    valid (first ++ wordBytes (transmittedChecksum (first ++ [0, 0] ++ rest)) ++ rest) = true := by
  by_cases zero : checksum (first ++ [0, 0] ++ rest) = 0
  · have folded : fold (total (first ++ rest)) = (65535 : Word) := by
      apply Fin.ext
      have same := congrArg Fin.val zero
      have bounded := (sum (first ++ [0, 0] ++ rest)).isLt
      simp only [checksum, sum, total_insert_zero first rest even] at same bounded
      change 65535 - (fold (total (first ++ rest))).val = 0 at same
      change (fold (total (first ++ rest))).val < 65536 at bounded
      change (fold (total (first ++ rest))).val = 65535
      omega
    have positive : 0 < total (first ++ rest) := by
      by_cases valueZero : total (first ++ rest) = 0
      · rw [valueZero] at folded
        exact False.elim ((by decide : fold 0 ≠ (65535 : Word)) folded)
      · omega
    rw [transmittedChecksum, ite_eq_left zero, valid_iff]
    simp only [sum, total_insert first rest _ even]
    change (fold (total (first ++ rest) + 65535)).val = 65535
    rw [fold_add_period _ positive, folded]
    rfl
  · simpa only [transmittedChecksum, ite_eq_right zero] using synthesize_valid first rest even

end Netlib.Protocol.InternetChecksum
