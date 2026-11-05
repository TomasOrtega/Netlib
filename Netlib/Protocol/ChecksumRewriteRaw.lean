import Netlib.Protocol.ChecksumRewrite

/-!
# Incremental checksums without an omission marker

Raw checksum zero participates in one's-complement arithmetic.
Updates preserve the residue of invalid checksums instead of repairing them.
-/

namespace Netlib.Protocol.ChecksumRewriteRaw

open InternetChecksum

def update (checksum : Word) (removed added : Nat) : Word :=
  fold (checksum.val + removed % 65535 + 65535 - added % 65535)

theorem update_positive (checksum : Word) (removed added : Nat) :
    0 < (update checksum removed added).val := by
  have bounded := Nat.mod_lt added (by decide : 0 < 65535)
  exact fold_positive _ (by omega)

theorem update_residue (checksum : Word) (removed added : Nat) :
    ((update checksum removed added).val + added) % 65535 =
      (checksum.val + removed) % 65535 := by
  have removedBound := Nat.mod_lt removed (by decide : 0 < 65535)
  have addedBound := Nat.mod_lt added (by decide : 0 < 65535)
  have residue := fold_mod (checksum.val + removed % 65535 + 65535 - added % 65535)
  change (fold (checksum.val + removed % 65535 + 65535 - added % 65535)).val % 65535 = _ at residue
  unfold update
  omega

theorem update_inverse_mod (checksum : Word) (removed added : Nat) :
    (update (update checksum removed added) added removed).val % 65535 = checksum.val % 65535 := by
  have forward := update_residue checksum removed added
  have reverse := update_residue (update checksum removed added) added removed
  omega

theorem update_inverse (checksum : Word) (removed added : Nat) (present : checksum ≠ 0) :
    update (update checksum removed added) added removed = checksum := by
  have residue := update_inverse_mod checksum removed added
  have positive := update_positive (update checksum removed added) added removed
  have original : 0 < checksum.val := by
    have : checksum.val ≠ 0 := fun zero => present (Fin.ext zero)
    omega
  have := (update (update checksum removed added) added removed).isLt
  have := checksum.isLt
  apply Fin.ext
  omega

theorem fold_valid_iff (value : Nat) (positive : 0 < value) :
    fold value = (65535 : Word) ↔ value % 65535 = 0 := by
  constructor
  · intro valid
    have residue := fold_mod value
    rw [valid] at residue
    exact residue.symm
  · intro residue
    have same := fold_eq_of_mod value 65535 (by omega) (by simpa using residue)
    exact same.trans (by decide)

theorem update_valid_iff (checksum : Word) (oldTotal newTotal removed added : Nat)
    (oldPositive : 0 < oldTotal) (newPositive : 0 < newTotal)
    (changed : removed + newTotal = added + oldTotal) :
    fold (newTotal + (update checksum removed added).val) = (65535 : Word) ↔
      fold (oldTotal + checksum.val) = (65535 : Word) := by
  rw [fold_valid_iff _ (by omega), fold_valid_iff _ (by omega)]
  have delta := update_residue checksum removed added
  omega

theorem update_valid_bytes_iff (checksum : Word)
    (oldPrefix oldSuffix newPrefix newSuffix : List UInt8) (removed added : Nat)
    (oldEven : oldPrefix.length % 2 = 0) (newEven : newPrefix.length % 2 = 0)
    (oldPositive : 0 < total (oldPrefix ++ oldSuffix))
    (newPositive : 0 < total (newPrefix ++ newSuffix))
    (changed : removed + total (newPrefix ++ newSuffix) = added + total (oldPrefix ++ oldSuffix)) :
    valid (newPrefix ++ wordBytes (update checksum removed added) ++ newSuffix) = true ↔
      valid (oldPrefix ++ wordBytes checksum ++ oldSuffix) = true := by
  rw [valid_iff, valid_iff]
  simp only [sum, total_insert oldPrefix oldSuffix checksum oldEven,
    total_insert newPrefix newSuffix (update checksum removed added) newEven]
  change (fold (total (newPrefix ++ newSuffix) + (update checksum removed added).val)).val =
      (65535 : Word).val ↔
    (fold (total (oldPrefix ++ oldSuffix) + checksum.val)).val = (65535 : Word).val
  rw [Fin.val_inj, Fin.val_inj]
  exact update_valid_iff checksum _ _ removed added oldPositive newPositive changed

end Netlib.Protocol.ChecksumRewriteRaw
