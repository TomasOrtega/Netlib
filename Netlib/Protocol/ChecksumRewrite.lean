import Netlib.Protocol.UDP

/-!
# Incremental Internet checksums

An update replaces aligned words using their ordinary natural-number totals.
Zero preserves UDP checksum omission; a present checksum retains the negative-zero representation.
-/

namespace Netlib.Protocol.ChecksumRewrite

open InternetChecksum

def update (checksum : Word) (removed added : Nat) : Word :=
  if checksum = 0 then 0
  else fold (checksum.val + removed % 65535 + 65535 - added % 65535)

@[simp] theorem update_zero (removed added : Nat) : update 0 removed added = 0 := by
  simp [update]

theorem update_positive (checksum : Word) (removed added : Nat) (present : checksum ≠ 0) :
    0 < (update checksum removed added).val := by
  have bounded := Nat.mod_lt added (by decide : 0 < 65535)
  rw [update, ite_eq_right present]
  exact fold_positive _ (by omega)

theorem update_nonzero (checksum : Word) (removed added : Nat) (present : checksum ≠ 0) :
    update checksum removed added ≠ 0 := by
  have positive := update_positive checksum removed added present
  intro zero
  rw [zero] at positive
  contradiction

@[simp] theorem update_omitted_iff (checksum : Word) (removed added : Nat) :
    update checksum removed added = 0 ↔ checksum = 0 := by
  constructor
  · intro zero
    by_cases present : checksum = 0
    · exact present
    · exact False.elim (update_nonzero checksum removed added present zero)
  · rintro rfl
    exact update_zero removed added

theorem update_residue (checksum : Word) (removed added : Nat) (present : checksum ≠ 0) :
    ((update checksum removed added).val + added) % 65535 =
      (checksum.val + removed) % 65535 := by
  have removedBound := Nat.mod_lt removed (by decide : 0 < 65535)
  have addedBound := Nat.mod_lt added (by decide : 0 < 65535)
  have residue := fold_mod (checksum.val + removed % 65535 + 65535 - added % 65535)
  rw [update, ite_eq_right present]
  omega

private theorem present_eq_of_residue (first second : Word) (firstPresent : first ≠ 0)
    (secondPresent : second ≠ 0) (same : first.val % 65535 = second.val % 65535) :
    first = second := by
  have firstPositive : 0 < first.val := by
    have : first.val ≠ 0 := fun zero => firstPresent (Fin.ext zero)
    omega
  have secondPositive : 0 < second.val := by
    have : second.val ≠ 0 := fun zero => secondPresent (Fin.ext zero)
    omega
  have := first.isLt
  have := second.isLt
  apply Fin.ext
  omega

@[simp] theorem update_identity (checksum : Word) (words : Nat) :
    update checksum words words = checksum := by
  by_cases omitted : checksum = 0
  · simp [omitted]
  · apply present_eq_of_residue _ _ (update_nonzero checksum words words omitted) omitted
    have same := update_residue checksum words words omitted
    omega

@[simp] theorem update_inverse (checksum : Word) (removed added : Nat) :
    update (update checksum removed added) added removed = checksum := by
  by_cases omitted : checksum = 0
  · simp [omitted]
  · have present := update_nonzero checksum removed added omitted
    apply present_eq_of_residue _ _ (update_nonzero _ added removed present) omitted
    have forward := update_residue checksum removed added omitted
    have reverse := update_residue (update checksum removed added) added removed present
    omega

theorem update_compose (checksum : Word) (removed added moreRemoved moreAdded : Nat) :
    update (update checksum removed added) moreRemoved moreAdded =
      update checksum (removed + moreRemoved) (added + moreAdded) := by
  by_cases omitted : checksum = 0
  · simp [omitted]
  · have present := update_nonzero checksum removed added omitted
    apply present_eq_of_residue _ _ (update_nonzero _ moreRemoved moreAdded present)
      (update_nonzero checksum (removed + moreRemoved) (added + moreAdded) omitted)
    have first := update_residue checksum removed added omitted
    have second := update_residue (update checksum removed added) moreRemoved moreAdded present
    have combined := update_residue checksum (removed + moreRemoved) (added + moreAdded) omitted
    omega

theorem update_valid (checksum : Word) (oldTotal newTotal removed added : Nat)
    (present : checksum ≠ 0) (changed : removed + newTotal = added + oldTotal)
    (valid : fold (oldTotal + checksum.val) = (65535 : Word)) :
    fold (newTotal + (update checksum removed added).val) = (65535 : Word) := by
  have positive := update_positive checksum removed added present
  have oldResidue := fold_mod (oldTotal + checksum.val)
  rw [valid] at oldResidue
  have changedResidue := update_residue checksum removed added present
  have residue : (newTotal + (update checksum removed added).val) % 65535 = 65535 % 65535 := by
    change 0 = (oldTotal + checksum.val) % 65535 at oldResidue
    omega
  have same := fold_eq_of_mod (newTotal + (update checksum removed added).val) 65535
    (by omega) residue
  exact same.trans (by decide)

theorem update_valid_bytes (checksum : Word) (oldPrefix newPrefix payload : List UInt8)
    (removed added : Nat) (present : checksum ≠ 0)
    (oldEven : oldPrefix.length % 2 = 0) (newEven : newPrefix.length % 2 = 0)
    (changed : removed + total (newPrefix ++ payload) = added + total (oldPrefix ++ payload))
    (valid : InternetChecksum.valid (oldPrefix ++ wordBytes checksum ++ payload) = true) :
    InternetChecksum.valid (newPrefix ++ wordBytes (update checksum removed added) ++ payload) = true := by
  rw [valid_iff] at valid ⊢
  simp only [sum, total_insert oldPrefix payload checksum oldEven] at valid
  simp only [sum, total_insert newPrefix payload (update checksum removed added) newEven]
  exact congrArg Fin.val (update_valid checksum _ _ removed added present changed (Fin.ext valid))

def udpTupleTotal (source destination : Netlib.Packet.Address) (sourcePort destinationPort : Word) : Nat :=
  total (IPv4.addressBytes source ++ IPv4.addressBytes destination ++
    wordBytes sourcePort ++ wordBytes destinationPort)

theorem udpTupleTotal_eq (source destination : Netlib.Packet.Address) (sourcePort destinationPort : Word) :
    udpTupleTotal source destination sourcePort destinationPort =
      total (IPv4.addressBytes source) + total (IPv4.addressBytes destination) + sourcePort.val + destinationPort.val := by
  simp only [udpTupleTotal, List.append_assoc]
  rw [total_append_even (IPv4.addressBytes source) _ (by simp [IPv4.addressBytes]),
    total_append_even (IPv4.addressBytes destination) _ (by simp [IPv4.addressBytes]),
    total_append_even (wordBytes sourcePort) _ (by simp), total_word, total_word]
  omega

theorem udp_checksum_total (source destination : Netlib.Packet.Address) (datagram : UDP.Datagram) :
    total (UDP.checksumBytes source destination datagram) =
      udpTupleTotal source destination datagram.sourcePort datagram.destinationPort +
        17 + 2 * datagram.lengthWord.val + datagram.checksum.val + total datagram.payload := by
  simp only [UDP.checksumBytes, UDP.checksumPrefix, UDP.pseudoHeader, List.append_assoc]
  rw [total_append_even (IPv4.addressBytes source) _ (by simp [IPv4.addressBytes]),
    total_append_even (IPv4.addressBytes destination) _ (by simp [IPv4.addressBytes]),
    total_append_even [0, 17] _ (by decide),
    total_append_even (wordBytes datagram.lengthWord) _ (by simp),
    total_append_even (wordBytes datagram.sourcePort) _ (by simp),
    total_append_even (wordBytes datagram.destinationPort) _ (by simp),
    total_append_even (wordBytes datagram.lengthWord) _ (by simp),
    total_append_even (wordBytes datagram.checksum) _ (by simp)]
  simp only [total_word, total, read16]
  change total (IPv4.addressBytes source) + (total (IPv4.addressBytes destination) +
    (17 + (datagram.lengthWord.val + (datagram.sourcePort.val + (datagram.destinationPort.val +
      (datagram.lengthWord.val + (datagram.checksum.val + total datagram.payload))))))) = _
  rw [udpTupleTotal_eq]
  omega

theorem udp_checksum_total_positive (source destination : Netlib.Packet.Address) (datagram : UDP.Datagram) :
    0 < total (UDP.checksumBytes source destination datagram) := by
  rw [udp_checksum_total]
  omega

theorem update_udp_valid (oldSource oldDestination newSource newDestination : Netlib.Packet.Address)
    (datagram : UDP.Datagram) (newSourcePort newDestinationPort : Word)
    (present : datagram.checksum ≠ 0)
    (valid : InternetChecksum.valid (UDP.checksumBytes oldSource oldDestination datagram) = true) :
    InternetChecksum.valid (UDP.checksumBytes newSource newDestination
      { datagram with
        sourcePort := newSourcePort
        destinationPort := newDestinationPort
        checksum := (update datagram.checksum
          (udpTupleTotal oldSource oldDestination datagram.sourcePort datagram.destinationPort)
          (udpTupleTotal newSource newDestination newSourcePort newDestinationPort)) }) = true := by
  rw [valid_iff] at valid ⊢
  simp only [sum, udp_checksum_total] at valid ⊢
  let oldTotal := udpTupleTotal oldSource oldDestination datagram.sourcePort datagram.destinationPort +
    17 + 2 * datagram.lengthWord.val + total datagram.payload
  let newTotal := udpTupleTotal newSource newDestination newSourcePort newDestinationPort +
    17 + 2 * datagram.lengthWord.val + total datagram.payload
  have checked : fold (oldTotal + datagram.checksum.val) = (65535 : Word) := by
    apply Fin.ext
    change (fold (oldTotal + datagram.checksum.val)).val = 65535
    simpa only [oldTotal, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using valid
  have changed : udpTupleTotal oldSource oldDestination datagram.sourcePort datagram.destinationPort + newTotal =
      udpTupleTotal newSource newDestination newSourcePort newDestinationPort + oldTotal := by
    dsimp only [oldTotal, newTotal]
    omega
  have result := update_valid datagram.checksum oldTotal newTotal _ _ present changed checked
  have resultVal := congrArg Fin.val result
  change _ = (65535 : Nat) at resultVal
  simpa only [newTotal, UDP.Datagram.lengthWord, UDP.Datagram.wireLength, Nat.add_assoc,
    Nat.add_comm, Nat.add_left_comm] using resultVal

theorem update_udp_accepts (oldSource oldDestination newSource newDestination : Netlib.Packet.Address)
    (datagram : UDP.Datagram) (newSourcePort newDestinationPort : Word)
    (accepted : UDP.checksumAccepts oldSource oldDestination datagram = true) :
    UDP.checksumAccepts newSource newDestination
      { datagram with
        sourcePort := newSourcePort
        destinationPort := newDestinationPort
        checksum := (update datagram.checksum
          (udpTupleTotal oldSource oldDestination datagram.sourcePort datagram.destinationPort)
          (udpTupleTotal newSource newDestination newSourcePort newDestinationPort)) } = true := by
  by_cases omitted : datagram.checksum = 0
  · simp [UDP.checksumAccepts, omitted]
  · have valid : InternetChecksum.valid (UDP.checksumBytes oldSource oldDestination datagram) = true := by
      simpa [UDP.checksumAccepts, omitted] using accepted
    have updated := update_udp_valid oldSource oldDestination newSource newDestination datagram
      newSourcePort newDestinationPort omitted valid
    simp [UDP.checksumAccepts, updated]

end Netlib.Protocol.ChecksumRewrite
