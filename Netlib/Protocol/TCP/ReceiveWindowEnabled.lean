import Netlib.Protocol.TCP.ReceiveWindow

/-!
# Receive-window exclusion of an old whole range

A consumed range ends at the current receive cursor.
Its positions stay outside the offered window under the stated epoch bound.
-/

namespace Netlib.Protocol.TCP.Seq

theorem distance_from_advanced (start : Seq) (length offset : Nat)
    (inside : offset < length) (bounded : length < modulus) :
    distance (start.add length) (start.add offset) = modulus - (length - offset) := by
  have origin := start.val_lt
  simp only [distance, val_add, modulus]
  unfold modulus at bounded
  omega

end Netlib.Protocol.TCP.Seq

namespace Netlib.Protocol.TCP.ReceiveWindow

theorem whole_old_range_rejected (start : Seq) (window length : Nat)
    (positive : 0 < length) (epoch : length + window ≤ Seq.modulus) :
    accepts (start.add length) window start length = false := by
  by_cases closed : window = 0
  · subst window
    exact positive_length_zero_window _ _ _ positive
  · have openWindow : 0 < window := by omega
    have bounded : length < Seq.modulus := by omega
    apply neither_endpoint _ _ _ _ openWindow positive
    · unfold Seq.InInterval
      have distance := Seq.distance_from_advanced start length 0 positive bounded
      simp only [Seq.add_zero, Nat.sub_zero] at distance
      rw [distance]
      omega
    · unfold Seq.InInterval
      rw [Seq.distance_from_advanced start length (length - 1) (by omega) bounded]
      omega

theorem whole_old_segment_rejected (segment : Segment) (window : Nat)
    (noSyn : Flags.syn segment.flags = false) (noFin : Flags.fin segment.flags = false)
    (positive : 0 < segment.payload.length) (epoch : segment.payload.length + window ≤ Seq.modulus) :
    acceptsSegment (segment.sequence.add segment.payload.length) window segment = false := by
  rw [acceptsSegment, segmentLength_no_control segment noSyn noFin]
  exact whole_old_range_rejected segment.sequence window segment.payload.length positive epoch

end Netlib.Protocol.TCP.ReceiveWindow
