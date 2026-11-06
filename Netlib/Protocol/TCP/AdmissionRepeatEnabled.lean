import Netlib.Protocol.TCP.AdmissionEnabled
import Netlib.Protocol.TCP.AdmissionRecoveryFacts

/-!
# Repeated data admission from stored coverage

The selected coverage source names an actual preceding observation.
Its repeat does not need fresh receive-window space.
-/

namespace Netlib.Protocol.TCP.Admission

theorem KnownRange.nonempty (known : KnownRange sender entry direction segment observations) :
    segment.payload ≠ [] := by
  obtain ⟨placed, accepted, _⟩ := known.placement
  exact (Theory.SparseCoverage.accept_stages _ _ _ _ _ _ accepted).2.1

theorem KnownRange.sequence_bound (known : KnownRange sender entry direction segment observations)
    (valid : sender.Valid) :
    Seq.distance sender.controlOrigin segment.sequence ≤ sender.highEnd + 1 := by
  obtain ⟨seen, _, source⟩ := known.source
  obtain ⟨_, _, _, _, _, extent, bounded, _⟩ := source
  have position : Seq.distance sender.base segment.sequence ≤ sender.highEnd := by omega
  have inside : 1 + Seq.distance sender.base segment.sequence < Seq.modulus := by
    have epoch := valid.2.1
    unfold Seq.halfSpace Seq.modulus at *
    omega
  calc
    Seq.distance sender.controlOrigin segment.sequence =
        Seq.distance sender.controlOrigin
          ((sender.controlOrigin.add 1).add (Seq.distance sender.base segment.sequence)) := by
      rw [sender.controlOrigin_add, Seq.add_distance]
    _ = 1 + Seq.distance sender.base segment.sequence := by
      rw [Seq.add_add, Seq.distance_add, Nat.mod_eq_of_lt inside]
    _ ≤ sender.highEnd + 1 := by omega

structure RepeatedReady (session : Session) (direction : Direction) (segment : Segment)
    (observations : List Seen) : Prop where
  profile : DataProfile segment
  known : KnownRange (session.sender direction) session.entry direction segment observations
  mss : segment.payload.length ≤ (session.peerMSS direction).limit
  acknowledgment : ackOffset (session.peer direction) segment ≤ (session.peer direction).observed
  stale : (session.peer direction).acknowledged ≤ ackOffset (session.peer direction) segment + 65535

instance (session : Session) (direction : Direction) (segment : Segment) (observations : List Seen) :
    Decidable (RepeatedReady session direction segment observations) :=
  decidable_of_iff (DataProfile segment ∧
    KnownRange (session.sender direction) session.entry direction segment observations ∧
    segment.payload.length ≤ (session.peerMSS direction).limit ∧
    ackOffset (session.peer direction) segment ≤ (session.peer direction).observed ∧
    (session.peer direction).acknowledged ≤ ackOffset (session.peer direction) segment + 65535) (by
      constructor
      · rintro ⟨profile, known, mss, acknowledgment, stale⟩
        exact ⟨profile, known, mss, acknowledgment, stale⟩
      · intro ready
        exact ⟨ready.profile, ready.known, ready.mss, ready.acknowledgment, ready.stale⟩)

theorem RepeatedReady.repeated_allowed (ready : RepeatedReady session direction segment observations) :
    RepeatedAllowed (session.sender direction) (session.peer direction) session.entry direction
      segment (session.peerMSS direction) observations :=
  ⟨ready.profile, ready.known.nonempty, ready.known.sequence_bound (session.sender_valid direction),
    ready.known, ready.mss, ready.acknowledgment, ready.stale,
    acknowledgedLane_valid _ _ (session.peer_valid direction) ready.acknowledgment⟩

theorem RepeatedReady.not_fresh (ready : RepeatedReady session direction segment observations) :
    ¬DataAllowed (session.sender direction) (session.peer direction) segment
      (session.peerMSS direction) observations.length := ready.known.not_fresh

theorem RepeatedReady.source (ready : RepeatedReady session direction segment observations) :
    ∃ seen ∈ observations, RangeFrom (session.sender direction) session.entry direction segment seen :=
  ready.known.source

theorem RepeatedReady.allowed (session : Session) (attachment : ConntrackLifecycle.Attachment)
    (segment : Segment) (observations : List Seen) (entry : attachment.entry = session.entry)
    (existing : attachment.fresh = false)
    (ready : RepeatedReady session attachment.direction segment observations) :
    Allowed (.data session) attachment segment observations := by
  refine ⟨entry, existing, ?_⟩
  have repeated := ready.repeated_allowed
  cases direction : attachment.direction <;>
    exact .inr (by simpa only [Session.sender, Session.peer, Session.peerMSS, direction] using repeated)

end Netlib.Protocol.TCP.Admission
