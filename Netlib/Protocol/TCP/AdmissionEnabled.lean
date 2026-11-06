import Netlib.Protocol.TCP.Admission

/-!
# Data and ACK admission from preceding lane geometry

These conditions concern old coverage, sequence positions, and offered windows.
Placement success and validity of the next lane are derived results.
-/

namespace Netlib.Protocol.TCP.Admission

def Session.sender (session : Session) : Direction → Lane
  | .original => session.original
  | .reply => session.reply

def Session.peer (session : Session) : Direction → Lane
  | .original => session.reply
  | .reply => session.original

theorem Session.sender_valid (session : Session) (direction : Direction) : (session.sender direction).Valid := by
  cases direction
  · exact session.originalValid
  · exact session.replyValid

theorem Session.peer_valid (session : Session) (direction : Direction) : (session.peer direction).Valid := by
  cases direction
  · exact session.replyValid
  · exact session.originalValid

structure FreshReady (session : Session) (direction : Direction) (segment : Segment) : Prop where
  profile : DataProfile segment
  nonempty : segment.payload ≠ []
  mss : segment.payload.length ≤ (session.peerMSS direction).limit
  epoch : Seq.distance (session.sender direction).base segment.sequence + segment.payload.length + 2 < Seq.halfSpace
  left : (session.sender direction).acknowledged ≤ Seq.distance (session.sender direction).base segment.sequence
  right : Seq.distance (session.sender direction).base segment.sequence + segment.payload.length ≤
    (session.sender direction).acknowledged + (session.sender direction).peerWindow.val
  disjoint : ∀ run ∈ (session.sender direction).coverage.runs,
    Seq.distance (session.sender direction).base segment.sequence + segment.payload.length ≤ run.position ∨
      run.limit ≤ Seq.distance (session.sender direction).base segment.sequence
  acknowledgment : ackOffset (session.peer direction) segment ≤ (session.peer direction).observed
  stale : (session.peer direction).acknowledged ≤ ackOffset (session.peer direction) segment + 65535

structure AckReady (session : Session) (direction : Direction) (segment : Segment) : Prop where
  profile : DataProfile segment
  empty : segment.payload = []
  sequence : Seq.distance (session.sender direction).base segment.sequence ≤ (session.sender direction).highEnd
  acknowledgment : ackOffset (session.peer direction) segment ≤ (session.peer direction).observed
  stale : (session.peer direction).acknowledged ≤ ackOffset (session.peer direction) segment + 65535

instance (session : Session) (direction : Direction) (segment : Segment) :
    Decidable (FreshReady session direction segment) :=
  decidable_of_iff (DataProfile segment ∧ segment.payload ≠ [] ∧
    segment.payload.length ≤ (session.peerMSS direction).limit ∧
    Seq.distance (session.sender direction).base segment.sequence + segment.payload.length + 2 < Seq.halfSpace ∧
    (session.sender direction).acknowledged ≤ Seq.distance (session.sender direction).base segment.sequence ∧
    Seq.distance (session.sender direction).base segment.sequence + segment.payload.length ≤
      (session.sender direction).acknowledged + (session.sender direction).peerWindow.val ∧
    (∀ run ∈ (session.sender direction).coverage.runs,
      Seq.distance (session.sender direction).base segment.sequence + segment.payload.length ≤ run.position ∨
        run.limit ≤ Seq.distance (session.sender direction).base segment.sequence) ∧
    ackOffset (session.peer direction) segment ≤ (session.peer direction).observed ∧
    (session.peer direction).acknowledged ≤ ackOffset (session.peer direction) segment + 65535) (by
      constructor
      · rintro ⟨profile, nonempty, mss, epoch, left, right, disjoint, acknowledgment, stale⟩
        exact ⟨profile, nonempty, mss, epoch, left, right, disjoint, acknowledgment, stale⟩
      · intro ready
        exact ⟨ready.profile, ready.nonempty, ready.mss, ready.epoch, ready.left, ready.right,
          ready.disjoint, ready.acknowledgment, ready.stale⟩)

instance (session : Session) (direction : Direction) (segment : Segment) :
    Decidable (AckReady session direction segment) :=
  decidable_of_iff (DataProfile segment ∧ segment.payload = [] ∧
    Seq.distance (session.sender direction).base segment.sequence ≤ (session.sender direction).highEnd ∧
    ackOffset (session.peer direction) segment ≤ (session.peer direction).observed ∧
    (session.peer direction).acknowledged ≤ ackOffset (session.peer direction) segment + 65535) (by
      constructor
      · rintro ⟨profile, empty, sequence, acknowledgment, stale⟩
        exact ⟨profile, empty, sequence, acknowledgment, stale⟩
      · intro ready
        exact ⟨ready.profile, ready.empty, ready.sequence, ready.acknowledgment, ready.stale⟩)

theorem sentLane_empty (sender : Lane) (segment : Segment) (source : Nat)
    (valid : sender.Valid) (empty : segment.payload = []) : sentLane sender segment source = sender := by
  simp only [sentLane, placement, Theory.SparseCoverage.accept, valid.2.2.2, not_true_eq_false,
    ite_false, empty, ite_true]

theorem ack_data_allowed (sender peer : Lane) (segment : Segment) (peerMSS : MSS.Offer) (source : Nat)
    (senderValid : sender.Valid) (peerValid : peer.Valid)
    (profile : DataProfile segment) (empty : segment.payload = [])
    (sequence : Seq.distance sender.base segment.sequence ≤ sender.highEnd)
    (acknowledgment : ackOffset peer segment ≤ peer.observed)
    (stale : peer.acknowledged ≤ ackOffset peer segment + 65535) :
    DataAllowed sender peer segment peerMSS source := by
  refine ⟨profile, ?_, ?_, acknowledgment, stale, .inl empty, ?_, acknowledgedLane_valid peer segment peerValid acknowledgment⟩
  · simpa only [FreshSequence, empty, ite_true] using sequence
  · simp only [empty, List.length_nil, Nat.zero_le]
  · rw [sentLane_empty sender segment source senderValid empty]
    exact senderValid

theorem FreshReady.allowed (ready : FreshReady session direction segment) (source : Nat) :
    DataAllowed (session.sender direction) (session.peer direction) segment (session.peerMSS direction) source :=
  fresh_data_allowed _ _ _ _ source (session.sender_valid direction) (session.peer_valid direction)
    ready.profile ready.nonempty ready.mss ready.epoch ready.left ready.right ready.disjoint ready.acknowledgment ready.stale

theorem AckReady.allowed (ready : AckReady session direction segment) (source : Nat) :
    DataAllowed (session.sender direction) (session.peer direction) segment (session.peerMSS direction) source :=
  ack_data_allowed _ _ _ _ source (session.sender_valid direction) (session.peer_valid direction)
    ready.profile ready.empty ready.sequence ready.acknowledgment ready.stale

def DataReady (session : Session) (direction : Direction) (segment : Segment) : Prop :=
  FreshReady session direction segment ∨ AckReady session direction segment

instance (session : Session) (direction : Direction) (segment : Segment) :
    Decidable (DataReady session direction segment) := by
  unfold DataReady
  infer_instance

theorem DataReady.allowed (session : Session) (attachment : ConntrackLifecycle.Attachment) (segment : Segment)
    (observations : List Seen) (entry : attachment.entry = session.entry) (existing : attachment.fresh = false)
    (ready : DataReady session attachment.direction segment) : Allowed (.data session) attachment segment observations := by
  have admitted : DataAllowed (session.sender attachment.direction) (session.peer attachment.direction)
      segment (session.peerMSS attachment.direction) observations.length := by
    rcases ready with fresh | acknowledgment
    · exact fresh.allowed _
    · exact acknowledgment.allowed _
  refine ⟨entry, existing, ?_⟩
  cases direction : attachment.direction <;> exact .inl (by simpa [Session.sender, Session.peer, Session.peerMSS, direction] using admitted)

end Netlib.Protocol.TCP.Admission
