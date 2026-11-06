import Netlib.Protocol.ConntrackLifecycle
import Netlib.Protocol.TCP.EstablishedReceive
import Netlib.Protocol.TCP.MSS
import Netlib.Theory.SparseCoverage

/-!
# A selected TCP admission history at a gateway

The gate starts without a connection history.
It learns control positions from checked SYN and SYN,ACK segments.
Data positions and ACK positions remain inside the observed finite byte epoch.
The selected lifecycle attachment supplies the exact NAT entry and direction.
This model does not establish Linux transport-tracker refinement.
Accepted ingress updates precede routing and filtering.
Commit retains those updates only with the actual confirmed lifecycle entry.
-/

namespace Netlib.Protocol.TCP.Admission

abbrev Input := EstablishedReceive.Input
abbrev Direction := FlowNAT.Direction
abbrev Entry := NetfilterNAT.Entry

namespace Coverage
export Theory.SparseCoverage (State Run Result Stop accept initial)
end Coverage

structure Lane where
  base : Seq
  coverage : Coverage.State Nat
  acknowledged : Nat
  peerWindow : InternetChecksum.Word
  windowSequence : Seq
  windowAcknowledgment : Seq
  deriving Repr, BEq, DecidableEq

def Lane.observed (lane : Lane) : Nat := lane.coverage.frontier
def Lane.highEnd (lane : Lane) : Nat := lane.coverage.highEnd
def Lane.uniqueBytes (lane : Lane) : Nat := lane.coverage.count
def Lane.next (lane : Lane) : Seq := lane.base.add lane.observed
def Lane.highNext (lane : Lane) : Seq := lane.base.add lane.highEnd
def Lane.una (lane : Lane) : Seq := lane.base.add lane.acknowledged
def Lane.outstanding (lane : Lane) : Nat := lane.highEnd - lane.acknowledged

def coverageBound : Nat := Seq.halfSpace - 3

def Lane.Valid (lane : Lane) : Prop :=
  lane.acknowledged ≤ lane.observed ∧ lane.highEnd + 2 < Seq.halfSpace ∧
    lane.outstanding ≤ 65535 ∧ lane.coverage.Valid coverageBound

instance (lane : Lane) : Decidable lane.Valid := by unfold Lane.Valid; infer_instance

def Lane.initial (base : Seq) (window : InternetChecksum.Word) (sequence acknowledgment : Seq) : Lane :=
  ⟨base, Coverage.initial, 0, window, sequence, acknowledgment⟩

theorem Lane.initial_valid (base : Seq) (window : InternetChecksum.Word) (sequence acknowledgment : Seq) :
    (Lane.initial base window sequence acknowledgment).Valid := by
  change 0 ≤ 0 ∧ 0 + 2 < Seq.halfSpace ∧ 0 - 0 ≤ 65535 ∧ Coverage.initial.Valid coverageBound
  exact ⟨by decide, by decide, by decide, Theory.SparseCoverage.initial_valid _⟩

def Lane.controlOrigin (lane : Lane) : Seq := lane.base.add (Seq.modulus - 1)

theorem control_inverse (iss : Seq) : (iss.add 1).add (Seq.modulus - 1) = iss := by
  rw [Seq.add_add]
  have total : 1 + (Seq.modulus - 1) = Seq.modulus := by decide
  rw [total, Seq.add_modulus]

theorem Lane.controlOrigin_add (lane : Lane) : lane.controlOrigin.add 1 = lane.base := by
  rw [Lane.controlOrigin, Seq.add_add]
  have total : Seq.modulus - 1 + 1 = Seq.modulus := by decide
  rw [total, Seq.add_modulus]

theorem Lane.control_distance (lane : Lane) (valid : lane.Valid) :
    Seq.distance lane.controlOrigin lane.next = lane.observed + 1 := by
  have bound : 1 + lane.observed < Seq.modulus := by
    have epoch := valid.2.1
    have covered : lane.observed ≤ lane.highEnd := lane.coverage.frontier_le_highEnd
    unfold Seq.halfSpace Seq.modulus at *
    omega
  change Seq.distance lane.controlOrigin (lane.base.add lane.observed) = _
  calc
    _ = Seq.distance lane.controlOrigin ((lane.controlOrigin.add 1).add lane.observed) := by
      rw [lane.controlOrigin_add]
    _ = _ := by
      rw [Seq.add_add, Seq.distance_add, Nat.mod_eq_of_lt bound]
      omega

def WindowHistory (lane peer : Lane) : Prop :=
  Seq.distance peer.controlOrigin lane.windowSequence ≤ peer.highEnd + 1 ∧
    Seq.distance lane.base lane.windowAcknowledgment ≤ lane.observed

structure Session where
  entry : Entry
  original : Lane
  reply : Lane
  originalValid : original.Valid
  replyValid : reply.Valid
  originalHistory : WindowHistory original reply
  replyHistory : WindowHistory reply original
  clientMSS : MSS.Offer := .absent
  serverMSS : MSS.Offer := .absent

def Session.peerMSS (session : Session) : Direction → MSS.Offer
  | .original => session.serverMSS
  | .reply => session.clientMSS

inductive Phase where
  | empty
  | syn (entry : Entry) (clientISS : Seq) (clientWindow : InternetChecksum.Word) (clientMSS : MSS.Offer)
  | synAck (entry : Entry) (clientISS : Seq) (clientWindow : InternetChecksum.Word)
      (serverISS : Seq) (serverWindow : InternetChecksum.Word) (clientMSS serverMSS : MSS.Offer)
  | data (session : Session)

def Phase.entry : Phase → Option Entry
  | .empty => none
  | .syn entry _ _ _ | .synAck entry _ _ _ _ _ _ => some entry
  | .data session => some session.entry

def Phase.name : Phase → String
  | .empty => "empty" | .syn .. => "syn" | .synAck .. => "synAck" | .data _ => "data"

structure Seen where
  zone : Nat
  bytes : List UInt8
  header : Packet.Header
  segment : Segment
  attachment : ConntrackLifecycle.Attachment
  deriving Repr, BEq, DecidableEq

structure State where
  phase : Phase := .empty
  observations : List Seen := []

def State.initial : State := {}

def observe (input : Input) (lifecycle : ConntrackLifecycle.Input)
    (prepared : ConntrackLifecycle.Prepared lifecycle) : Seen :=
  ⟨lifecycle.zone, input.bytes, input.packet.header, input.packet.segment, prepared.attachment⟩

def Startup (segment : Segment) (flags : UInt8) : Prop :=
  segment.flags = flags ∧
    (if flags = 16 then segment.options = [] else (MSS.readStartup segment.options).isOk = true) ∧ segment.payload = []

instance (segment : Segment) (flags : UInt8) : Decidable (Startup segment flags) := by
  unfold Startup
  infer_instance

def DataProfile (segment : Segment) : Prop :=
  (segment.flags = 16 ∨ segment.flags = 24) ∧ segment.options = []

instance (segment : Segment) : Decidable (DataProfile segment) := by unfold DataProfile; infer_instance

def ackOffset (peer : Lane) (segment : Segment) : Nat := Seq.distance peer.base segment.acknowledgment

def windowFresh (peer : Lane) (segment : Segment) : Bool :=
  Seq.before peer.windowSequence segment.sequence ||
    (decide (peer.windowSequence = segment.sequence) &&
      (decide (peer.windowAcknowledgment = segment.acknowledgment) ||
        Seq.before peer.windowAcknowledgment segment.acknowledgment))

def windowEligible (peer : Lane) (segment : Segment) : Bool :=
  decide (peer.acknowledged ≤ ackOffset peer segment) && windowFresh peer segment

def placement (sender : Lane) (segment : Segment) (source : Nat) : Except Coverage.Stop (Coverage.Result Nat) :=
  Coverage.accept sender.coverage (Seq.distance sender.base segment.sequence) segment.payload source coverageBound

def sentLane (sender : Lane) (segment : Segment) (source : Nat := 0) : Lane :=
  match placement sender segment source with
  | .ok result => { sender with coverage := result.state }
  | .error _ => sender

def FreshSequence (sender : Lane) (segment : Segment) (source : Nat) : Prop :=
  if segment.payload = [] then Seq.distance sender.base segment.sequence ≤ sender.highEnd
  else match placement sender segment source with
    | .ok result => result.novel = segment.payload.length
    | .error _ => False

instance (sender : Lane) (segment : Segment) (source : Nat) : Decidable (FreshSequence sender segment source) := by
  unfold FreshSequence
  split <;> first | infer_instance | (split <;> infer_instance)

def acknowledgedLane (peer : Lane) (segment : Segment) : Lane :=
  let after := { peer with acknowledged := max peer.acknowledged (ackOffset peer segment) }
  if windowEligible peer segment then
    { after with
      peerWindow := segment.window
      windowSequence := segment.sequence
      windowAcknowledgment := segment.acknowledgment }
  else after

@[simp] theorem acknowledgedLane_base (peer : Lane) (segment : Segment) :
    (acknowledgedLane peer segment).base = peer.base := by
  unfold acknowledgedLane
  split <;> rfl

@[simp] theorem acknowledgedLane_observed (peer : Lane) (segment : Segment) :
    (acknowledgedLane peer segment).observed = peer.observed := by
  unfold acknowledgedLane
  split <;> rfl

@[simp] theorem acknowledgedLane_coverage (peer : Lane) (segment : Segment) :
    (acknowledgedLane peer segment).coverage = peer.coverage := by
  unfold acknowledgedLane
  split <;> rfl

@[simp] theorem acknowledgedLane_highEnd (peer : Lane) (segment : Segment) :
    (acknowledgedLane peer segment).highEnd = peer.highEnd := by
  simp only [Lane.highEnd, acknowledgedLane_coverage]

@[simp] theorem sentLane_base (sender : Lane) (segment : Segment) (source : Nat) :
    (sentLane sender segment source).base = sender.base := by
  unfold sentLane
  split <;> rfl

@[simp] theorem sentLane_windowSequence (sender : Lane) (segment : Segment) (source : Nat) :
    (sentLane sender segment source).windowSequence = sender.windowSequence := by
  unfold sentLane
  split <;> rfl

@[simp] theorem sentLane_windowAcknowledgment (sender : Lane) (segment : Segment) (source : Nat) :
    (sentLane sender segment source).windowAcknowledgment = sender.windowAcknowledgment := by
  unfold sentLane
  split <;> rfl

theorem sentLane_monotone (sender : Lane) (segment : Segment) (source : Nat) :
    sender.observed ≤ (sentLane sender segment source).observed ∧
      sender.highEnd ≤ (sentLane sender segment source).highEnd := by
  unfold sentLane
  split
  · rename_i result accepted
    exact ⟨Theory.SparseCoverage.accept_frontier_mono _ _ _ _ _ _ accepted,
      Theory.SparseCoverage.accept_highEnd_mono _ _ _ _ _ _ accepted⟩
  · exact ⟨Nat.le_refl _, Nat.le_refl _⟩

theorem sent_history (sender peer : Lane) (segment : Segment) (source : Nat) (history : WindowHistory sender peer) :
    WindowHistory (sentLane sender segment source) (acknowledgedLane peer segment) := by
  have monotone := (sentLane_monotone sender segment source).1
  simpa only [WindowHistory, Lane.controlOrigin, sentLane_base, acknowledgedLane_base,
    acknowledgedLane_highEnd, sentLane_windowSequence, sentLane_windowAcknowledgment] using (show Seq.distance peer.controlOrigin sender.windowSequence ≤ peer.highEnd + 1 ∧
      Seq.distance sender.base sender.windowAcknowledgment ≤ (sentLane sender segment source).observed from
      ⟨history.1, Nat.le_trans history.2 monotone⟩)

def DataAllowed (sender peer : Lane) (segment : Segment) (peerMSS : MSS.Offer := .absent) (source : Nat := 0) : Prop :=
  DataProfile segment ∧ FreshSequence sender segment source ∧ segment.payload.length ≤ peerMSS.limit ∧
    ackOffset peer segment ≤ peer.observed ∧ peer.acknowledged ≤ ackOffset peer segment + 65535 ∧
    (segment.payload = [] ∨ Seq.distance sender.base segment.sequence + segment.payload.length ≤
      sender.acknowledged + sender.peerWindow.val) ∧
    (sentLane sender segment source).Valid ∧ (acknowledgedLane peer segment).Valid

instance (sender peer : Lane) (segment : Segment) (peerMSS : MSS.Offer) (source : Nat) :
    Decidable (DataAllowed sender peer segment peerMSS source) := by
  unfold DataAllowed
  infer_instance

theorem fresh_sequence_bound (sender : Lane) (segment : Segment) (source : Nat)
    (fresh : FreshSequence sender segment source) (valid : (sentLane sender segment source).Valid) :
    Seq.distance sender.controlOrigin segment.sequence ≤ (sentLane sender segment source).highEnd + 1 := by
  have offset : Seq.distance sender.base segment.sequence ≤ (sentLane sender segment source).highEnd := by
    unfold FreshSequence at fresh
    split at fresh
    · exact Nat.le_trans fresh (sentLane_monotone sender segment source).2
    · split at fresh
      · rename_i result accepted
        have slice := (Theory.SparseCoverage.accept_source _ _ _ _ _ _ accepted).2
        have member := (Theory.SparseCoverage.accept_source _ _ _ _ _ _ accepted).1
        have limit := Theory.SparseCoverage.State.limit_le_highEnd result.state result.source member
        simpa only [sentLane, accepted, Lane.highEnd] using (show Seq.distance sender.base segment.sequence ≤ result.state.highEnd by
          unfold Theory.SparseCoverage.Slice at slice
          unfold Theory.SparseCoverage.Run.limit at limit
          omega)
      · contradiction
  have bound := valid.2.1
  have shifted : sender.controlOrigin.add (1 + Seq.distance sender.base segment.sequence) = segment.sequence := by
    rw [← Seq.add_add, sender.controlOrigin_add, Seq.add_distance]
  have short : 1 + Seq.distance sender.base segment.sequence < Seq.modulus := by
    unfold Seq.halfSpace at bound
    unfold Seq.modulus
    omega
  rw [← shifted, Seq.distance_add, Nat.mod_eq_of_lt short]
  omega

theorem acknowledged_history (sender peer : Lane) (segment : Segment) (source : Nat)
    (history : WindowHistory peer sender) (allowed : DataAllowed sender peer segment peerMSS source) :
    WindowHistory (acknowledgedLane peer segment) (sentLane sender segment source) := by
  have monotone := (sentLane_monotone sender segment source).2
  have sequence := fresh_sequence_bound sender segment source allowed.2.1 allowed.2.2.2.2.2.2.1
  unfold acknowledgedLane
  split
  · simpa only [WindowHistory, Lane.controlOrigin, sentLane_base] using ⟨sequence, allowed.2.2.2.1⟩
  · exact ⟨by simpa only [Lane.controlOrigin, sentLane_base] using Nat.le_trans history.1 (Nat.add_le_add_right monotone 1),
      by simpa only [sentLane_base, Lane.observed] using history.2⟩

theorem acknowledgedLane_valid (peer : Lane) (segment : Segment) (valid : peer.Valid)
    (acknowledgment : ackOffset peer segment ≤ peer.observed) : (acknowledgedLane peer segment).Valid := by
  have extent := valid.2.2.1
  unfold Lane.outstanding at extent
  unfold acknowledgedLane
  split <;> refine ⟨?_, valid.2.1, ?_, valid.2.2.2⟩
  all_goals first
    | (change max peer.acknowledged (ackOffset peer segment) ≤ peer.observed
       exact Nat.max_le.mpr ⟨valid.1, acknowledgment⟩)
    | (change peer.highEnd - max peer.acknowledged (ackOffset peer segment) ≤ 65535
       omega)

theorem fresh_data_allowed (sender peer : Lane) (segment : Segment) (peerMSS : MSS.Offer) (source : Nat)
    (senderValid : sender.Valid) (peerValid : peer.Valid)
    (profile : DataProfile segment) (nonempty : segment.payload ≠ [])
    (mss : segment.payload.length ≤ peerMSS.limit)
    (epoch : Seq.distance sender.base segment.sequence + segment.payload.length + 2 < Seq.halfSpace)
    (left : sender.acknowledged ≤ Seq.distance sender.base segment.sequence)
    (right : Seq.distance sender.base segment.sequence + segment.payload.length ≤
      sender.acknowledged + sender.peerWindow.val)
    (disjoint : ∀ run ∈ sender.coverage.runs,
      Seq.distance sender.base segment.sequence + segment.payload.length ≤ run.position ∨
        run.limit ≤ Seq.distance sender.base segment.sequence)
    (acknowledgment : ackOffset peer segment ≤ peer.observed)
    (stale : peer.acknowledged ≤ ackOffset peer segment + 65535) :
    DataAllowed sender peer segment peerMSS source := by
  have inside : Seq.distance sender.base segment.sequence + segment.payload.length ≤ coverageBound := by
    unfold coverageBound Seq.halfSpace at *
    omega
  have separate : ∀ run ∈ sender.coverage.runs,
      (Theory.SparseCoverage.current sender.coverage (Seq.distance sender.base segment.sequence) segment.payload source).Before run ∨
        run.Before (Theory.SparseCoverage.current sender.coverage (Seq.distance sender.base segment.sequence) segment.payload source) := by
    intro run member
    simpa only [Theory.SparseCoverage.Run.Before, Theory.SparseCoverage.Run.limit,
      Theory.SparseCoverage.current] using disjoint run member
  obtain ⟨placed, accepted, novel, _, _, _⟩ := Theory.SparseCoverage.accept_fresh_exists sender.coverage
    (Seq.distance sender.base segment.sequence) segment.payload source coverageBound senderValid.2.2.2 nonempty inside separate
  have placementEq : placement sender segment source = .ok placed := accepted
  have fresh : FreshSequence sender segment source := by
    simp only [FreshSequence, nonempty, ite_false, placementEq]
    exact novel
  have stored := Theory.SparseCoverage.accept_valid _ _ _ _ _ _ accepted
  have frontier := Theory.SparseCoverage.accept_frontier_mono _ _ _ _ _ _ accepted
  have endPosition := Theory.SparseCoverage.accept_highEnd _ _ _ _ _ _ accepted
  have sentValid : (sentLane sender segment source).Valid := by
    rw [sentLane, placementEq]
    refine ⟨?_, ?_, ?_, stored⟩
    · change sender.acknowledged ≤ placed.state.frontier
      exact Nat.le_trans senderValid.1 frontier
    · change placed.state.highEnd + 2 < Seq.halfSpace
      rw [endPosition]
      have oldEnd := senderValid.2.1
      change sender.highEnd + 2 < Seq.halfSpace at oldEnd
      change max sender.highEnd (Seq.distance sender.base segment.sequence + segment.payload.length) + 2 < Seq.halfSpace
      omega
    · change placed.state.highEnd - sender.acknowledged ≤ 65535
      rw [endPosition]
      have oldExtent := senderValid.2.2.1
      have windowBound := sender.peerWindow.isLt
      have afterAck := Nat.le_trans left (Nat.le_add_right (Seq.distance sender.base segment.sequence) segment.payload.length)
      unfold Lane.outstanding at oldExtent
      change max sender.highEnd (Seq.distance sender.base segment.sequence + segment.payload.length) - sender.acknowledged ≤ 65535
      omega
  exact ⟨profile, fresh, mss, acknowledgment, stale, .inr right, sentValid,
    acknowledgedLane_valid peer segment peerValid acknowledgment⟩

def RangeFrom (sender : Lane) (entry : Entry) (direction : Direction) (segment : Segment) (seen : Seen) : Prop :=
  let start := Seq.distance sender.base segment.sequence
  let earlier := Seq.distance sender.base seen.segment.sequence
  seen.attachment.entry = entry ∧ seen.attachment.direction = direction ∧
    DataProfile seen.segment ∧ seen.segment.payload ≠ [] ∧ earlier ≤ start ∧
    start + segment.payload.length ≤ earlier + seen.segment.payload.length ∧
    earlier + seen.segment.payload.length ≤ sender.highEnd ∧
    segment.payload = (seen.segment.payload.drop (start - earlier)).take segment.payload.length

instance (sender : Lane) (entry : Entry) (direction : Direction) (segment : Segment) (seen : Seen) :
    Decidable (RangeFrom sender entry direction segment seen) := by
  unfold RangeFrom
  infer_instance

def KnownRange (sender : Lane) (entry : Entry) (direction : Direction) (segment : Segment)
    (observations : List Seen) : Prop :=
  match placement sender segment observations.length with
  | .error _ => False
  | .ok result => result.novel = 0 ∧
    match observations[result.source.metadata]? with
    | none => False
    | some seen => RangeFrom sender entry direction segment seen

instance (sender : Lane) (entry : Entry) (direction : Direction) (segment : Segment) (observations : List Seen) :
    Decidable (KnownRange sender entry direction segment observations) := by
  unfold KnownRange
  split
  · infer_instance
  · split <;> infer_instance

theorem KnownRange.placement (known : KnownRange sender entry direction segment observations) :
    ∃ result, placement sender segment observations.length = .ok result ∧ result.novel = 0 ∧
      ∃ seen, observations[result.source.metadata]? = some seen ∧ RangeFrom sender entry direction segment seen := by
  unfold KnownRange at known
  split at known
  · contradiction
  · rename_i result accepted
    refine ⟨result, accepted, known.1, ?_⟩
    split at known
    · exact False.elim known.2
    · rename_i seen selected
      exact ⟨seen, selected, known.2⟩

theorem KnownRange.source (known : KnownRange sender entry direction segment observations) :
    ∃ seen ∈ observations, RangeFrom sender entry direction segment seen := by
  obtain ⟨result, _, _, seen, selected, source⟩ := known.placement
  exact ⟨seen, List.mem_of_getElem? selected, source⟩

def RepeatedAllowed (sender peer : Lane) (entry : Entry) (direction : Direction) (segment : Segment)
    (peerMSS : MSS.Offer) (observations : List Seen) : Prop :=
  DataProfile segment ∧ segment.payload ≠ [] ∧
    Seq.distance sender.controlOrigin segment.sequence ≤ sender.highEnd + 1 ∧
    KnownRange sender entry direction segment observations ∧ segment.payload.length ≤ peerMSS.limit ∧
    ackOffset peer segment ≤ peer.observed ∧ peer.acknowledged ≤ ackOffset peer segment + 65535 ∧
    (acknowledgedLane peer segment).Valid

instance (sender peer : Lane) (entry : Entry) (direction : Direction) (segment : Segment)
    (peerMSS : MSS.Offer) (observations : List Seen) :
    Decidable (RepeatedAllowed sender peer entry direction segment peerMSS observations) := by
  unfold RepeatedAllowed
  infer_instance

theorem repeated_sent_history (sender peer : Lane) (segment : Segment) (history : WindowHistory sender peer) :
    WindowHistory sender (acknowledgedLane peer segment) := by
  simpa only [WindowHistory, Lane.controlOrigin, acknowledgedLane_base, acknowledgedLane_highEnd] using history

theorem repeated_acknowledged_history (sender peer : Lane) (segment : Segment)
    (history : WindowHistory peer sender)
    (sequence : Seq.distance sender.controlOrigin segment.sequence ≤ sender.highEnd + 1)
    (acknowledgment : ackOffset peer segment ≤ peer.observed) :
    WindowHistory (acknowledgedLane peer segment) sender := by
  unfold acknowledgedLane
  split
  · exact ⟨sequence, acknowledgment⟩
  · exact history

theorem RepeatedAllowed.source
    (allowed : RepeatedAllowed sender peer entry direction segment peerMSS observations) :
    ∃ seen ∈ observations, seen.attachment.entry = entry ∧ seen.attachment.direction = direction ∧
      segment.payload = (seen.segment.payload.drop
        (Seq.distance sender.base segment.sequence - Seq.distance sender.base seen.segment.sequence)).take
          segment.payload.length := by
  obtain ⟨seen, member, range⟩ := allowed.2.2.2.1.source
  exact ⟨seen, member, range.1, range.2.1, range.2.2.2.2.2.2.2⟩

def Allowed (phase : Phase) (attachment : ConntrackLifecycle.Attachment) (segment : Segment)
    (observations : List Seen := []) : Prop :=
  match phase with
  | .empty => attachment.fresh = true ∧ attachment.direction = .original ∧ Startup segment 2
  | .syn entry clientISS _ _ =>
    attachment.entry = entry ∧ attachment.fresh = false ∧ attachment.direction = .reply ∧
      Startup segment 18 ∧ segment.acknowledgment = clientISS.add 1
  | .synAck entry clientISS _ serverISS _ _ _ =>
    attachment.entry = entry ∧ attachment.fresh = false ∧ attachment.direction = .original ∧
      Startup segment 16 ∧ segment.sequence = clientISS.add 1 ∧ segment.acknowledgment = serverISS.add 1
  | .data session =>
    attachment.entry = session.entry ∧ attachment.fresh = false ∧
      match attachment.direction with
      | .original => DataAllowed session.original session.reply segment session.serverMSS observations.length ∨
          RepeatedAllowed session.original session.reply session.entry .original segment session.serverMSS observations
      | .reply => DataAllowed session.reply session.original segment session.clientMSS observations.length ∨
          RepeatedAllowed session.reply session.original session.entry .reply segment session.clientMSS observations

instance (phase : Phase) (attachment : ConntrackLifecycle.Attachment) (segment : Segment) (observations : List Seen) :
    Decidable (Allowed phase attachment segment observations) := by
  cases phase <;> cases selected : attachment.direction <;> simp only [Allowed, selected] <;> infer_instance

def nextPhase (phase : Phase) (attachment : ConntrackLifecycle.Attachment) (segment : Segment)
    {observations : List Seen} (allowed : Allowed phase attachment segment observations) : Phase :=
  match phase with
  | .empty => .syn attachment.entry segment.sequence segment.window
      (MSS.selectStartup segment.options (by simpa [Startup] using allowed.2.2.2.1)).val
  | .syn entry clientISS clientWindow clientMSS =>
    .synAck entry clientISS clientWindow segment.sequence segment.window clientMSS
      (MSS.selectStartup segment.options (by simpa [Startup] using allowed.2.2.2.1.2.1)).val
  | .synAck entry clientISS _ serverISS serverWindow clientMSS serverMSS =>
    .data ⟨entry,
      Lane.initial (clientISS.add 1) serverWindow serverISS (clientISS.add 1),
      Lane.initial (serverISS.add 1) segment.window segment.sequence segment.acknowledgment,
      Lane.initial_valid _ _ _ _, Lane.initial_valid _ _ _ _,
      by simp only [WindowHistory, Lane.controlOrigin, Lane.initial, Lane.highEnd, Lane.observed, Theory.SparseCoverage.State.highEnd,
        Theory.SparseCoverage.State.frontier, Theory.SparseCoverage.initial, Theory.SparseCoverage.highEnd,
        Theory.SparseCoverage.frontierFrom, control_inverse, Seq.distance_self]; decide,
      by
        have sequence := allowed.2.2.2.2.1
        have acknowledgment := allowed.2.2.2.2.2
        simp only [WindowHistory, Lane.controlOrigin, Lane.initial, Lane.highEnd, Lane.observed, Theory.SparseCoverage.State.highEnd,
          Theory.SparseCoverage.State.frontier, Theory.SparseCoverage.initial, Theory.SparseCoverage.highEnd,
          Theory.SparseCoverage.frontierFrom, control_inverse, sequence, acknowledgment,
          Seq.distance_add, Seq.distance_self]
        decide, clientMSS, serverMSS⟩
  | .data session =>
    match direction : attachment.direction with
    | .original =>
      have selected : DataAllowed session.original session.reply segment session.serverMSS observations.length ∨
          RepeatedAllowed session.original session.reply session.entry .original segment session.serverMSS observations := by
        simpa only [Allowed, direction] using allowed.2.2
      if fresh : DataAllowed session.original session.reply segment session.serverMSS observations.length then
        .data ⟨session.entry, sentLane session.original segment observations.length, acknowledgedLane session.reply segment,
          fresh.2.2.2.2.2.2.1, fresh.2.2.2.2.2.2.2,
          sent_history _ _ _ observations.length session.originalHistory,
          acknowledged_history _ _ _ observations.length session.replyHistory fresh,
          session.clientMSS, session.serverMSS⟩
      else
        have repeated := selected.resolve_left fresh
        .data ⟨session.entry, session.original, acknowledgedLane session.reply segment,
          session.originalValid, repeated.2.2.2.2.2.2.2,
          repeated_sent_history _ _ _ session.originalHistory,
          repeated_acknowledged_history _ _ _ session.replyHistory repeated.2.2.1 repeated.2.2.2.2.2.1,
          session.clientMSS, session.serverMSS⟩
    | .reply =>
      have selected : DataAllowed session.reply session.original segment session.clientMSS observations.length ∨
          RepeatedAllowed session.reply session.original session.entry .reply segment session.clientMSS observations := by
        simpa only [Allowed, direction] using allowed.2.2
      if fresh : DataAllowed session.reply session.original segment session.clientMSS observations.length then
        .data ⟨session.entry, acknowledgedLane session.original segment, sentLane session.reply segment observations.length,
          fresh.2.2.2.2.2.2.2, fresh.2.2.2.2.2.2.1,
          acknowledged_history _ _ _ observations.length session.originalHistory fresh,
          sent_history _ _ _ observations.length session.replyHistory, session.clientMSS, session.serverMSS⟩
      else
        have repeated := selected.resolve_left fresh
        .data ⟨session.entry, acknowledgedLane session.original segment, session.reply,
          repeated.2.2.2.2.2.2.2, session.replyValid,
          repeated_acknowledged_history _ _ _ session.originalHistory repeated.2.2.1 repeated.2.2.2.2.2.1,
          repeated_sent_history _ _ _ session.replyHistory, session.clientMSS, session.serverMSS⟩

inductive Unsupported where
  | missingHistory | replacement | direction | flags | options | data | sequence | acknowledgment
  | window | epoch | historyLost | overlap | conflict
  deriving Repr, BEq, DecidableEq

inductive Error where
  | unsupported (reason : Unsupported)
  deriving Repr, BEq, DecidableEq

def Error.message : Error → String
  | .unsupported .missingHistory => "The selected TCP attachment has no earlier admitted SYN."
  | .unsupported .replacement => "TCP attachment replacement or reopen is outside this profile."
  | .unsupported .direction => "The selected TCP direction requires processing outside this phase."
  | .unsupported .flags => "The TCP control flags require processing outside this profile."
  | .unsupported .options => "TCP option processing is outside this profile."
  | .unsupported .data => "The TCP payload requires processing outside this profile."
  | .unsupported .sequence => "The TCP sequence is outside the selected observed byte epoch."
  | .unsupported .acknowledgment => "The TCP ACK is outside the selected observed byte history."
  | .unsupported .window => "New TCP data exceeds the observed peer window."
  | .unsupported .epoch => "The TCP byte epoch or outstanding span exceeds the selected bounds."
  | .unsupported .overlap => "The TCP range partly overlaps an earlier observation."
  | .unsupported .conflict => "The TCP range conflicts with earlier observed bytes."
  | .unsupported .historyLost => "The earlier TCP entry is absent from the resulting confirmed table."

private def startupReason (segment : Segment) (flags : UInt8) : Unsupported :=
  if (if flags = 16 then segment.options ≠ [] else (MSS.readStartup segment.options).isOk = false) then .options
  else if segment.flags ≠ flags then .flags
  else if segment.payload ≠ [] then .data
  else .acknowledgment

private def dataReason (sender peer : Lane) (segment : Segment) (peerMSS : MSS.Offer)
    (_entry : Entry) (_direction : Direction) (observations : List Seen) : Unsupported :=
  if segment.options ≠ [] then .options
  else if ¬(segment.flags = 16 ∨ segment.flags = 24) then .flags
  else if segment.payload.length > peerMSS.limit then .data
  else if Seq.distance sender.base segment.sequence > coverageBound then .sequence
  else if segment.payload = [] ∧ Seq.distance sender.base segment.sequence > sender.highEnd then .sequence
  else
    let storage := placement sender segment observations.length
    match storage with
    | .error .overlap => .overlap
    | .error .conflict => .conflict
    | _ =>
      if ackOffset peer segment > peer.observed ∨ peer.acknowledged > ackOffset peer segment + 65535 then .acknowledgment
      else if segment.payload ≠ [] ∧
          (match storage with | .ok result => result.novel | .error _ => segment.payload.length) ≠ 0 ∧
          Seq.distance sender.base segment.sequence + segment.payload.length >
            sender.acknowledged + sender.peerWindow.val then .window
      else .epoch

def reason (phase : Phase) (attachment : ConntrackLifecycle.Attachment) (segment : Segment)
    (observations : List Seen := []) : Unsupported :=
  match phase with
  | .empty =>
    if attachment.fresh ≠ true ∨ attachment.direction ≠ .original then .missingHistory
    else startupReason segment 2
  | .syn entry clientISS _ _ =>
    if attachment.entry ≠ entry ∨ attachment.fresh ≠ false then .replacement
    else if attachment.direction ≠ .reply then .direction
    else if ¬Startup segment 18 then startupReason segment 18
    else if segment.acknowledgment ≠ clientISS.add 1 then .acknowledgment
    else .epoch
  | .synAck entry clientISS _ serverISS _ _ _ =>
    if attachment.entry ≠ entry ∨ attachment.fresh ≠ false then .replacement
    else if attachment.direction ≠ .original then .direction
    else if ¬Startup segment 16 then startupReason segment 16
    else if segment.sequence ≠ clientISS.add 1 then .sequence
    else if segment.acknowledgment ≠ serverISS.add 1 then .acknowledgment
    else .epoch
  | .data session =>
    if attachment.entry ≠ session.entry ∨ attachment.fresh ≠ false then .replacement
    else match attachment.direction with
      | .original => dataReason session.original session.reply segment session.serverMSS session.entry .original observations
      | .reply => dataReason session.reply session.original segment session.clientMSS session.entry .reply observations

structure Result (before : State) (input : Input) (lifecycle : ConntrackLifecycle.Input)
    (prepared : ConntrackLifecycle.Prepared lifecycle) where
  state : State
  admitted : Allowed before.phase prepared.attachment input.packet.segment before.observations
  phase : state.phase = nextPhase before.phase prepared.attachment input.packet.segment admitted
  ledger : state.observations = before.observations ++ [observe input lifecycle prepared]
  selectedKey : prepared.attachment.entry.flow.key prepared.attachment.direction = (lifecycle.zone, input.packet.header)

def step (before : State) (input : Input) (lifecycle : ConntrackLifecycle.Input)
    (prepared : ConntrackLifecycle.Prepared lifecycle) (same : lifecycle.packet = input.packet.header) :
    Except Error (Result before input lifecycle prepared) :=
  if allowed : Allowed before.phase prepared.attachment input.packet.segment before.observations then
    .ok ⟨⟨nextPhase before.phase prepared.attachment input.packet.segment allowed,
        before.observations ++ [observe input lifecycle prepared]⟩, allowed, rfl, rfl,
      by simpa only [same] using prepared.attached⟩
  else .error (.unsupported (reason before.phase prepared.attachment input.packet.segment before.observations))

def confirmed (entry : Entry) (tracker : ConntrackLifecycle.State) : Bool :=
  tracker.records.any (fun record => decide (record.entry = entry))

def commit (result : Result before input lifecycle prepared) (tracker : ConntrackLifecycle.State) : Except Error State :=
  if confirmed prepared.attachment.entry tracker then .ok result.state
  else if prepared.attachment.fresh then .ok State.initial
  else .error (.unsupported .historyLost)

theorem nextPhase_entry (phase : Phase) (attachment : ConntrackLifecycle.Attachment) (segment : Segment)
    {observations : List Seen} (allowed : Allowed phase attachment segment observations) :
    (nextPhase phase attachment segment allowed).entry = some attachment.entry := by
  cases phase with
  | empty => rfl
  | syn entry iss window clientMSS => exact congrArg some allowed.1.symm
  | synAck entry clientISS clientWindow serverISS serverWindow clientMSS serverMSS => exact congrArg some allowed.1.symm
  | data session =>
    cases attachment with
    | mk entry direction classification fresh =>
      cases direction <;> simp only [nextPhase] <;> split <;> exact congrArg some allowed.1.symm

theorem Result.selected_entry (result : Result before input lifecycle prepared) :
    result.state.phase.entry = some prepared.attachment.entry := by
  rw [result.phase]
  exact nextPhase_entry _ _ _ result.admitted

theorem Result.fresh_phase (result : Result before input lifecycle prepared)
    (fresh : prepared.attachment.fresh = true) : before.phase = .empty := by
  have allowed := result.admitted
  cases selected : before.phase with
  | empty => rfl
  | syn entry iss window clientMSS => simp only [Allowed, selected] at allowed; simp [fresh] at allowed
  | synAck entry clientISS clientWindow serverISS serverWindow clientMSS serverMSS =>
    simp only [Allowed, selected] at allowed
    simp [fresh] at allowed
  | data session => simp only [Allowed, selected] at allowed; simp [fresh] at allowed

theorem step_exists (before : State) (input : Input) (lifecycle : ConntrackLifecycle.Input)
    (prepared : ConntrackLifecycle.Prepared lifecycle) (same : lifecycle.packet = input.packet.header)
    (allowed : Allowed before.phase prepared.attachment input.packet.segment before.observations) :
    ∃ result, step before input lifecycle prepared same = .ok result := by
  simp only [step, allowed, dite_true]
  exact ⟨_, rfl⟩

theorem confirmed_correct (entry : Entry) (tracker : ConntrackLifecycle.State) :
    confirmed entry tracker = true ↔ ∃ record ∈ tracker.records, record.entry = entry := by
  simp only [confirmed, List.any_eq_true, decide_eq_true_eq]

theorem commit_cases (result : Result before input lifecycle prepared) (tracker : ConntrackLifecycle.State)
    (after : State) (accepted : commit result tracker = .ok after) :
    (after = result.state ∧ confirmed prepared.attachment.entry tracker = true) ∨
      (after = State.initial ∧ prepared.attachment.fresh = true ∧ confirmed prepared.attachment.entry tracker = false) := by
  unfold commit at accepted
  split at accepted
  · rename_i present
    cases accepted
    exact .inl ⟨rfl, present⟩
  · rename_i absent
    have missing : confirmed prepared.attachment.entry tracker = false := by
      cases selected : confirmed prepared.attachment.entry tracker <;> simp_all
    split at accepted
    · rename_i fresh
      cases accepted
      exact .inr ⟨rfl, fresh, missing⟩
    · cases accepted

theorem Result.existing_committed (result : Result before input lifecycle prepared) (tracker : ConntrackLifecycle.State)
    (fresh : prepared.attachment.fresh = false) (after : State) (accepted : commit result tracker = .ok after) :
    after = result.state ∧ (∃ record ∈ tracker.records, record.entry = prepared.attachment.entry) ∧
      after.observations = before.observations ++ [observe input lifecycle prepared] := by
  rcases commit_cases result tracker after accepted with ⟨same, confirmed⟩ | ⟨_, newer, _⟩
  · exact ⟨same, (confirmed_correct _ _).mp confirmed, same ▸ result.ledger⟩
  · simp [fresh] at newer

theorem Result.actual_bytes (result : Result before input lifecycle prepared) :
    ∃ prior, result.state.observations = prior ++ [observe input lifecycle prepared] ∧
      (observe input lifecycle prepared).bytes = input.bytes :=
  ⟨before.observations, result.ledger, rfl⟩

theorem Result.source_key (result : Result before input lifecycle prepared) :
    prepared.attachment.entry.flow.key prepared.attachment.direction = (lifecycle.zone, input.packet.header) := result.selectedKey

theorem Result.checked_source (_result : Result before input lifecycle prepared) :
    decodeIPv4 input.bytes = .ok input.packet := input.checked

theorem Result.confirmed_keeps (result : Result before input lifecycle prepared) (tracker : ConntrackLifecycle.State)
    (present : confirmed prepared.attachment.entry tracker = true) : commit result tracker = .ok result.state := by
  simp only [commit, present, ite_true]

theorem Result.fresh_unconfirmed (result : Result before input lifecycle prepared) (tracker : ConntrackLifecycle.State)
    (absent : confirmed prepared.attachment.entry tracker = false) (fresh : prepared.attachment.fresh = true) :
    commit result tracker = .ok State.initial := by
  simp only [commit, absent, Bool.false_eq_true, ite_false, fresh, ite_true]

theorem Result.existing_missing (result : Result before input lifecycle prepared) (tracker : ConntrackLifecycle.State)
    (absent : confirmed prepared.attachment.entry tracker = false) (fresh : prepared.attachment.fresh = false) :
    commit result tracker = .error (.unsupported .historyLost) := by
  simp only [commit, absent, fresh, Bool.false_eq_true, ite_false]

theorem data_ack_bound (sender peer : Lane) (segment : Segment) {peerMSS : MSS.Offer} {source : Nat}
    (allowed : DataAllowed sender peer segment peerMSS source) :
    segment.payload.length ≤ peerMSS.limit ∧ ackOffset peer segment ≤ peer.observed :=
  ⟨allowed.2.2.1, allowed.2.2.2.1⟩

theorem Lane.cursor (lane : Lane) (valid : lane.Valid) : lane.una.add lane.outstanding = lane.highNext := by
  simp only [Lane.una, Lane.outstanding, Lane.highNext, Seq.add_add]
  have covered := lane.coverage.frontier_le_highEnd
  have sum : lane.acknowledged + (lane.highEnd - lane.acknowledged) = lane.highEnd := by
    have bound := valid.1
    change lane.observed ≤ lane.highEnd at covered
    omega
  rw [sum]

theorem data_ack_count (sender peer : Lane) (segment : Segment) (valid : peer.Valid)
    {peerMSS : MSS.Offer} {source : Nat} (allowed : DataAllowed sender peer segment peerMSS source) :
    EstablishedReceive.acknowledgedCountAt peer.una peer.outstanding segment.acknowledgment =
      some (ackOffset peer segment - peer.acknowledged) := by
  have covered : peer.observed ≤ peer.highEnd := peer.coverage.frontier_le_highEnd
  have short : peer.observed + 1 < Seq.halfSpace := by have bound := valid.2.1; omega
  have acknowledgedBound : peer.acknowledged < Seq.modulus := by
    have amount := valid.1
    have bound := valid.2.1
    unfold Seq.modulus Seq.halfSpace at *
    omega
  have unaOffset : Seq.distance peer.base peer.una = peer.acknowledged := by
    rw [Lane.una, Seq.distance_add, Nat.mod_eq_of_lt acknowledgedBound]
  have unaInside : Seq.InInterval peer.base (peer.observed + 1) peer.una := by
    unfold Seq.InInterval
    rw [unaOffset]
    have bound := valid.1
    omega
  have ackInside : Seq.InInterval peer.base (peer.observed + 1) segment.acknowledgment := by
    have bound := allowed.2.2.2.1
    unfold Seq.InInterval ackOffset at *
    omega
  by_cases forward : peer.acknowledged ≤ ackOffset peer segment
  · have distance : Seq.distance peer.una segment.acknowledgment = ackOffset peer segment - peer.acknowledged := by
      simpa only [unaOffset, ackOffset] using Seq.common_arc_distance peer.base peer.una segment.acknowledgment
        (peer.observed + 1) short unaInside ackInside (by simpa only [unaOffset, ackOffset] using forward)
    have fits : Seq.distance peer.una segment.acknowledgment ≤ peer.outstanding := by
      rw [distance]
      have bound := allowed.2.2.2.1
      unfold Lane.outstanding
      omega
    unfold EstablishedReceive.acknowledgedCountAt
    rw [ite_eq_left fits, distance]
  · have reverse : Seq.distance segment.acknowledgment peer.una = peer.acknowledged - ackOffset peer segment := by
      simpa only [unaOffset, ackOffset] using Seq.common_arc_distance peer.base segment.acknowledgment peer.una
        (peer.observed + 1) short ackInside unaInside
        (by simpa only [unaOffset, ackOffset] using Nat.le_of_lt (Nat.lt_of_not_ge forward))
    have different : peer.una ≠ segment.acknowledgment := by
      intro same
      have offset := congrArg (Seq.distance peer.base) same
      rw [unaOffset] at offset
      exact forward (Nat.le_of_eq offset)
    have total := Seq.distance_reverse peer.una segment.acknowledgment different
    rw [reverse] at total
    have gap := allowed.2.2.2.2.1
    have span := valid.2.2.1
    have outside : ¬Seq.distance peer.una segment.acknowledgment ≤ peer.outstanding := by
      unfold Seq.modulus at total
      omega
    have old : Seq.distance segment.acknowledgment peer.una ≤ EstablishedReceive.maxSendWindow := by
      rw [reverse]
      unfold EstablishedReceive.maxSendWindow
      omega
    have zero : ackOffset peer segment - peer.acknowledged = 0 := by omega
    unfold EstablishedReceive.acknowledgedCountAt
    rw [ite_eq_right outside, ite_eq_left old, zero]

theorem acknowledgedLane_count (peer : Lane) (segment : Segment) :
    (acknowledgedLane peer segment).acknowledged = max peer.acknowledged (ackOffset peer segment) := by
  unfold acknowledgedLane
  split <;> rfl

theorem old_ack_window (peer : Lane) (segment : Segment) (old : ackOffset peer segment < peer.acknowledged) :
    windowEligible peer segment = false ∧
      (acknowledgedLane peer segment).peerWindow = peer.peerWindow ∧
      (acknowledgedLane peer segment).windowSequence = peer.windowSequence ∧
      (acknowledgedLane peer segment).windowAcknowledgment = peer.windowAcknowledgment := by
  have outside : ¬peer.acknowledged ≤ ackOffset peer segment := by omega
  have rejected : windowEligible peer segment = false := by simp only [windowEligible, outside, decide_false, Bool.false_and]
  exact ⟨rejected, by simp only [acknowledgedLane, rejected, Bool.false_eq_true, ite_false],
    by simp only [acknowledgedLane, rejected, Bool.false_eq_true, ite_false],
    by simp only [acknowledgedLane, rejected, Bool.false_eq_true, ite_false]⟩

theorem duplicate_ack_window (peer : Lane) (segment : Segment)
    (same : ackOffset peer segment = peer.acknowledged) :
    windowEligible peer segment = windowFresh peer segment := by
  simp only [windowEligible, same, Nat.le_refl, decide_true, Bool.true_and]

theorem windowFresh_coordinates (sender peer : Lane) (segment : Segment)
    (_senderValid : sender.Valid) (peerValid : peer.Valid) (history : WindowHistory peer sender)
    {peerMSS : MSS.Offer} {source : Nat} (allowed : DataAllowed sender peer segment peerMSS source) :
    windowFresh peer segment = true ↔
      Seq.distance sender.controlOrigin peer.windowSequence < Seq.distance sender.controlOrigin segment.sequence ∨
        (peer.windowSequence = segment.sequence ∧
          Seq.distance peer.base peer.windowAcknowledgment ≤ ackOffset peer segment) := by
  have updated := allowed.2.2.2.2.2.2.1
  have monotone := (sentLane_monotone sender segment source).2
  have sequenceBound := fresh_sequence_bound sender segment source allowed.2.1 updated
  have sequenceShort : (sentLane sender segment source).highEnd + 2 < Seq.halfSpace := updated.2.1
  have covered : peer.observed ≤ peer.highEnd := peer.coverage.frontier_le_highEnd
  have ackShort : peer.observed + 1 < Seq.halfSpace := by have bound := peerValid.2.1; omega
  have oldSequence : Seq.InInterval sender.controlOrigin ((sentLane sender segment source).highEnd + 2) peer.windowSequence := by
    have bound := history.1
    unfold Seq.InInterval
    omega
  have newSequence : Seq.InInterval sender.controlOrigin ((sentLane sender segment source).highEnd + 2) segment.sequence := by
    unfold Seq.InInterval
    omega
  have oldAck : Seq.InInterval peer.base (peer.observed + 1) peer.windowAcknowledgment := by
    have bound := history.2
    unfold Seq.InInterval
    omega
  have newAck : Seq.InInterval peer.base (peer.observed + 1) segment.acknowledgment := by
    have bound := allowed.2.2.2.1
    unfold Seq.InInterval ackOffset at *
    omega
  have sequenceOrder := Seq.common_arc_before sender.controlOrigin peer.windowSequence segment.sequence
    ((sentLane sender segment source).highEnd + 2) sequenceShort oldSequence newSequence
  have ackOrder := Seq.common_arc_before peer.base peer.windowAcknowledgment segment.acknowledgment
    (peer.observed + 1) ackShort oldAck newAck
  have ackEqual : peer.windowAcknowledgment = segment.acknowledgment ↔
      Seq.distance peer.base peer.windowAcknowledgment = ackOffset peer segment := by
    constructor
    · intro same; rw [same]; rfl
    · intro same
      calc
        _ = peer.base.add (Seq.distance peer.base peer.windowAcknowledgment) := (Seq.add_distance _ _).symm
        _ = peer.base.add (ackOffset peer segment) := congrArg (Seq.add peer.base) same
        _ = _ := Seq.add_distance _ _
  simp only [windowFresh, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, Seq.before_correct]
  rw [sequenceOrder, ackOrder]
  change _ ∨ (peer.windowSequence = segment.sequence ∧
    (peer.windowAcknowledgment = segment.acknowledgment ∨
      Seq.distance peer.base peer.windowAcknowledgment < ackOffset peer segment)) ↔ _
  rw [ackEqual]
  have arithmetic (a b : Nat) : a = b ∨ a < b ↔ a ≤ b := by omega
  rw [arithmetic]

end Netlib.Protocol.TCP.Admission
