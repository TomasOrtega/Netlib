import Netlib.Protocol.IPv4Fragmentation
import Netlib.Protocol.IPv4InputFragment

/-!
# Re-fragmentation contracts

The caller supplies the effective size cap and the selected output DF behavior.
Generated families follow the copying layout. Checked families can retain other legal boundaries.
These contracts do not select Linux allocation or fragment-list paths.
-/

namespace Netlib.Protocol.IPv4Refragmentation

open IPv4Fragmentation

abbrev Budget := { value : Nat // 28 ≤ value ∧ value < 65536 }

def Budget.cap (route ingress : Budget) : Budget :=
  ⟨min route.val ingress.val, by constructor <;> have := route.property <;> have := ingress.property <;> omega⟩

def outputPacket (packet : IPv4.Packet) (df : Bool) : IPv4.Packet :=
  { packet with dontFragment := df }

def capacity (budget : Budget) : Nat := ((budget.val - 20) / 8) * 8

def payloadLimit (budget : Budget) : Nat := budget.val - 20

theorem capacity_positive (budget : Budget) : 0 < capacity budget := by
  have := budget.property.1
  unfold capacity
  omega

theorem capacity_aligned (budget : Budget) : capacity budget % 8 = 0 := by simp [capacity]

theorem capacity_le_limit (budget : Budget) : capacity budget ≤ payloadLimit budget := by
  unfold capacity payloadLimit
  omega

def pieces (packet : IPv4.Packet) (budget : Budget) : List Piece :=
  if packet.wireLength ≤ budget.val then [⟨0, packet.payload, false⟩]
  else chunks (capacity budget) (capacity_positive budget) (payloadLimit budget)
    (capacity_le_limit budget) 0 packet.payload

theorem pieces_layout (packet : IPv4.Packet) (budget : Budget) : Layout 0 packet.payload (pieces packet budget) := by
  unfold pieces
  split
  · exact .last _ _
  · exact chunks_layout _ _ (capacity_aligned budget) _ _ _ _

theorem pieces_fits (packet : IPv4.Packet) (budget : Budget) :
    ∀ piece ∈ pieces packet budget, piece.data.length + 20 ≤ budget.val := by
  unfold pieces
  split
  · intro piece member
    simp only [List.mem_singleton] at member
    subst piece
    assumption
  · intro piece member
    have := chunks_fits _ (capacity_positive budget) _ (capacity_le_limit budget) 0 packet.payload piece member
    have := budget.property.1
    unfold payloadLimit at *
    omega

theorem pieces_positive (packet : IPv4.Packet) (budget : Budget) :
    ∀ piece ∈ pieces packet budget, piece.start ≠ 0 → piece.data ≠ [] := by
  unfold pieces
  split
  · simp
  · rename_i large
    have nonempty : packet.payload ≠ [] := by
      intro empty
      have := budget.property.1
      simp [IPv4.Packet.wireLength, empty] at large
      omega
    exact fun piece member _ =>
      chunks_positive _ (capacity_positive budget) _ (capacity_le_limit budget) _ _ nonempty piece member

def FlagsValid (packet : IPv4Fragment.Packet) : Prop :=
  (packet.moreFragments = true → packet.payload ≠ [] ∧ packet.payload.length % 8 = 0) ∧
    (packet.offset.val ≠ 0 → packet.payload ≠ [])

instance (packet : IPv4Fragment.Packet) : Decidable (FlagsValid packet) := by unfold FlagsValid; infer_instance

def validFragment (part : IPv4Fragment.Decoded) : Bool :=
  decide (part.packet.wireLength < 65536 ∧ FlagsValid part.packet) &&
    InternetChecksum.valid (IPv4Fragment.headerBytes part.packet part.checksum)

theorem validFragment_spec (part : IPv4Fragment.Decoded) :
    validFragment part = true ↔ part.packet.wireLength < 65536 ∧ FlagsValid part.packet ∧
      InternetChecksum.valid (IPv4Fragment.headerBytes part.packet part.checksum) = true := by
  simp only [validFragment, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨bounded, flags⟩, checked⟩
    exact ⟨bounded, flags, checked⟩
  · rintro ⟨bounded, flags, checked⟩
    exact ⟨⟨bounded, flags⟩, checked⟩

def scanMatches (payload : List UInt8) (parts : List Piece) : Bool :=
  match scan 0 parts with
  | .ok actual => decide (actual = payload)
  | .error _ => false

theorem scanMatches_spec (payload : List UInt8) (parts : List Piece) :
    scanMatches payload parts = true ↔ scan 0 parts = .ok payload := by
  unfold scanMatches
  cases joined : scan 0 parts <;> simp

def Accepts (packet : IPv4.Packet) (budget : Budget) (df : Bool) (fragments : List IPv4Fragment.Decoded) : Prop :=
  packet.Encodable ∧ fragments ≠ [] ∧ fragments.all validFragment = true ∧
    fragments.all (fun part => decide (part.packet.wireLength ≤ budget.val)) = true ∧
    fragments.all (fun part => decide (metadata part = { outputPacket packet df with payload := [] })) = true ∧
    scanMatches packet.payload ((sort fragments).map asPiece) = true

instance (packet : IPv4.Packet) (budget : Budget) (df : Bool) (fragments : List IPv4Fragment.Decoded) :
    Decidable (Accepts packet budget df fragments) := by unfold Accepts; infer_instance

structure CertifiedFamily (packet : IPv4.Packet) (budget : Budget) (df : Bool) where
  fragments : List IPv4Fragment.Decoded
  accepted : Accepts packet budget df fragments

def check (packet : IPv4.Packet) (budget : Budget) (df : Bool) (fragments : List IPv4Fragment.Decoded) :
    Except String (CertifiedFamily packet budget df) :=
  if accepted : Accepts packet budget df fragments then .ok ⟨fragments, accepted⟩
  else .error "The observed IPv4 fragment family violates its payload, metadata, or size contract."

theorem check_sound (packet : IPv4.Packet) (budget : Budget) (df : Bool) (fragments : List IPv4Fragment.Decoded)
    (result : CertifiedFamily packet budget df) (checked : check packet budget df fragments = .ok result) :
    result.fragments = fragments ∧ Accepts packet budget df fragments := by
  unfold check at checked
  split at checked
  · cases checked
    exact ⟨rfl, by assumption⟩
  · cases checked

def reassemble (fragments : List IPv4Fragment.Decoded) : Except String IPv4.Packet :=
  match sort fragments with
  | [] => .error "Supply at least one fragment."
  | first :: rest => do
    if !(first :: rest).all validFragment then throw "A fragment has invalid fields or checksum."
    if !(first :: rest).all (fun part => decide (metadata part = metadata first)) then
      throw "The fragment family has inconsistent metadata."
    let payload ← scan 0 ((first :: rest).map asPiece)
    let packet := { metadata first with payload }
    if packet.Encodable then return packet
    else throw "The reassembled IPv4 datagram exceeds its total-length field."

namespace CertifiedFamily

variable {packet : IPv4.Packet} {budget : Budget} {df : Bool}

theorem bounded (result : CertifiedFamily packet budget df) : packet.Encodable := result.accepted.1

theorem nonempty (result : CertifiedFamily packet budget df) : result.fragments ≠ [] := result.accepted.2.1

theorem checked (result : CertifiedFamily packet budget df) (part : IPv4Fragment.Decoded)
    (member : part ∈ result.fragments) : validFragment part = true :=
  List.all_eq_true.mp result.accepted.2.2.1 part member

theorem fits (result : CertifiedFamily packet budget df) (part : IPv4Fragment.Decoded)
    (member : part ∈ result.fragments) : part.packet.wireLength ≤ budget.val :=
  of_decide_eq_true (List.all_eq_true.mp result.accepted.2.2.2.1 part member)

theorem common (result : CertifiedFamily packet budget df) (part : IPv4Fragment.Decoded)
    (member : part ∈ result.fragments) : metadata part = { outputPacket packet df with payload := [] } :=
  of_decide_eq_true (List.all_eq_true.mp result.accepted.2.2.2.2.1 part member)

theorem joined (result : CertifiedFamily packet budget df) :
    scan 0 ((sort result.fragments).map asPiece) = .ok packet.payload :=
  (scanMatches_spec _ _).mp result.accepted.2.2.2.2.2

theorem layout (result : CertifiedFamily packet budget df) :
    Layout 0 packet.payload ((sort result.fragments).map asPiece) := by
  apply scan_layout _ _ _ result.joined
  intro piece member more
  obtain ⟨part, belongs, same⟩ := List.mem_map.mp member
  subst piece
  exact ((validFragment_spec part).mp (result.checked part (List.mem_mergeSort.mp belongs))).2.1.1 more

theorem payload (result : CertifiedFamily packet budget df) :
    (sort result.fragments).flatMap (·.packet.payload) = packet.payload := by
  simpa only [List.flatMap_map, Function.comp_def, asPiece] using result.layout.payload

theorem ordered_bounds (result : CertifiedFamily packet budget df) (part : IPv4Fragment.Decoded)
    (member : part ∈ sort result.fragments) :
    part.packet.offset.val * 8 + part.packet.payload.length ≤ packet.payload.length := by
  have bounds := result.layout.bounds (asPiece part) (List.mem_map.mpr ⟨part, member, rfl⟩)
  simpa only [asPiece, Nat.zero_add] using bounds.2

theorem metadata (result : CertifiedFamily packet budget df) (part : IPv4Fragment.Decoded)
    (member : part ∈ result.fragments) :
    part.packet.tos = packet.tos ∧ part.packet.identification = packet.identification ∧
    part.packet.dontFragment = df ∧ part.packet.ttl = packet.ttl ∧ part.packet.protocol = packet.protocol ∧
    part.packet.source = packet.source ∧ part.packet.destination = packet.destination := by
  have common := result.common part member
  have tos := congrArg IPv4.Packet.tos common
  have identification := congrArg IPv4.Packet.identification common
  have dontFragment := congrArg IPv4.Packet.dontFragment common
  have ttl := congrArg IPv4.Packet.ttl common
  have protocol := congrArg IPv4.Packet.protocol common
  have source := congrArg IPv4.Packet.source common
  have destination := congrArg IPv4.Packet.destination common
  exact ⟨tos, identification, dontFragment, ttl, protocol, source, destination⟩

def bytes (result : CertifiedFamily packet budget df) : List (List UInt8) :=
  result.fragments.map (fun part => fragmentBytes part ++ part.padding)

theorem encoded (result : CertifiedFamily packet budget df) (part : IPv4Fragment.Decoded)
    (member : part ∈ result.fragments) :
    IPv4InputFragment.encodeDecoded part = .ok (fragmentBytes part ++ part.padding) := by
  obtain ⟨bounded, _, checksum⟩ := (validFragment_spec part).mp (result.checked part member)
  simp only [IPv4InputFragment.encodeDecoded, bounded, checksum, ite_true, fragmentBytes, List.append_assoc]

theorem decoded (result : CertifiedFamily packet budget df) (part : IPv4Fragment.Decoded)
    (member : part ∈ result.fragments) :
    IPv4InputFragment.decode (fragmentBytes part ++ part.padding) = .ok part :=
  IPv4InputFragment.decode_encodeDecoded part _ (result.encoded part member)

theorem reassembled (result : CertifiedFamily packet budget df) :
    reassemble result.fragments = .ok (outputPacket packet df) := by
  have orderedNonempty : sort result.fragments ≠ [] := by
    intro empty
    have : (sort result.fragments).length = result.fragments.length := by
      exact (List.mergeSort_perm result.fragments
        (fun first second => decide ((asPiece first).start ≤ (asPiece second).start))).length_eq
    rw [empty] at this
    exact result.nonempty (List.length_eq_zero_iff.mp this.symm)
  have allChecked : (sort result.fragments).all validFragment = true := by
    apply List.all_eq_true.mpr
    intro part member
    exact result.checked part (List.mem_mergeSort.mp member)
  have allCommon : ∀ part ∈ sort result.fragments,
      IPv4Fragmentation.metadata part = { outputPacket packet df with payload := [] } := by
    intro part member
    exact result.common part (List.mem_mergeSort.mp member)
  have joined := result.joined
  cases sorted : sort result.fragments with
  | nil => exact False.elim (orderedNonempty sorted)
  | cons first rest =>
    rw [sorted] at allChecked allCommon joined
    have firstCommon := allCommon first (by simp)
    have equalMetadata : (first :: rest).all
        (fun part => decide (IPv4Fragmentation.metadata part = IPv4Fragmentation.metadata first)) = true := by
      apply List.all_eq_true.mpr
      intro part member
      exact decide_eq_true ((allCommon part member).trans firstCommon.symm)
    simp only [reassemble, sorted, allChecked, equalMetadata, Bool.not_true, Bool.false_eq_true,
      ite_false, joined, bind, Except.bind]
    rw [firstCommon]
    have bounded : (outputPacket packet df).Encodable := result.bounded
    change (if (outputPacket packet df).Encodable then _ else _) = _
    simp only [bounded, ite_true, pure, Except.pure]
    rfl

end CertifiedFamily

def generatedFragments (packet : IPv4.Packet) (budget : Budget) (df : Bool) : List IPv4Fragment.Decoded :=
  (pieces packet budget).map (fragmentDecoded (outputPacket packet df))

theorem fragment_offset (packet : IPv4.Packet) (budget : Budget) (df : Bool) (bounded : packet.Encodable)
    (piece : Piece) (member : piece ∈ pieces packet budget) :
    (fragmentPacket (outputPacket packet df) piece).offset.val * 8 = piece.start := by
  have limits := (pieces_layout packet budget).bounds piece member
  have aligned := (pieces_layout packet budget).aligned (by decide) piece member
  have maximum : packet.payload.length + 20 < 65536 := bounded
  have fits : piece.start / 8 < 8192 := by omega
  change (piece.start / 8 % 8192) * 8 = piece.start
  rw [Nat.mod_eq_of_lt fits]
  omega

theorem generated_projection (packet : IPv4.Packet) (budget : Budget) (df : Bool) (bounded : packet.Encodable) :
    (generatedFragments packet budget df).map asPiece = pieces packet budget := by
  unfold generatedFragments
  rw [List.map_map]
  have same : (pieces packet budget).map (asPiece ∘ fragmentDecoded (outputPacket packet df)) =
      (pieces packet budget).map id := by
    apply List.map_congr_left
    intro piece member
    have offset := fragment_offset packet budget df bounded piece member
    change (Piece.mk ((fragmentPacket (outputPacket packet df) piece).offset.val * 8) piece.data piece.more) = piece
    rw [offset]
  simpa only [List.map_id] using same

theorem generated_sorted (packet : IPv4.Packet) (budget : Budget) (df : Bool) (bounded : packet.Encodable) :
    sort (generatedFragments packet budget df) = generatedFragments packet budget df := by
  apply List.mergeSort_of_pairwise
  have sorted := (pieces_layout packet budget).sorted
  rw [← generated_projection packet budget df bounded] at sorted
  exact (List.pairwise_map.mp sorted).imp (fun relation => by simpa only [decide_eq_true_eq] using relation)

theorem generated_valid (packet : IPv4.Packet) (budget : Budget) (df : Bool) :
    ∀ part ∈ generatedFragments packet budget df, validFragment part = true := by
  intro part member
  obtain ⟨piece, belongs, same⟩ := List.mem_map.mp member
  subst part
  apply validFragment_spec _ |>.mpr
  refine ⟨?_, ⟨?_, ?_⟩, IPv4Fragment.computedChecksum_valid _⟩
  · have fit := pieces_fits packet budget piece belongs
    have := budget.property.2
    change piece.data.length + 20 < 65536
    omega
  · exact (pieces_layout packet budget).flags piece belongs
  · intro offset
    apply pieces_positive packet budget piece belongs
    intro zero
    apply offset
    simp [fragmentDecoded, fragmentPacket, zero]

theorem generated_accepts (packet : IPv4.Packet) (budget : Budget) (df : Bool) (bounded : packet.Encodable) :
    Accepts packet budget df (generatedFragments packet budget df) := by
  refine ⟨bounded, ?_, List.all_eq_true.mpr (generated_valid packet budget df), ?_, ?_, ?_⟩
  · intro empty
    exact (pieces_layout packet budget).nonempty (List.map_eq_nil_iff.mp empty)
  · apply List.all_eq_true.mpr
    intro part member
    obtain ⟨piece, belongs, same⟩ := List.mem_map.mp member
    subst part
    exact decide_eq_true (pieces_fits packet budget piece belongs)
  · apply List.all_eq_true.mpr
    intro part member
    obtain ⟨piece, _, same⟩ := List.mem_map.mp member
    subst part
    exact decide_eq_true rfl
  · apply (scanMatches_spec _ _).mpr
    rw [generated_sorted packet budget df bounded, generated_projection packet budget df bounded]
    exact (pieces_layout packet budget).scan

structure CertifiedGenerated (packet : IPv4.Packet) (budget : Budget) (df : Bool)
    extends CertifiedFamily packet budget df where
  generated : fragments = generatedFragments packet budget df

def generate (packet : IPv4.Packet) (budget : Budget) (df : Bool) (bounded : packet.Encodable) :
    CertifiedGenerated packet budget df :=
  ⟨⟨generatedFragments packet budget df, generated_accepts packet budget df bounded⟩, rfl⟩

def checkGenerated (packet : IPv4.Packet) (budget : Budget) (df : Bool) :
    Except String (CertifiedGenerated packet budget df) :=
  if bounded : packet.Encodable then .ok (generate packet budget df bounded)
  else .error "The IPv4 datagram exceeds its total-length field."

namespace CertifiedGenerated

variable {packet : IPv4.Packet} {budget : Budget} {df : Bool}

theorem layout (result : CertifiedGenerated packet budget df) :
    Layout 0 packet.payload (result.fragments.map asPiece) := by
  rw [result.generated, generated_projection packet budget df result.bounded]
  exact pieces_layout packet budget

theorem payload (result : CertifiedGenerated packet budget df) :
    result.fragments.flatMap (·.packet.payload) = packet.payload := by
  simpa only [List.flatMap_map, Function.comp_def, asPiece] using result.layout.payload

theorem encoded (result : CertifiedGenerated packet budget df) (part : IPv4Fragment.Decoded)
    (member : part ∈ result.fragments) : IPv4InputFragment.encodeDecoded part = .ok (fragmentBytes part) := by
  have padded := result.toCertifiedFamily.encoded part member
  have noPadding : part.padding = [] := by
    rw [result.generated] at member
    obtain ⟨piece, _, same⟩ := List.mem_map.mp member
    subst part
    rfl
  simpa only [noPadding, List.append_nil] using padded

theorem decoded (result : CertifiedGenerated packet budget df) (part : IPv4Fragment.Decoded)
    (member : part ∈ result.fragments) : IPv4InputFragment.decode (fragmentBytes part) = .ok part :=
  IPv4InputFragment.decode_encodeDecoded part _ (result.encoded part member)

theorem fits (result : CertifiedGenerated packet budget df) (part : IPv4Fragment.Decoded)
    (member : part ∈ result.fragments) : part.packet.wireLength ≤ budget.val := result.toCertifiedFamily.fits part member

theorem metadata (result : CertifiedGenerated packet budget df) (part : IPv4Fragment.Decoded)
    (member : part ∈ result.fragments) :
    IPv4Fragmentation.metadata part = { outputPacket packet df with payload := [] } := result.common part member

theorem reassembled (result : CertifiedGenerated packet budget df) :
    reassemble result.fragments = .ok (outputPacket packet df) := result.toCertifiedFamily.reassembled

end CertifiedGenerated

end Netlib.Protocol.IPv4Refragmentation
