import Netlib.Protocol.IPv4Fragment

/-!
# MTU fragmentation and strict reassembly

The selected MTU is at least 68 bytes. Fragmentation splits the complete IP payload.
Reassembly rejects overlaps, gaps, duplicate parts, and inconsistent metadata.
It does not model native overlap resolution, timers, or resource eviction.
-/

namespace Netlib.Protocol.IPv4Fragmentation

abbrev MTU := { value : Nat // 68 ≤ value ∧ value < 65536 }

def Allowed (packet : IPv4.Packet) (mtu : MTU) : Prop := packet.dontFragment = true → packet.wireLength ≤ mtu.val

instance (packet : IPv4.Packet) (mtu : MTU) : Decidable (Allowed packet mtu) := by unfold Allowed; infer_instance

def capacity (mtu : MTU) : Nat := ((mtu.val - 20) / 8) * 8

def payloadLimit (mtu : MTU) : Nat := mtu.val - 20

theorem capacity_positive (mtu : MTU) : 0 < capacity mtu := by
  have minimum := mtu.property.1
  unfold capacity
  omega

theorem capacity_aligned (mtu : MTU) : capacity mtu % 8 = 0 := by simp [capacity]

theorem capacity_fits (mtu : MTU) : capacity mtu + 20 ≤ mtu.val := by
  have minimum := mtu.property.1
  unfold capacity
  omega

theorem capacity_le_payloadLimit (mtu : MTU) : capacity mtu ≤ payloadLimit mtu := by
  have fits := capacity_fits mtu
  unfold payloadLimit
  omega

structure Piece where
  start : Nat
  data : List UInt8
  more : Bool
  deriving Repr, BEq, DecidableEq

def chunks (size : Nat) (positive : 0 < size) (finalLimit : Nat) (minimum : size ≤ finalLimit)
    (start : Nat) (data : List UInt8) : List Piece :=
  if data.length ≤ finalLimit then [⟨start, data, false⟩]
  else ⟨start, data.take size, true⟩ :: chunks size positive finalLimit minimum (start + size) (data.drop size)
termination_by data.length
decreasing_by simp only [List.length_drop]; omega

inductive Layout : Nat → List UInt8 → List Piece → Prop
  | last (start : Nat) (data : List UInt8) : Layout start data [⟨start, data, false⟩]
  | cons (start : Nat) (first rest : List UInt8) (tail : List Piece)
      (positive : 0 < first.length) (aligned : first.length % 8 = 0)
      (next : Layout (start + first.length) rest tail) :
      Layout start (first ++ rest) (⟨start, first, true⟩ :: tail)

theorem chunks_layout (size : Nat) (positive : 0 < size) (aligned : size % 8 = 0)
    (finalLimit : Nat) (minimum : size ≤ finalLimit) (start : Nat) (data : List UInt8) :
    Layout start data (chunks size positive finalLimit minimum start data) := by
  fun_induction chunks size positive finalLimit minimum start data with
  | case1 start data fitting => exact .last _ _
  | case2 start data large ih =>
    have length : (data.take size).length = size := by rw [List.length_take, Nat.min_eq_left (by omega : size ≤ data.length)]
    have built := Layout.cons start (data.take size) (data.drop size)
      (chunks size positive finalLimit minimum (start + size) (data.drop size))
      (by rw [length]; exact positive) (by rw [length]; exact aligned)
      (by simpa only [length] using ih)
    simpa only [List.take_append_drop] using built

theorem chunks_fits (size : Nat) (positive : 0 < size) (finalLimit : Nat) (minimum : size ≤ finalLimit)
    (start : Nat) (data : List UInt8) :
    ∀ piece ∈ chunks size positive finalLimit minimum start data, piece.data.length ≤ finalLimit := by
  fun_induction chunks size positive finalLimit minimum start data with
  | case1 start data fitting => simp_all
  | case2 start data large ih =>
    intro piece member
    rcases List.mem_cons.mp member with rfl | member
    · change (data.take size).length ≤ finalLimit
      rw [List.length_take]
      exact Nat.le_trans (Nat.min_le_left size data.length) minimum
    · exact ih piece member

theorem chunks_positive (size : Nat) (positive : 0 < size) (finalLimit : Nat) (minimum : size ≤ finalLimit)
    (start : Nat) (data : List UInt8) (nonempty : data ≠ []) :
    ∀ piece ∈ chunks size positive finalLimit minimum start data, piece.data ≠ [] := by
  fun_induction chunks size positive finalLimit minimum start data with
  | case1 start data fitting => simp_all
  | case2 start data large ih =>
    intro piece member
    rcases List.mem_cons.mp member with rfl | member
    · have length : (data.take size).length = size := by rw [List.length_take, Nat.min_eq_left (by omega : size ≤ data.length)]
      intro empty
      change data.take size = [] at empty
      rw [empty] at length
      simp only [List.length_nil] at length
      omega
    · apply ih (by intro empty; have := congrArg List.length empty; simp at this; omega) piece member

theorem Layout.nonempty (layout : Layout start data pieces) : pieces ≠ [] := by cases layout <;> simp

theorem Layout.payload (layout : Layout start data pieces) : pieces.flatMap Piece.data = data := by
  induction layout with
  | last => simp
  | cons start first rest tail positive aligned next ih => simpa only [List.flatMap_cons] using congrArg (first ++ ·) ih

theorem Layout.bounds (layout : Layout start data pieces) :
    ∀ piece ∈ pieces, start ≤ piece.start ∧ piece.start + piece.data.length ≤ start + data.length := by
  induction layout with
  | last => simp
  | cons start first rest tail positive aligned next ih =>
    intro piece member
    rcases List.mem_cons.mp member with rfl | member
    · simp
    · have bound := ih piece member
      simp only [List.length_append]
      omega

theorem Layout.aligned (layout : Layout start data pieces) (initial : start % 8 = 0) :
    ∀ piece ∈ pieces, piece.start % 8 = 0 := by
  induction layout with
  | last => simp_all
  | cons start first rest tail positive aligned next ih =>
    intro piece member
    rcases List.mem_cons.mp member with rfl | member
    · exact initial
    · exact ih (by omega) piece member

theorem Layout.flags (layout : Layout start data pieces) :
    ∀ piece ∈ pieces, piece.more = true → piece.data ≠ [] ∧ piece.data.length % 8 = 0 := by
  induction layout with
  | last => simp
  | cons start first rest tail positive aligned next ih =>
    intro piece member more
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨by intro empty; change first = [] at empty; simp [empty] at positive, aligned⟩
    · exact ih piece member more

theorem Layout.sorted (layout : Layout start data pieces) :
    pieces.Pairwise (fun first second => first.start ≤ second.start) := by
  induction layout with
  | last => simp
  | cons start first rest tail positive aligned next ih =>
    apply List.pairwise_cons.mpr
    refine ⟨?_, ih⟩
    intro piece member
    have bound := next.bounds piece member
    simp only
    omega

theorem Layout.strictSorted (layout : Layout start data pieces) :
    pieces.Pairwise (fun first second => first.start < second.start) := by
  induction layout with
  | last => simp
  | cons start first rest tail positive aligned next ih =>
    apply List.pairwise_cons.mpr
    refine ⟨?_, ih⟩
    intro piece member
    have bound := next.bounds piece member
    simp only
    omega

private theorem unique_key {α : Type} (key : α → Nat) (values : List α)
    (ordered : values.Pairwise (fun first second => key first < key second)) :
    ∀ first ∈ values, ∀ second ∈ values, key first = key second → first = second := by
  induction values with
  | nil => simp
  | cons head tail ih =>
    obtain ⟨before, orderedTail⟩ := List.pairwise_cons.mp ordered
    intro first firstMember second secondMember same
    rcases List.mem_cons.mp firstMember with firstEq | firstTail
    · subst first
      rcases List.mem_cons.mp secondMember with secondEq | secondTail
      · exact secondEq.symm
      · have less := before second secondTail
        omega
    · rcases List.mem_cons.mp secondMember with secondEq | secondTail
      · subst second
        have less := before first firstTail
        omega
      · exact ih orderedTail first firstTail second secondTail same

def scan (expected : Nat) : List Piece → Except String (List UInt8)
  | [] => .error "The fragment family has no final part."
  | first :: rest =>
    if first.start = expected then
      if first.more then
        if rest.isEmpty then .error "The fragment family has no final part."
        else (scan (expected + first.data.length) rest).map (first.data ++ ·)
      else if rest.isEmpty then .ok first.data
      else .error "A final fragment is followed by additional parts."
    else .error "Fragment offsets contain a gap, overlap, or duplicate."

theorem Layout.scan (layout : Layout start data pieces) : scan start pieces = .ok data := by
  induction layout with
  | last => simp [Netlib.Protocol.IPv4Fragmentation.scan]
  | cons start first rest tail positive aligned next ih =>
    have nonempty := next.nonempty
    simp [Netlib.Protocol.IPv4Fragmentation.scan, ih, nonempty, Except.map]

theorem scan_layout (parts : List Piece) (expected : Nat) (data : List UInt8)
    (accepted : scan expected parts = .ok data)
    (valid : ∀ piece ∈ parts, piece.more = true → piece.data ≠ [] ∧ piece.data.length % 8 = 0) :
    Layout expected data parts := by
  induction parts generalizing expected data with
  | nil => simp [scan] at accepted
  | cons first rest ih =>
    rcases first with ⟨start, headData, more⟩
    by_cases same : start = expected
    · subst start
      cases more with
      | false =>
        cases rest with
        | nil =>
          simp [scan] at accepted
          cases accepted
          exact .last _ _
        | cons next tail => simp [scan] at accepted
      | true =>
        cases rest with
        | nil => simp [scan] at accepted
        | cons next tail =>
          rw [scan] at accepted
          simp only [Bool.false_eq_true, List.isEmpty_cons, ite_true, ite_false] at accepted
          cases found : scan (expected + headData.length) (next :: tail) with
          | error error => simp [found, Except.map] at accepted
          | ok tailData =>
            simp [found, Except.map] at accepted
            cases accepted
            have headValid := valid ⟨expected, headData, true⟩ (by simp) rfl
            apply Layout.cons expected headData tailData (next :: tail)
            · exact List.length_pos_iff.mpr headValid.1
            · exact headValid.2
            · exact ih _ _ found (fun piece member => valid piece (List.mem_cons_of_mem _ member))
    · simp [scan, same] at accepted

def pieces (packet : IPv4.Packet) (mtu : MTU) : List Piece :=
  if packet.wireLength ≤ mtu.val then [⟨0, packet.payload, false⟩]
  else chunks (capacity mtu) (capacity_positive mtu) (payloadLimit mtu) (capacity_le_payloadLimit mtu) 0 packet.payload

theorem pieces_layout (packet : IPv4.Packet) (mtu : MTU) : Layout 0 packet.payload (pieces packet mtu) := by
  unfold pieces
  split
  · exact .last _ _
  · exact chunks_layout _ _ (capacity_aligned mtu) _ _ _ _

theorem pieces_fits (packet : IPv4.Packet) (mtu : MTU) :
    ∀ piece ∈ pieces packet mtu, piece.data.length + 20 ≤ mtu.val := by
  unfold pieces
  split
  · intro piece member
    simp only [List.mem_singleton] at member
    subst piece
    assumption
  · intro piece member
    have size := chunks_fits _ (capacity_positive mtu) _ (capacity_le_payloadLimit mtu) 0 packet.payload piece member
    have minimum := mtu.property.1
    unfold payloadLimit at size
    omega

theorem pieces_positive (packet : IPv4.Packet) (mtu : MTU) :
    ∀ piece ∈ pieces packet mtu, piece.start ≠ 0 → piece.data ≠ [] := by
  unfold pieces
  split
  · simp
  · rename_i large
    have nonempty : packet.payload ≠ [] := by
      intro empty
      have minimum := mtu.property.1
      simp [IPv4.Packet.wireLength, empty] at large
      omega
    exact fun piece member _ =>
      chunks_positive _ (capacity_positive mtu) _ (capacity_le_payloadLimit mtu) _ _ nonempty piece member

theorem pieces_df (packet : IPv4.Packet) (mtu : MTU) (allowed : Allowed packet mtu) (df : packet.dontFragment = true) :
    pieces packet mtu = [⟨0, packet.payload, false⟩] := by
  exact ite_eq_left (allowed df)

def fragmentPacket (packet : IPv4.Packet) (piece : Piece) : IPv4Fragment.Packet :=
  ⟨{ packet with payload := piece.data }, piece.more,
    ⟨(piece.start / 8) % 8192, Nat.mod_lt _ (by decide)⟩⟩

theorem fragment_offset (packet : IPv4.Packet) (mtu : MTU) (bounded : packet.Encodable)
    (piece : Piece) (member : piece ∈ pieces packet mtu) :
    (fragmentPacket packet piece).offset.val * 8 = piece.start := by
  have limits := (pieces_layout packet mtu).bounds piece member
  have aligned := (pieces_layout packet mtu).aligned (by decide) piece member
  have maximum : packet.payload.length + 20 < 65536 := bounded
  have fits : piece.start / 8 < 8192 := by omega
  change (piece.start / 8 % 8192) * 8 = piece.start
  rw [Nat.mod_eq_of_lt fits]
  omega

theorem fragment_encodable (packet : IPv4.Packet) (mtu : MTU) (_bounded : packet.Encodable) (allowed : Allowed packet mtu)
    (piece : Piece) (member : piece ∈ pieces packet mtu) : (fragmentPacket packet piece).Encodable := by
  constructor
  · have fits := pieces_fits packet mtu piece member
    have maximum := mtu.property.2
    change piece.data.length + 20 < 65536
    omega
  · refine ⟨?_, ?_, ?_⟩
    · intro df
      have only := pieces_df packet mtu allowed df
      rw [only] at member
      simp only [List.mem_singleton] at member
      subst piece
      exact ⟨rfl, by simp [fragmentPacket]⟩
    · exact (pieces_layout packet mtu).flags piece member
    · intro offset
      apply pieces_positive packet mtu piece member
      intro zero
      apply offset
      simp [fragmentPacket, zero]

def fragmentDecoded (packet : IPv4.Packet) (piece : Piece) : IPv4Fragment.Decoded :=
  ⟨fragmentPacket packet piece, IPv4Fragment.computedChecksum (fragmentPacket packet piece), []⟩

def fragmentBytes (fragment : IPv4Fragment.Decoded) : List UInt8 :=
  IPv4Fragment.headerBytes fragment.packet fragment.checksum ++ fragment.packet.payload

def generatedFragments (packet : IPv4.Packet) (mtu : MTU) : List IPv4Fragment.Decoded :=
  (pieces packet mtu).map (fragmentDecoded packet)

def asPiece (fragment : IPv4Fragment.Decoded) : Piece :=
  ⟨fragment.packet.offset.val * 8, fragment.packet.payload, fragment.packet.moreFragments⟩

def sort (fragments : List IPv4Fragment.Decoded) : List IPv4Fragment.Decoded :=
  fragments.mergeSort (fun first second => decide ((asPiece first).start ≤ (asPiece second).start))

def metadata (fragment : IPv4Fragment.Decoded) : IPv4.Packet := { fragment.packet.toPacket with payload := [] }

def validFragment (fragment : IPv4Fragment.Decoded) : Bool :=
  decide fragment.packet.Encodable && InternetChecksum.valid (IPv4Fragment.headerBytes fragment.packet fragment.checksum)

def reassemble (fragments : List IPv4Fragment.Decoded) : Except String IPv4.Packet :=
  match sort fragments with
  | [] => .error "Supply at least one fragment."
  | first :: rest => do
    if !(first :: rest).all validFragment then throw "A fragment has invalid fields or checksum."
    if !(first :: rest).all (fun fragment => decide (metadata fragment = metadata first)) then
      throw "The fragment family has inconsistent metadata."
    let payload ← scan 0 ((first :: rest).map asPiece)
    let packet := { metadata first with payload }
    if packet.Encodable then return packet
    else throw "The reassembled IPv4 datagram exceeds its total-length field."

theorem generated_projection (packet : IPv4.Packet) (mtu : MTU) (bounded : packet.Encodable) :
    (generatedFragments packet mtu).map asPiece = pieces packet mtu := by
  unfold generatedFragments
  rw [List.map_map]
  have same : (pieces packet mtu).map (asPiece ∘ fragmentDecoded packet) = (pieces packet mtu).map id := by
    apply List.map_congr_left
    intro piece member
    have offset := fragment_offset packet mtu bounded piece member
    change (Piece.mk ((fragmentPacket packet piece).offset.val * 8) piece.data piece.more) = piece
    rw [offset]
  simpa only [List.map_id] using same

theorem generated_sorted (packet : IPv4.Packet) (mtu : MTU) (bounded : packet.Encodable) :
    sort (generatedFragments packet mtu) = generatedFragments packet mtu := by
  apply List.mergeSort_of_pairwise
  have sorted := (pieces_layout packet mtu).sorted
  rw [← generated_projection packet mtu bounded] at sorted
  have projected := List.pairwise_map.mp sorted
  exact projected.imp (fun relation => by simpa only [decide_eq_true_eq] using relation)

theorem sort_sorted (fragments : List IPv4Fragment.Decoded) :
    (sort fragments).Pairwise (fun first second => (asPiece first).start ≤ (asPiece second).start) := by
  have sorted := List.pairwise_mergeSort
    (le := fun first second : IPv4Fragment.Decoded => decide ((asPiece first).start ≤ (asPiece second).start))
    (fun first second third before after => by simp only [decide_eq_true_eq] at *; omega)
    (fun first second => by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega) fragments
  exact sorted.imp (fun relation => of_decide_eq_true relation)

theorem sort_permutation (left right : List IPv4Fragment.Decoded) (permutation : left.Perm right)
    (unique : ∀ first ∈ right, ∀ second ∈ right, (asPiece first).start = (asPiece second).start → first = second) :
    sort left = sort right := by
  apply List.Perm.eq_of_pairwise _ (sort_sorted left) (sort_sorted right)
    ((List.mergeSort_perm left _).trans (permutation.trans (List.mergeSort_perm right _).symm))
  intro first second firstMember secondMember before after
  apply unique first (permutation.subset (List.mem_mergeSort.mp firstMember)) second (List.mem_mergeSort.mp secondMember)
  omega

theorem generated_metadata (packet : IPv4.Packet) (mtu : MTU) :
    ∀ part ∈ generatedFragments packet mtu, metadata part = { packet with payload := [] } := by
  intro part member
  unfold generatedFragments at member
  obtain ⟨piece, belongs, same⟩ := List.mem_map.mp member
  subst part
  rfl

theorem reassemble_ordered (packet : IPv4.Packet) (fragments : List IPv4Fragment.Decoded)
    (nonempty : fragments ≠ []) (sorted : sort fragments = fragments)
    (checked : ∀ part ∈ fragments, validFragment part = true)
    (common : ∀ part ∈ fragments, metadata part = { packet with payload := [] })
    (joined : scan 0 (fragments.map asPiece) = .ok packet.payload) (bounded : packet.Encodable) :
    reassemble fragments = .ok packet := by
  cases fragments with
  | nil => exact False.elim (nonempty rfl)
  | cons first rest =>
    have allChecked : (first :: rest).all validFragment = true := List.all_eq_true.mpr checked
    have firstCommon := common first (by simp)
    have allCommon : (first :: rest).all (fun part => decide (metadata part = metadata first)) = true := by
      apply List.all_eq_true.mpr
      intro part member
      simp only [decide_eq_true_eq]
      exact (common part member).trans firstCommon.symm
    simp only [reassemble, sorted, allChecked, allCommon, Bool.not_true, Bool.false_eq_true, ite_false,
      joined, bind, Except.bind]
    rw [firstCommon]
    simp only [bounded, ite_true, pure, Except.pure]

structure Certified (packet : IPv4.Packet) (mtu : MTU) where
  fragments : List IPv4Fragment.Decoded
  bytes : List (List UInt8)
  generated : fragments = generatedFragments packet mtu
  wire : bytes = fragments.map fragmentBytes
  bounded : packet.Encodable
  allowed : Allowed packet mtu

def fragment (packet : IPv4.Packet) (mtu : MTU) (bounded : packet.Encodable) (allowed : Allowed packet mtu) :
    Certified packet mtu :=
  ⟨generatedFragments packet mtu, (generatedFragments packet mtu).map fragmentBytes, rfl, rfl, bounded, allowed⟩

def check (packet : IPv4.Packet) (mtu : MTU) : Except String (Certified packet mtu) :=
  if bounded : packet.Encodable then
    if allowed : Allowed packet mtu then .ok (fragment packet mtu bounded allowed)
    else .error "An oversized DF packet cannot be fragmented."
  else .error "The IPv4 datagram exceeds its total-length field."

namespace Certified

variable {packet : IPv4.Packet} {mtu : MTU}

def packets (result : Certified packet mtu) : List IPv4Fragment.Packet := result.fragments.map (·.packet)

theorem layout (result : Certified packet mtu) : Layout 0 packet.payload (result.fragments.map asPiece) := by
  rw [result.generated, generated_projection packet mtu result.bounded]
  exact pieces_layout packet mtu

theorem nonempty (result : Certified packet mtu) : result.fragments ≠ [] := by
  rw [result.generated]
  intro empty
  exact (pieces_layout packet mtu).nonempty (List.map_eq_nil_iff.mp empty)

theorem encoded (result : Certified packet mtu) (part : IPv4Fragment.Decoded) (member : part ∈ result.fragments) :
    IPv4Fragment.encodeDecoded part = .ok (fragmentBytes part) := by
  rw [result.generated] at member
  unfold generatedFragments at member
  obtain ⟨piece, belongs, same⟩ := List.mem_map.mp member
  subst part
  have bounded := fragment_encodable packet mtu result.bounded result.allowed piece belongs
  have checked := IPv4Fragment.computedChecksum_valid (fragmentPacket packet piece)
  simp only [IPv4Fragment.encodeDecoded, fragmentDecoded, bounded, ite_true, checked, List.append_nil]
  rfl

theorem decoded (result : Certified packet mtu) (part : IPv4Fragment.Decoded) (member : part ∈ result.fragments) :
    IPv4Fragment.decode (fragmentBytes part) = .ok part :=
  IPv4Fragment.decode_encodeDecoded part _ (result.encoded part member)

theorem fits (result : Certified packet mtu) (part : IPv4Fragment.Decoded) (member : part ∈ result.fragments) :
    part.packet.wireLength ≤ mtu.val := by
  rw [result.generated] at member
  unfold generatedFragments at member
  obtain ⟨piece, belongs, same⟩ := List.mem_map.mp member
  subst part
  exact pieces_fits packet mtu piece belongs

theorem payload (result : Certified packet mtu) : result.fragments.flatMap (·.packet.payload) = packet.payload := by
  rw [result.generated]
  simpa only [generatedFragments, List.flatMap_map, Function.comp_def, fragmentDecoded, fragmentPacket]
    using (pieces_layout packet mtu).payload

theorem metadata (result : Certified packet mtu) (part : IPv4Fragment.Decoded) (member : part ∈ result.fragments) :
    Netlib.Protocol.IPv4Fragmentation.metadata part = { packet with payload := [] } := by
  rw [result.generated] at member
  exact generated_metadata packet mtu part member

theorem no_split_fits (result : Certified packet mtu) (fitting : packet.wireLength ≤ mtu.val) :
    result.fragments = [fragmentDecoded packet ⟨0, packet.payload, false⟩] := by
  rw [result.generated]
  simp only [generatedFragments, pieces, fitting, ite_true, List.map_singleton]

theorem no_split_df (result : Certified packet mtu) (df : packet.dontFragment = true) :
    result.fragments = [fragmentDecoded packet ⟨0, packet.payload, false⟩] := by
  rw [result.generated]
  simp only [generatedFragments, pieces_df packet mtu result.allowed df, List.map_singleton]

theorem reassembled (result : Certified packet mtu) : reassemble result.fragments = .ok packet := by
  apply reassemble_ordered packet result.fragments result.nonempty
  · rw [result.generated]
    exact generated_sorted packet mtu result.bounded
  · intro part member
    obtain ⟨bounded, checked⟩ := IPv4Fragment.encodeDecoded_valid part _ (result.encoded part member)
    simp only [validFragment, bounded, decide_true, Bool.true_and, checked]
  · rw [result.generated]
    exact generated_metadata packet mtu
  · rw [result.generated, generated_projection packet mtu result.bounded]
    exact (pieces_layout packet mtu).scan
  · exact result.bounded

theorem reassembled_perm (result : Certified packet mtu) (family : List IPv4Fragment.Decoded)
    (permutation : family.Perm result.fragments) : reassemble family = .ok packet := by
  have strict := (pieces_layout packet mtu).strictSorted
  rw [← generated_projection packet mtu result.bounded, ← result.generated] at strict
  have ordered : result.fragments.Pairwise (fun first second => (asPiece first).start < (asPiece second).start) :=
    (List.pairwise_map (f := asPiece) (R := fun first second : Piece => first.start < second.start)).mp strict
  have unique := unique_key (fun part : IPv4Fragment.Decoded => (asPiece part).start) result.fragments
    ordered
  have sorted := sort_permutation family result.fragments permutation unique
  unfold reassemble
  rw [sorted]
  exact result.reassembled

end Certified

end Netlib.Protocol.IPv4Fragmentation
