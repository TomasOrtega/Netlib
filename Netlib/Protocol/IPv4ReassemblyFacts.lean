import Netlib.Protocol.IPv4Reassembly

namespace Netlib.Protocol.IPv4Reassembly

@[simp] theorem normalize_fragment (fragment : IPv4Fragment.Decoded) :
    (normalize fragment).fragment = fragment := rfl

@[simp] theorem normalize_start (fragment : IPv4Fragment.Decoded) :
    (normalize fragment).start = fragment.packet.offset.val * 8 := rfl

theorem normalize_prefix (fragment : IPv4Fragment.Decoded) :
    (normalize fragment).data <+: fragment.packet.payload := by
  unfold normalize
  split
  · exact List.take_prefix _ _
  · exact List.prefix_refl _

theorem normalize_length (fragment : IPv4Fragment.Decoded) :
    (normalize fragment).data.length ≤ fragment.packet.payload.length := by
  exact (normalize_prefix fragment).length_le

theorem normalize_more_length (fragment : IPv4Fragment.Decoded) (more : fragment.packet.moreFragments = true) :
    (normalize fragment).data.length = fragment.packet.payload.length / 8 * 8 := by
  simp only [normalize, more, ↓reduceIte, List.length_take]
  apply Nat.min_eq_left
  omega

theorem normalize_more_aligned (fragment : IPv4Fragment.Decoded) (more : fragment.packet.moreFragments = true) :
    (normalize fragment).data.length % 8 = 0 := by
  rw [normalize_more_length _ more]
  omega

@[simp] theorem Run.append_pieces (run : Run) (piece : Piece) :
    (run.append piece).pieces = run.pieces ++ [piece] := by simp [Run.append, Run.pieces]

@[simp] theorem insert_pieces (piece : Piece) (runs : List Run) :
    ((insert piece runs).flatMap Run.pieces).Perm (piece :: runs.flatMap Run.pieces) := by
  induction runs with
  | nil => simp [IPv4Reassembly.insert, Run.pieces]
  | cons run rest ih =>
    rw [IPv4Reassembly.insert.eq_def]
    by_cases before : piece.start < run.start
    · simp [before, Run.pieces]
    · simp only [before, ↓reduceIte]
      cases rest with
      | nil =>
        by_cases adjacent : piece.start = run.stop
        · simp [adjacent]
        · simpa [adjacent, Run.pieces] using
            (List.perm_append_comm (l₁ := run.pieces) (l₂ := [piece]))
      | cons next tail =>
        simp only [List.flatMap_cons]
        exact (List.Perm.append_left run.pieces ih).trans List.perm_middle

@[simp] theorem insert_mem (piece value : Piece) (runs : List Run) :
    value ∈ (insert piece runs).flatMap Run.pieces ↔ value = piece ∨ value ∈ runs.flatMap Run.pieces := by
  rw [(insert_pieces piece runs).mem_iff]
  simp

inductive Coverage : Nat → List Piece → Prop
  | nil (start : Nat) : Coverage start []
  | cons (piece : Piece) (rest : List Piece) (tail : Coverage piece.stop rest) :
      Coverage piece.start (piece :: rest)

theorem joinAt_payload (pieces : List Piece) (start : Nat) (payload : List UInt8)
    (joined : joinAt start pieces = some payload) :
    payload = pieces.flatMap (·.data) ∧ Coverage start pieces := by
  induction pieces generalizing start payload with
  | nil => simp [joinAt] at joined; subst payload; exact ⟨rfl, .nil _⟩
  | cons piece rest ih =>
    unfold joinAt at joined
    split at joined
    · rename_i same
      cases tail : joinAt piece.stop rest with
      | none => simp [tail] at joined
      | some data =>
        simp only [tail, Option.map_some, Option.some.injEq] at joined
        obtain ⟨bytes, covered⟩ := ih _ _ tail
        subst start
        exact ⟨by rw [← joined, bytes]; rfl, .cons _ _ covered⟩
    · cases joined

theorem Coverage.joinAt (coverage : Coverage start pieces) :
    joinAt start pieces = some (pieces.flatMap (·.data)) := by
  induction coverage with
  | nil => rfl
  | cons piece rest tail ih => simp [IPv4Reassembly.joinAt, ih]

theorem Coverage.before (coverage : Coverage start pieces) :
    ∀ piece ∈ pieces, start ≤ piece.start := by
  induction coverage with
  | nil => simp
  | cons piece rest tail ih =>
    intro value member
    rcases List.mem_cons.mp member with rfl | member
    · exact Nat.le_refl _
    · have bound := ih value member
      unfold Piece.stop at bound
      omega

theorem Coverage.strictSorted (coverage : Coverage start pieces)
    (positive : ∀ piece ∈ pieces, 0 < piece.data.length) :
    pieces.Pairwise (fun first second => first.start < second.start) := by
  induction coverage with
  | nil => simp
  | cons piece rest tail ih =>
    apply List.pairwise_cons.mpr
    constructor
    · intro value member
      have bound := tail.before value member
      have nonempty := positive piece (by simp)
      unfold Piece.stop at bound
      omega
    · exact ih (fun value member => positive value (by simp [member]))

theorem starts_unique (pieces : List Piece)
    (ordered : pieces.Pairwise (fun first second => first.start < second.start)) :
    ∀ first ∈ pieces, ∀ second ∈ pieces, first.start = second.start → first = second := by
  induction pieces with
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

theorem joined_permutation (first second : List Piece) (left right : List UInt8)
    (leftJoined : joinAt 0 first = some left) (rightJoined : joinAt 0 second = some right)
    (permutation : first.Perm second) (positive : ∀ piece ∈ first, 0 < piece.data.length) : left = right := by
  obtain ⟨leftPayload, leftCovered⟩ := joinAt_payload _ _ _ leftJoined
  obtain ⟨rightPayload, rightCovered⟩ := joinAt_payload _ _ _ rightJoined
  have leftSorted := leftCovered.strictSorted positive
  have rightSorted := rightCovered.strictSorted (fun piece member => positive piece (permutation.mem_iff.mpr member))
  have same : first = second := by
    apply List.Perm.eq_of_pairwise _
      (leftSorted.imp (fun less => Nat.le_of_lt less)) (rightSorted.imp (fun less => Nat.le_of_lt less)) permutation
    intro a b aMember bMember before after
    exact starts_unique first leftSorted a aMember b (permutation.mem_iff.mpr bMember) (by omega)
  rw [leftPayload, rightPayload, same]

@[simp] theorem State.age_member (state : State) (now : Nat) (queue : Queue) :
    queue ∈ (state.age now).queues ↔ queue ∈ state.queues ∧ now < queue.expires := by
  simp [State.age]

@[simp] theorem State.erase_member (state : State) (wanted : Key) (queue : Queue) :
    queue ∈ (state.erase wanted).queues ↔ queue ∈ state.queues ∧ queue.key ≠ wanted := by
  simp [State.erase]

@[simp] theorem State.put_member (state : State) (queue value : Queue) :
    value ∈ (state.put queue).queues ↔ value = queue ∨ value ∈ state.queues ∧ value.key ≠ queue.key := by
  simp [State.put]

theorem State.lookup_key (state : State) (wanted : Key) (queue : Queue)
    (found : state.lookup wanted = some queue) : queue.key = wanted :=
  of_decide_eq_true (List.find?_some (p := fun value : Queue => decide (value.key = wanted)) found)

theorem State.lookup_member (state : State) (wanted : Key) (queue : Queue)
    (found : state.lookup wanted = some queue) : queue ∈ state.queues := List.mem_of_find?_eq_some found

@[simp] theorem State.erase_lookup (state : State) (wanted : Key) : (state.erase wanted).lookup wanted = none := by
  apply List.find?_eq_none.mpr
  intro queue member
  have absent := (State.erase_member _ _ _).mp member
  simp [absent.2]

@[simp] theorem State.put_lookup (state : State) (queue : Queue) : (state.put queue).lookup queue.key = some queue := by
  simp [State.lookup, State.put]

theorem State.expired_absent (state : State) (now : Nat) (queue : Queue) (expired : queue.expires ≤ now) :
    queue ∉ (state.age now).queues := by
  simp only [State.age_member]
  omega

@[simp] theorem store_key (queue : Queue) (piece : Piece) : (store queue piece).key = queue.key := rfl
@[simp] theorem store_expires (queue : Queue) (piece : Piece) : (store queue piece).expires = queue.expires := rfl

@[simp] theorem store_piece_member (queue : Queue) (piece value : Piece) :
    value ∈ (store queue piece).pieces ↔ value = piece ∨ value ∈ queue.pieces := by
  exact insert_mem _ _ _

theorem queuedLength_fields (queue next : Queue) (piece : Piece) (updated : queuedLength queue piece = some next) :
    next.key = queue.key ∧ next.expires = queue.expires ∧ next.runs = queue.runs ∧ next.first = queue.first ∧
      next.ecn = queue.ecn ∧ next.maxSize = queue.maxSize ∧ next.maxDFSize = queue.maxDFSize := by
  unfold queuedLength at updated
  split at updated
  · split at updated
    · cases updated
    · cases updated; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · split at updated
    · cases updated
    · cases updated; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

structure Queue.Valid (queue : Queue) : Prop where
  normalized : ∀ piece ∈ queue.pieces, piece = normalize piece.fragment
  nonempty : ∀ piece ∈ queue.pieces, 0 < piece.data.length
  fragmentBound : ∀ piece ∈ queue.pieces, piece.fragment.packet.wireLength < 65536
  fragmentKey : ∀ piece ∈ queue.pieces, IPv4Reassembly.key queue.key.domain piece.fragment = queue.key
  maximum : ∀ piece ∈ queue.pieces, piece.data.length + 20 ≤ queue.maxSize
  bounded : queue.maxSize < 65536
  df : queue.maxDFSize ≤ queue.maxSize
  first : ∀ header, queue.first = some header → 28 ≤ queue.maxSize ∧
    ∃ piece ∈ queue.pieces, piece.start = 0 ∧ header = piece.fragment.packet.toPacket

def State.Valid (state : State) : Prop := ∀ queue ∈ state.queues, queue.Valid

theorem State.initial_valid : State.initial.Valid := by simp [State.Valid, State.initial]

theorem Queue.fresh_valid (wanted : Key) (expires : Nat) :
    (⟨wanted, expires, [], 0, false, none, 0, 0, 0⟩ : Queue).Valid := by
  constructor <;> simp [Queue.pieces]

theorem State.age_valid (state : State) (now : Nat) (valid : state.Valid) : (state.age now).Valid := by
  intro queue member
  exact valid queue ((State.age_member _ _ _).mp member).1

theorem State.erase_valid (state : State) (wanted : Key) (valid : state.Valid) : (state.erase wanted).Valid := by
  intro queue member
  exact valid queue ((State.erase_member _ _ _).mp member).1

theorem State.put_valid (state : State) (queue : Queue) (valid : state.Valid) (inserted : queue.Valid) :
    (state.put queue).Valid := by
  intro value member
  rcases (State.put_member _ _ _).mp member with rfl | previous
  · exact inserted
  · exact valid value previous.1

theorem queuedLength_valid (queue next : Queue) (piece : Piece)
    (updated : queuedLength queue piece = some next) (valid : queue.Valid) : next.Valid := by
  unfold queuedLength at updated
  split at updated
  · split at updated
    · cases updated
    · cases updated; exact ⟨valid.normalized, valid.nonempty, valid.fragmentBound, valid.fragmentKey,
        valid.maximum, valid.bounded, valid.df, valid.first⟩
  · split at updated
    · cases updated
    · cases updated; exact ⟨valid.normalized, valid.nonempty, valid.fragmentBound, valid.fragmentKey,
        valid.maximum, valid.bounded, valid.df, valid.first⟩

theorem store_valid (queue : Queue) (piece : Piece) (valid : queue.Valid)
    (normalized : piece = normalize piece.fragment) (nonempty : 0 < piece.data.length)
    (bounded : piece.fragment.packet.wireLength < 65536)
    (same : key queue.key.domain piece.fragment = queue.key)
    (firstSize : piece.start = 0 → 28 ≤ piece.data.length + 20) : (store queue piece).Valid := by
  have sizeBound : piece.data.length + 20 < 65536 := by
    have prefixBound := normalize_length piece.fragment
    rw [← normalized] at prefixBound
    change piece.fragment.packet.payload.length + 20 < 65536 at bounded
    omega
  constructor
  · intro value member
    rcases (store_piece_member _ _ _).mp member with rfl | member
    · exact normalized
    · exact valid.normalized _ member
  · intro value member
    rcases (store_piece_member _ _ _).mp member with rfl | member
    · exact nonempty
    · exact valid.nonempty _ member
  · intro value member
    rcases (store_piece_member _ _ _).mp member with rfl | member
    · exact bounded
    · exact valid.fragmentBound _ member
  · intro value member
    rcases (store_piece_member _ _ _).mp member with rfl | member
    · exact same
    · exact valid.fragmentKey _ member
  · intro value member
    rcases (store_piece_member _ _ _).mp member with rfl | member
    · exact Nat.le_max_right _ _
    · exact Nat.le_trans (valid.maximum _ member) (Nat.le_max_left _ _)
  · change max queue.maxSize (piece.data.length + 20) < 65536
    exact Nat.max_lt.mpr ⟨valid.bounded, sizeBound⟩
  · change (if piece.fragment.packet.dontFragment then max queue.maxDFSize (piece.data.length + 20)
        else queue.maxDFSize) ≤ max queue.maxSize (piece.data.length + 20)
    have previous := valid.df
    split <;> omega
  · intro header found
    unfold store at found
    split at found
    · rename_i zero
      cases found
      exact ⟨Nat.le_trans (firstSize zero) (Nat.le_max_right _ _), piece,
        (store_piece_member _ _ _).mpr (Or.inl rfl), zero, rfl⟩
    · obtain ⟨minimum, old, member, zero, original⟩ := valid.first header found
      exact ⟨Nat.le_trans minimum (Nat.le_max_left _ _), old,
        (store_piece_member _ _ _).mpr (Or.inr member), zero, original⟩

theorem accept_valid (state : State) (queue : Queue) (piece : Piece)
    (stateValid : state.Valid) (queueValid : queue.Valid)
    (normalized : piece = normalize piece.fragment)
    (bounded : piece.fragment.packet.wireLength < 65536)
    (same : key queue.key.domain piece.fragment = queue.key)
    (firstSize : 0 < piece.data.length → piece.start = 0 → 28 ≤ piece.data.length + 20) :
    (accept state queue piece).state.Valid := by
  unfold accept
  split
  · exact state.erase_valid _ stateValid
  · rename_i nonempty
    split
    · exact state.put_valid _ stateValid queueValid
    · split
      · exact state.erase_valid _ stateValid
      · have positive : 0 < piece.data.length := by
          cases data : piece.data with
          | nil => simp [data] at nonempty
          | cons head tail => simp
        have stored := store_valid queue piece queueValid normalized positive bounded same (firstSize positive)
        dsimp only
        cases done : (store queue piece).complete with
        | waiting => exact state.put_valid _ stateValid stored
        | rejected reason => exact state.erase_valid _ stateValid
        | accepted output => exact state.erase_valid _ stateValid

theorem process_valid (policy : Policy) (before : State) (now : Nat) (domain : Domain)
    (fragment : IPv4Fragment.Decoded) (valid : before.Valid) (bounded : fragment.packet.wireLength < 65536) :
    (process policy before now domain fragment).state.Valid := by
  let state : State := { before.age now with lastTime := now }
  let wanted := key domain fragment
  let old := (state.lookup wanted).getD { key := wanted, expires := now + policy.timeout }
  have stateValid : state.Valid := before.age_valid now valid
  have oldValid : old.Valid := by
    cases found : state.lookup wanted with
    | none => simpa only [old, found, Option.getD_none] using Queue.fresh_valid wanted (now + policy.timeout)
    | some queue =>
      simpa only [old, found, Option.getD_some] using stateValid queue (state.lookup_member _ _ found)
  have oldKey : old.key = wanted := by
    cases found : state.lookup wanted with
    | none => simp [old, found]
    | some queue => simpa only [old, found, Option.getD_some] using state.lookup_key _ _ found
  change (if !fragment.packet.moreFragments && decide (fragment.packet.offset.val = 0) then
      (⟨state, .whole, some ⟨fragment.packet.toPacket, [⟨fragment, fragment.packet.payload⟩], 0, 0, false⟩⟩ : Result)
    else match queuedLength old (normalize fragment) with
      | none => ⟨state.erase wanted, .inconsistentLength, none⟩
      | some queue => accept state queue (normalize fragment)).state.Valid
  split
  · exact stateValid
  · rename_i fragmented
    split
    · exact state.erase_valid _ stateValid
    · rename_i queue lengthUpdated
      have fields := queuedLength_fields _ _ _ lengthUpdated
      apply accept_valid _ _ _ stateValid (queuedLength_valid _ _ _ lengthUpdated oldValid) rfl bounded
      · rw [fields.1, oldKey]
        rfl
      · intro positive zero
        have offset : fragment.packet.offset.val = 0 := by
          change fragment.packet.offset.val * 8 = 0 at zero
          omega
        have more : fragment.packet.moreFragments = true := by
          cases mf : fragment.packet.moreFragments
          · simp [mf, offset] at fragmented
          · rfl
        have aligned := normalize_more_aligned fragment more
        omega

theorem arrive_processed (policy : Policy) (before : State) (now : Nat) (domain : Domain)
    (fragment : IPv4Fragment.Decoded) (result : Result)
    (accepted : arrive policy before now domain fragment = .ok result) :
    result = process policy before now domain fragment ∧ fragment.packet.wireLength < 65536 ∧
      before.lastTime ≤ now ∧ 0 < policy.timeout := by
  unfold arrive at accepted
  split at accepted
  · cases accepted
  · rename_i timeout
    split at accepted
    · cases accepted
    · rename_i clock
      split at accepted
      · cases accepted
      · rename_i checked
        simp only [Except.ok.injEq] at accepted
        exact ⟨accepted.symm, by omega, by omega, by omega⟩

theorem arrive_valid (policy : Policy) (before : State) (now : Nat) (domain : Domain)
    (fragment : IPv4Fragment.Decoded) (result : Result)
    (accepted : arrive policy before now domain fragment = .ok result) (valid : before.Valid) : result.state.Valid := by
  obtain ⟨processed, bounded, _, _⟩ := arrive_processed _ _ _ _ _ _ accepted
  rw [processed]
  exact process_valid _ _ _ _ _ valid bounded

def packetKey (domain : Domain) (packet : IPv4.Packet) : Key :=
  ⟨domain, packet.source, packet.destination, packet.protocol, packet.identification⟩

structure Output.Valid (wanted : Key) (output : Output) : Prop where
  encodable : output.packet.Encodable
  sameKey : packetKey wanted.domain output.packet = wanted
  payload : output.packet.payload = output.pieces.flatMap (·.data)
  coverage : Coverage 0 output.pieces
  normalized : ∀ piece ∈ output.pieces, piece = normalize piece.fragment
  fragmentBound : ∀ piece ∈ output.pieces, piece.fragment.packet.wireLength < 65536
  nonempty : output.reassembled = true → ∀ piece ∈ output.pieces, 0 < piece.data.length
  sizes : output.reassembled = true → 28 ≤ output.maxSize ∧ output.maxSize < 65536 ∧ output.maxDFSize ≤ output.maxSize
  df : output.reassembled = true → output.packet.dontFragment = decide (output.maxDFSize = output.maxSize)

theorem Queue.complete_valid (queue : Queue) (output : Output) (valid : queue.Valid)
    (completed : queue.complete = .accepted output) : output.Valid queue.key := by
  unfold Queue.complete at completed
  split at completed
  · cases completed
  · rename_i header first
    split at completed
    · rename_i ready
      have readyParts : queue.last = true ∧ queue.meat = queue.length := by
        simpa only [Bool.and_eq_true, decide_eq_true_eq] using ready
      have lengthSame := readyParts.2
      split at completed
      · cases completed
      · split at completed
        · cases completed
        · rename_i bounded
          split at completed
          · cases completed
          · rename_i payload joined
            cases completed
            obtain ⟨bytes, coverage⟩ := joinAt_payload _ _ _ joined
            obtain ⟨minimum, initial, member, zero, origin⟩ := valid.first header first
            constructor
            · change payload.length + 20 < 65536
              rw [bytes]
              change (queue.pieces.flatMap (·.data)).length = queue.length at lengthSame
              omega
            · change packetKey queue.key.domain header = queue.key
              rw [origin]
              exact valid.fragmentKey _ member
            · exact bytes
            · exact coverage
            · exact valid.normalized
            · exact valid.fragmentBound
            · exact fun _ => valid.nonempty
            · exact fun _ => ⟨minimum, valid.bounded, valid.df⟩
            · exact fun _ => rfl
    · cases completed

theorem accept_output (state : State) (queue : Queue) (piece : Piece) (output : Output)
    (emitted : (accept state queue piece).output = some output) :
    (accept state queue piece).state = state.erase queue.key ∧
      (accept state queue piece).disposition = .complete ∧ (store queue piece).complete = .accepted output := by
  unfold accept at emitted
  split at emitted
  · cases emitted
  · rename_i nonempty
    split at emitted
    · cases emitted
    · rename_i duplicate
      split at emitted
      · cases emitted
      · rename_i overlap
        dsimp only at emitted
        split at emitted
        · cases emitted
        · cases emitted
        · rename_i result completed
          cases Option.some.inj emitted
          have computed : accept state queue piece = ⟨state.erase queue.key, .complete, some output⟩ := by
            simp [accept, nonempty, duplicate, overlap, completed]
          rw [computed]
          exact ⟨rfl, rfl, completed⟩

theorem accept_output_valid (state : State) (queue : Queue) (piece : Piece) (output : Output)
    (emitted : (accept state queue piece).output = some output) (valid : queue.Valid)
    (normalized : piece = normalize piece.fragment) (bounded : piece.fragment.packet.wireLength < 65536)
    (same : key queue.key.domain piece.fragment = queue.key)
    (firstSize : 0 < piece.data.length → piece.start = 0 → 28 ≤ piece.data.length + 20) :
    output.Valid queue.key := by
  have positive : 0 < piece.data.length := by
    by_cases empty : piece.data.isEmpty = true
    · simp only [accept, empty, ↓reduceIte] at emitted
      cases emitted
    · cases data : piece.data with
      | nil => simp [data] at empty
      | cons head tail => simp
  have stored := store_valid queue piece valid normalized positive bounded same (firstSize positive)
  exact Queue.complete_valid (store queue piece) output stored (accept_output _ _ _ _ emitted).2.2

theorem whole_output_valid (domain : Domain) (fragment : IPv4Fragment.Decoded)
    (bounded : fragment.packet.wireLength < 65536)
    (whole : (!fragment.packet.moreFragments && decide (fragment.packet.offset.val = 0)) = true) :
    (⟨fragment.packet.toPacket, [⟨fragment, fragment.packet.payload⟩], 0, 0, false⟩ : Output).Valid (key domain fragment) := by
  have more : fragment.packet.moreFragments = false := by
    cases mf : fragment.packet.moreFragments
    · rfl
    · simp [mf] at whole
  have offset : fragment.packet.offset.val = 0 := by simpa [more] using whole
  constructor
  · exact bounded
  · rfl
  · simp
  · have start : (⟨fragment, fragment.packet.payload⟩ : Piece).start = 0 := by simp [Piece.start, offset]
    simpa only [start] using Coverage.cons (⟨fragment, fragment.packet.payload⟩ : Piece) [] (Coverage.nil _)
  · intro piece member
    simp only [List.mem_singleton] at member
    subst piece
    simp [normalize, more]
  · intro piece member
    simp only [List.mem_singleton] at member
    subst piece
    exact bounded
  · simp
  · simp
  · simp

theorem process_output_valid (policy : Policy) (before : State) (now : Nat) (domain : Domain)
    (fragment : IPv4Fragment.Decoded) (output : Output)
    (emitted : (process policy before now domain fragment).output = some output)
    (valid : before.Valid) (bounded : fragment.packet.wireLength < 65536) : output.Valid (key domain fragment) := by
  let state : State := { before.age now with lastTime := now }
  let wanted := key domain fragment
  let old := (state.lookup wanted).getD { key := wanted, expires := now + policy.timeout }
  have stateValid : state.Valid := before.age_valid now valid
  have oldValid : old.Valid := by
    cases found : state.lookup wanted with
    | none => simpa only [old, found, Option.getD_none] using Queue.fresh_valid wanted (now + policy.timeout)
    | some queue => simpa only [old, found, Option.getD_some] using stateValid queue (state.lookup_member _ _ found)
  have oldKey : old.key = wanted := by
    cases found : state.lookup wanted with
    | none => simp [old, found]
    | some queue => simpa only [old, found, Option.getD_some] using state.lookup_key _ _ found
  change (if !fragment.packet.moreFragments && decide (fragment.packet.offset.val = 0) then
      (⟨state, .whole, some ⟨fragment.packet.toPacket, [⟨fragment, fragment.packet.payload⟩], 0, 0, false⟩⟩ : Result)
    else match queuedLength old (normalize fragment) with
      | none => ⟨state.erase wanted, .inconsistentLength, none⟩
      | some queue => accept state queue (normalize fragment)).output = some output at emitted
  split at emitted
  · rename_i whole
    cases Option.some.inj emitted
    exact whole_output_valid _ _ bounded whole
  · rename_i fragmented
    split at emitted
    · cases emitted
    · rename_i queue lengthUpdated
      have fields := queuedLength_fields _ _ _ lengthUpdated
      have queueKey : queue.key = wanted := fields.1.trans oldKey
      have currentValid := queuedLength_valid _ _ _ lengthUpdated oldValid
      have firstSize : 0 < (normalize fragment).data.length → (normalize fragment).start = 0 →
          28 ≤ (normalize fragment).data.length + 20 := by
        intro positive zero
        have offset : fragment.packet.offset.val = 0 := by
          change fragment.packet.offset.val * 8 = 0 at zero
          omega
        have more : fragment.packet.moreFragments = true := by
          cases mf : fragment.packet.moreFragments
          · simp [mf, offset] at fragmented
          · rfl
        have aligned := normalize_more_aligned fragment more
        omega
      have same : key queue.key.domain (normalize fragment).fragment = queue.key := by rw [queueKey]; rfl
      have checked := accept_output_valid state queue (normalize fragment) output emitted currentValid rfl bounded same firstSize
      rw [queueKey] at checked
      exact checked

theorem arrive_output_valid (policy : Policy) (before : State) (now : Nat) (domain : Domain)
    (fragment : IPv4Fragment.Decoded) (result : Result) (output : Output)
    (accepted : arrive policy before now domain fragment = .ok result)
    (emitted : result.output = some output) (valid : before.Valid) : output.Valid (key domain fragment) := by
  obtain ⟨processed, bounded, _, _⟩ := arrive_processed _ _ _ _ _ _ accepted
  rw [processed] at emitted
  exact process_output_valid _ _ _ _ _ _ emitted valid bounded

theorem process_reassembled_erased (policy : Policy) (before : State) (now : Nat) (domain : Domain)
    (fragment : IPv4Fragment.Decoded) (output : Output)
    (emitted : (process policy before now domain fragment).output = some output)
    (reassembled : output.reassembled = true) :
    (process policy before now domain fragment).state.lookup (key domain fragment) = none := by
  let state : State := { before.age now with lastTime := now }
  let wanted := key domain fragment
  let old := (state.lookup wanted).getD { key := wanted, expires := now + policy.timeout }
  have oldKey : old.key = wanted := by
    cases found : state.lookup wanted with
    | none => simp [old, found]
    | some queue => simpa only [old, found, Option.getD_some] using state.lookup_key _ _ found
  unfold process at emitted ⊢
  split at emitted
  · cases Option.some.inj emitted
    cases reassembled
  · rename_i fragmented
    dsimp only at emitted
    split at emitted
    · cases emitted
    · rename_i queue lengthUpdated
      have queueKey := (queuedLength_fields _ _ _ lengthUpdated).1.trans oldKey
      have removed := (accept_output _ _ _ _ emitted).1
      simp only [fragmented, lengthUpdated, Bool.false_eq_true, ite_false]
      rw [removed, queueKey]
      exact state.erase_lookup wanted

theorem arrive_reassembled_erased (policy : Policy) (before : State) (now : Nat) (domain : Domain)
    (fragment : IPv4Fragment.Decoded) (result : Result) (output : Output)
    (accepted : arrive policy before now domain fragment = .ok result)
    (emitted : result.output = some output) (reassembled : output.reassembled = true) :
    result.state.lookup (key domain fragment) = none := by
  obtain ⟨processed, _, _, _⟩ := arrive_processed _ _ _ _ _ _ accepted
  rw [processed] at emitted ⊢
  exact process_reassembled_erased _ _ _ _ _ _ emitted reassembled

theorem State.erase_other (state : State) (wanted : Key) (queue : Queue) (other : queue.key ≠ wanted) :
    queue ∈ (state.erase wanted).queues ↔ queue ∈ state.queues := by simp [other]

theorem State.put_other (state : State) (inserted queue : Queue) (other : queue.key ≠ inserted.key) :
    queue ∈ (state.put inserted).queues ↔ queue ∈ state.queues := by
  have different : queue ≠ inserted := by intro same; exact other (congrArg Queue.key same)
  simp [different, other]

theorem accept_other (state : State) (queue : Queue) (piece : Piece) (untouched : Queue)
    (other : untouched.key ≠ queue.key) :
    untouched ∈ (accept state queue piece).state.queues ↔ untouched ∈ state.queues := by
  unfold accept
  split
  · exact state.erase_other _ _ other
  · split
    · exact state.put_other _ _ other
    · split
      · exact state.erase_other _ _ other
      · dsimp only
        cases done : (store queue piece).complete with
        | waiting => exact state.put_other _ _ other
        | rejected reason => exact state.erase_other _ _ other
        | accepted output => exact state.erase_other _ _ other

theorem process_other (policy : Policy) (before : State) (now : Nat) (domain : Domain)
    (fragment : IPv4Fragment.Decoded) (untouched : Queue) (other : untouched.key ≠ key domain fragment) :
    untouched ∈ (process policy before now domain fragment).state.queues ↔ untouched ∈ (before.age now).queues := by
  let state : State := { before.age now with lastTime := now }
  let wanted := key domain fragment
  let old := (state.lookup wanted).getD { key := wanted, expires := now + policy.timeout }
  have oldKey : old.key = wanted := by
    cases found : state.lookup wanted with
    | none => simp [old, found]
    | some queue => simpa only [old, found, Option.getD_some] using state.lookup_key _ _ found
  unfold process
  split
  · rfl
  · dsimp only
    split
    · exact state.erase_other _ _ other
    · rename_i queue lengthUpdated
      have queueKey := (queuedLength_fields _ _ _ lengthUpdated).1.trans oldKey
      exact accept_other _ _ _ _ (by rw [queueKey]; exact other)

theorem arrive_other (policy : Policy) (before : State) (now : Nat) (domain : Domain)
    (fragment : IPv4Fragment.Decoded) (result : Result) (untouched : Queue)
    (accepted : arrive policy before now domain fragment = .ok result) (other : untouched.key ≠ key domain fragment) :
    untouched ∈ result.state.queues ↔ untouched ∈ before.queues ∧ now < untouched.expires := by
  obtain ⟨processed, _, _, _⟩ := arrive_processed _ _ _ _ _ _ accepted
  rw [processed, process_other _ _ _ _ _ _ other, State.age_member]

theorem Queue.complete_pieces (queue : Queue) (output : Output)
    (completed : queue.complete = .accepted output) : output.pieces = queue.pieces ∧ output.reassembled = true := by
  unfold Queue.complete at completed
  split at completed
  · cases completed
  · split at completed
    · split at completed
      · cases completed
      · split at completed
        · cases completed
        · split at completed
          · cases completed
          · cases completed; exact ⟨rfl, rfl⟩
    · cases completed

theorem accept_output_piece (state : State) (queue : Queue) (piece : Piece) (output : Output) (value : Piece)
    (emitted : (accept state queue piece).output = some output) (member : value ∈ output.pieces) :
    value = piece ∨ value ∈ queue.pieces := by
  have completed := (accept_output _ _ _ _ emitted).2.2
  rw [(Queue.complete_pieces _ _ completed).1] at member
  exact (store_piece_member _ _ _).mp member

theorem process_output_piece (policy : Policy) (before : State) (now : Nat) (domain : Domain)
    (fragment : IPv4Fragment.Decoded) (output : Output) (value : Piece)
    (emitted : (process policy before now domain fragment).output = some output) (member : value ∈ output.pieces) :
    value = normalize fragment ∨ ∃ queue ∈ before.queues, now < queue.expires ∧ value ∈ queue.pieces := by
  let state : State := { before.age now with lastTime := now }
  let wanted := key domain fragment
  let old := (state.lookup wanted).getD { key := wanted, expires := now + policy.timeout }
  unfold process at emitted
  split at emitted
  · rename_i whole
    cases Option.some.inj emitted
    simp only [List.mem_singleton] at member
    subst value
    have more : fragment.packet.moreFragments = false := by
      cases mf : fragment.packet.moreFragments
      · rfl
      · simp [mf] at whole
    exact Or.inl (by simp [normalize, more])
  · dsimp only at emitted
    split at emitted
    · cases emitted
    · rename_i queue lengthUpdated
      rcases accept_output_piece _ _ _ _ _ emitted member with current | previous
      · exact Or.inl current
      · have runs := (queuedLength_fields _ _ _ lengthUpdated).2.2.1
        change value ∈ queue.runs.flatMap Run.pieces at previous
        rw [runs] at previous
        change value ∈ old.pieces at previous
        cases found : state.lookup wanted with
        | none => simp [old, found, Queue.pieces] at previous
        | some source =>
          have belongs := state.lookup_member _ _ found
          have aged : source ∈ before.queues ∧ now < source.expires := (State.age_member _ _ _).mp belongs
          refine Or.inr ⟨source, aged.1, aged.2, ?_⟩
          simpa only [old, found, Option.getD_some] using previous

theorem arrive_output_piece (policy : Policy) (before : State) (now : Nat) (domain : Domain)
    (fragment : IPv4Fragment.Decoded) (result : Result) (output : Output) (value : Piece)
    (accepted : arrive policy before now domain fragment = .ok result) (emitted : result.output = some output)
    (member : value ∈ output.pieces) :
    value = normalize fragment ∨ ∃ queue ∈ before.queues, now < queue.expires ∧ value ∈ queue.pieces := by
  obtain ⟨processed, _, _, _⟩ := arrive_processed _ _ _ _ _ _ accepted
  rw [processed] at emitted
  exact process_output_piece _ _ _ _ _ _ _ emitted member

structure Arrival where
  now : Nat
  domain : Domain
  fragment : IPv4Fragment.Decoded
  deriving Repr, BEq, DecidableEq

def execute (policy : Policy) (before : State) : List Arrival → Except Error (State × List Result)
  | [] => .ok (before, [])
  | event :: rest => do
    let result ← arrive policy before event.now event.domain event.fragment
    let (final, findings) ← execute policy result.state rest
    return (final, result :: findings)

theorem execute_valid (policy : Policy) (before final : State) (events : List Arrival) (results : List Result)
    (accepted : execute policy before events = .ok (final, results)) (valid : before.Valid) :
    final.Valid ∧ ∀ result ∈ results, result.state.Valid := by
  induction events generalizing before final results with
  | nil =>
    simp only [execute, Except.ok.injEq, Prod.mk.injEq] at accepted
    obtain ⟨rfl, rfl⟩ := accepted
    exact ⟨valid, by simp⟩
  | cons event rest ih =>
    cases computed : arrive policy before event.now event.domain event.fragment with
    | error error => simp [execute, computed, bind, Except.bind] at accepted
    | ok result =>
      have current := arrive_valid _ _ _ _ _ _ computed valid
      cases following : execute policy result.state rest with
      | error error => simp [execute, computed, following, bind, Except.bind] at accepted
      | ok pair =>
        rcases pair with ⟨after, findings⟩
        simp only [execute, computed, following, bind, Except.bind, pure, Except.pure, Except.ok.injEq,
          Prod.mk.injEq] at accepted
        obtain ⟨rfl, rfl⟩ := accepted
        obtain ⟨finalValid, tailValid⟩ := ih _ _ _ following current
        exact ⟨finalValid, fun value member => by
          rcases List.mem_cons.mp member with rfl | later
          · exact current
          · exact tailValid value later⟩

theorem process_output_disposition (policy : Policy) (before : State) (now : Nat) (domain : Domain)
    (fragment : IPv4Fragment.Decoded) (output : Output)
    (emitted : (process policy before now domain fragment).output = some output) :
    (process policy before now domain fragment).disposition = .whole ∨
      (process policy before now domain fragment).disposition = .complete := by
  unfold process at emitted ⊢
  split at emitted
  · rename_i whole
    simp only [whole, ↓reduceIte]
    exact Or.inl True.intro
  · rename_i fragmented
    dsimp only at emitted
    split at emitted
    · cases emitted
    · rename_i queue lengthUpdated
      have complete := (accept_output _ _ _ _ emitted).2.1
      simp only [fragmented, lengthUpdated, Bool.false_eq_true, ite_false]
      exact Or.inr complete

theorem arrive_duplicate_no_output (policy : Policy) (before : State) (now : Nat) (domain : Domain)
    (fragment : IPv4Fragment.Decoded) (result : Result)
    (accepted : arrive policy before now domain fragment = .ok result)
    (duplicate : result.disposition = .duplicate) : result.output = none := by
  cases emitted : result.output with
  | none => rfl
  | some output =>
    obtain ⟨processed, _, _, _⟩ := arrive_processed _ _ _ _ _ _ accepted
    rw [processed] at emitted duplicate
    rcases process_output_disposition _ _ _ _ _ _ emitted with whole | complete
    · rw [duplicate] at whole
      cases whole
    · rw [duplicate] at complete
      cases complete

def Queue.Sources (queue : Queue) (history : List IPv4Fragment.Decoded) : Prop :=
  ∀ piece ∈ queue.pieces, piece.fragment ∈ history

def State.Sources (state : State) (history : List IPv4Fragment.Decoded) : Prop :=
  ∀ queue ∈ state.queues, queue.Sources history

theorem State.initial_sources : State.initial.Sources [] := by simp [State.Sources, State.initial]

theorem State.sources_mono (state : State) (first second : List IPv4Fragment.Decoded)
    (sources : state.Sources first) (subset : ∀ fragment ∈ first, fragment ∈ second) : state.Sources second := by
  intro queue member piece stored
  exact subset _ (sources queue member piece stored)

theorem State.age_sources (state : State) (now : Nat) (history : List IPv4Fragment.Decoded)
    (sources : state.Sources history) : (state.age now).Sources history := by
  intro queue member
  exact sources queue ((State.age_member _ _ _).mp member).1

theorem State.erase_sources (state : State) (wanted : Key) (history : List IPv4Fragment.Decoded)
    (sources : state.Sources history) : (state.erase wanted).Sources history := by
  intro queue member
  exact sources queue ((State.erase_member _ _ _).mp member).1

theorem State.put_sources (state : State) (queue : Queue) (history : List IPv4Fragment.Decoded)
    (sources : state.Sources history) (inserted : queue.Sources history) : (state.put queue).Sources history := by
  intro value member
  rcases (State.put_member _ _ _).mp member with rfl | previous
  · exact inserted
  · exact sources value previous.1

theorem accept_sources (state : State) (queue : Queue) (piece : Piece) (history : List IPv4Fragment.Decoded)
    (sources : state.Sources history) (previous : queue.Sources history) (current : piece.fragment ∈ history) :
    (accept state queue piece).state.Sources history := by
  unfold accept
  split
  · exact state.erase_sources _ _ sources
  · split
    · exact state.put_sources _ _ sources previous
    · split
      · exact state.erase_sources _ _ sources
      · have stored : (store queue piece).Sources history := by
          intro value member
          rcases (store_piece_member _ _ _).mp member with rfl | old
          · exact current
          · exact previous value old
        dsimp only
        cases done : (store queue piece).complete with
        | waiting => exact state.put_sources _ _ sources stored
        | rejected reason => exact state.erase_sources _ _ sources
        | accepted output => exact state.erase_sources _ _ sources

theorem process_sources (policy : Policy) (before : State) (now : Nat) (domain : Domain)
    (fragment : IPv4Fragment.Decoded) (history : List IPv4Fragment.Decoded) (sources : before.Sources history) :
    (process policy before now domain fragment).state.Sources (fragment :: history) := by
  let state : State := { before.age now with lastTime := now }
  let wanted := key domain fragment
  let old := (state.lookup wanted).getD { key := wanted, expires := now + policy.timeout }
  have stateSources : state.Sources (fragment :: history) :=
    state.sources_mono history (fragment :: history) (before.age_sources now history sources)
      (fun value member => by simp [member])
  have oldSources : old.Sources (fragment :: history) := by
    cases found : state.lookup wanted with
    | none => simp [old, found, Queue.Sources, Queue.pieces]
    | some queue => simpa only [old, found, Option.getD_some] using stateSources queue (state.lookup_member _ _ found)
  unfold process
  split
  · exact stateSources
  · dsimp only
    split
    · exact state.erase_sources _ _ stateSources
    · rename_i queue lengthUpdated
      have runs := (queuedLength_fields _ _ _ lengthUpdated).2.2.1
      have queueSources : queue.Sources (fragment :: history) := by
        unfold Queue.Sources Queue.pieces
        rw [runs]
        exact oldSources
      exact accept_sources _ _ _ _ stateSources queueSources (by simp)

theorem arrive_sources (policy : Policy) (before : State) (now : Nat) (domain : Domain)
    (fragment : IPv4Fragment.Decoded) (result : Result) (history : List IPv4Fragment.Decoded)
    (accepted : arrive policy before now domain fragment = .ok result) (sources : before.Sources history) :
    result.state.Sources (fragment :: history) := by
  obtain ⟨processed, _, _, _⟩ := arrive_processed _ _ _ _ _ _ accepted
  rw [processed]
  exact process_sources _ _ _ _ _ _ sources

theorem arrive_output_sources (policy : Policy) (before : State) (now : Nat) (domain : Domain)
    (fragment : IPv4Fragment.Decoded) (result : Result) (output : Output) (history : List IPv4Fragment.Decoded)
    (accepted : arrive policy before now domain fragment = .ok result) (emitted : result.output = some output)
    (sources : before.Sources history) : ∀ piece ∈ output.pieces, piece.fragment ∈ fragment :: history := by
  intro piece member
  rcases arrive_output_piece _ _ _ _ _ _ _ _ accepted emitted member with rfl | previous
  · simp
  · obtain ⟨queue, belongs, _, stored⟩ := previous
    exact List.mem_cons_of_mem _ (sources queue belongs piece stored)

theorem execute_sources (policy : Policy) (before final : State) (events : List Arrival)
    (results : List Result) (history : List IPv4Fragment.Decoded)
    (accepted : execute policy before events = .ok (final, results)) (sources : before.Sources history) :
    final.Sources (events.map (·.fragment) ++ history) := by
  induction events generalizing before final results history with
  | nil =>
    simp only [execute, Except.ok.injEq, Prod.mk.injEq] at accepted
    obtain ⟨rfl, rfl⟩ := accepted
    exact sources
  | cons event rest ih =>
    cases computed : arrive policy before event.now event.domain event.fragment with
    | error error => simp [execute, computed, bind, Except.bind] at accepted
    | ok result =>
      have current := arrive_sources _ _ _ _ _ _ _ computed sources
      cases following : execute policy result.state rest with
      | error error => simp [execute, computed, following, bind, Except.bind] at accepted
      | ok pair =>
        rcases pair with ⟨after, findings⟩
        simp only [execute, computed, following, bind, Except.bind, pure, Except.pure, Except.ok.injEq,
          Prod.mk.injEq] at accepted
        obtain ⟨rfl, rfl⟩ := accepted
        have finalSources := ih _ _ _ _ following current
        apply State.sources_mono _ _ _ finalSources
        intro fragment member
        rcases List.mem_append.mp member with later | previous
        · exact List.mem_append.mpr (Or.inl (List.mem_cons_of_mem _ later))
        · rcases List.mem_cons.mp previous with rfl | old
          · exact List.mem_append.mpr (Or.inl (by simp))
          · exact List.mem_append.mpr (Or.inr old)

theorem computed_payload_permutation (leftPolicy rightPolicy : Policy) (leftBefore rightBefore : State)
    (leftNow rightNow : Nat) (leftDomain rightDomain : Domain)
    (leftFragment rightFragment : IPv4Fragment.Decoded) (leftResult rightResult : Result) (left right : Output)
    (leftStep : arrive leftPolicy leftBefore leftNow leftDomain leftFragment = .ok leftResult)
    (rightStep : arrive rightPolicy rightBefore rightNow rightDomain rightFragment = .ok rightResult)
    (leftOutput : leftResult.output = some left) (rightOutput : rightResult.output = some right)
    (leftValid : leftBefore.Valid) (rightValid : rightBefore.Valid) (reassembled : left.reassembled = true)
    (permutation : left.pieces.Perm right.pieces) : left.packet.payload = right.packet.payload := by
  have first := arrive_output_valid _ _ _ _ _ _ _ leftStep leftOutput leftValid
  have second := arrive_output_valid _ _ _ _ _ _ _ rightStep rightOutput rightValid
  apply joined_permutation left.pieces right.pieces
  · rw [first.payload]
    exact first.coverage.joinAt
  · rw [second.payload]
    exact second.coverage.joinAt
  · exact permutation
  · exact first.nonempty reassembled

end Netlib.Protocol.IPv4Reassembly
