import Netlib.Protocol.TCP.ReceiveStore

/-!
# Actual receipt allocations and retained run origins

The history records exact successful store operations.
Its carrier links each operation to the enclosing execution history.
A released run keeps its original receipt and metadata.
-/

namespace Netlib.Protocol.TCP.ReceiveStoreHistory

namespace S
export ReceiveStore (State Run Result current accept)
end S

structure Accepted (Meta Tag : Type) where
  before : S.State Meta
  position : Nat
  payload : List UInt8
  metadata : Meta
  edge : Nat
  budget : Nat
  result : S.Result Meta
  carrier : Tag
  checked : S.accept before position payload metadata edge budget = .ok result

variable {Meta Tag : Type}

def Accepted.after (step : Accepted Meta Tag) : S.State Meta := step.result.state

def Accepted.allocated (step : Accepted Meta Tag) : S.Run Meta :=
  S.current step.before step.position step.payload step.metadata

theorem Accepted.identity (step : Accepted Meta Tag) :
    step.result.receiptID = step.before.nextID ∧ step.after.nextID = step.before.nextID + 1 :=
  ReceiveStore.accept_identity _ _ _ _ _ _ _ step.checked

theorem Accepted.source (step : Accepted Meta Tag) (run : S.Run Meta)
    (member : run ∈ step.result.released ∨ run ∈ step.after.held) :
    run ∈ step.before.held ∨ run = step.allocated :=
  ReceiveStore.accept_source _ _ _ _ _ _ _ step.checked run member

theorem Accepted.held_before (step : Accepted Meta Tag) (run : S.Run Meta)
    (held : run ∈ step.before.held) : run.receipt < step.before.nextID := by
  obtain ⟨_, _, _, valid, _⟩ := ReceiveStore.accept_stages _ _ _ _ _ _ _ step.checked
  exact (valid.2.2.2.1 run held).2.2.2

theorem Accepted.frontier (step : Accepted Meta Tag) :
    step.after.frontier = step.before.frontier + (ReceiveStore.bytes step.result.released).length := by
  rw [ReceiveStore.size_bytes]
  exact ReceiveStore.accept_frontier _ _ _ _ _ _ _ step.checked

theorem Accepted.contiguous (step : Accepted Meta Tag) :
    ReceiveStore.Contiguous step.before.frontier step.result.released :=
  ReceiveStore.accept_contiguous _ _ _ _ _ _ _ step.checked

inductive History : S.State Meta → List (Accepted Meta Tag) → S.State Meta → Prop where
  | nil (state : S.State Meta) : History state [] state
  | cons (head : Accepted Meta Tag) (tail : History head.after steps final) :
      History head.before (head :: steps) final

variable {initial middle final : S.State Meta} {steps prior later : List (Accepted Meta Tag)}

theorem History.append (first : History initial prior middle) (second : History middle later final) :
    History initial (prior ++ later) final := by
  induction first with
  | nil state => exact second
  | cons head tail ih => exact .cons head (ih second)

theorem History.split (history : History initial steps final) (step : Accepted Meta Tag) (member : step ∈ steps) :
    ∃ prior later, steps = prior ++ step :: later ∧ History initial prior step.before ∧
      History step.after later final := by
  induction history with
  | nil state => simp at member
  | @cons steps final head tail ih =>
    rcases List.mem_cons.mp member with same | member
    · subst step
      exact ⟨[], steps, rfl, .nil head.before, tail⟩
    · obtain ⟨prior, later, same, preceding, following⟩ := ih member
      exact ⟨head :: prior, later, by simp [same], .cons head preceding, following⟩

theorem History.cut (history : History initial (prior ++ head :: later) final) :
    History initial prior head.before ∧ History head.after later final := by
  induction prior generalizing initial with
  | nil =>
    cases history with
    | cons first tail => exact ⟨.nil head.before, tail⟩
  | cons first prior ih =>
    cases history with
    | cons first tail =>
      obtain ⟨preceding, following⟩ := ih tail
      exact ⟨.cons first preceding, following⟩

theorem History.counter (history : History initial steps final) :
    final.nextID = initial.nextID + steps.length := by
  induction history with
  | nil state => simp
  | cons head tail ih =>
    rw [ih, head.identity.2]
    simp only [List.length_cons]
    omega

theorem History.frontier (history : History initial steps final) :
    final.frontier = initial.frontier + (steps.flatMap (fun step => ReceiveStore.bytes step.result.released)).length := by
  induction history with
  | nil state => simp
  | cons head tail ih =>
    rw [ih, head.frontier]
    simp only [List.flatMap_cons, List.length_append]
    omega

theorem History.counter_lower (history : History initial steps final) (step : Accepted Meta Tag)
    (member : step ∈ steps) : initial.nextID ≤ step.before.nextID := by
  obtain ⟨prior, _, _, preceding, _⟩ := history.split step member
  rw [preceding.counter]
  omega

theorem History.counter_upper (history : History initial steps final) (step : Accepted Meta Tag)
    (member : step ∈ steps) : step.before.nextID < final.nextID := by
  obtain ⟨_, later, _, _, following⟩ := history.split step member
  rw [following.counter, step.identity.2]
  omega

theorem History.ordered (history : History initial steps final) :
    steps.Pairwise (fun first second => first.before.nextID < second.before.nextID) := by
  induction history with
  | nil state => exact .nil
  | cons head tail ih =>
    apply List.pairwise_cons.mpr
    refine ⟨?_, ih⟩
    intro step member
    have lower := tail.counter_lower step member
    rw [head.identity.2] at lower
    omega

theorem History.allocation_unique (history : History initial steps final)
    (first second : Accepted Meta Tag) (firstMember : first ∈ steps) (secondMember : second ∈ steps)
    (same : first.before.nextID = second.before.nextID) : first = second := by
  induction history with
  | nil state => simp at firstMember
  | cons head tail ih =>
    rcases List.mem_cons.mp firstMember with firstEq | firstMember
    · subst first
      rcases List.mem_cons.mp secondMember with secondEq | secondMember
      · subst second
        rfl
      · have lower := tail.counter_lower second secondMember
        rw [head.identity.2] at lower
        omega
    · rcases List.mem_cons.mp secondMember with secondEq | secondMember
      · subst second
        have lower := tail.counter_lower first firstMember
        rw [head.identity.2] at lower
        omega
      · exact ih firstMember secondMember

theorem History.held_origin_or_initial (history : History initial steps final)
    (run : S.Run Meta) (member : run ∈ final.held) :
    run ∈ initial.held ∨ ∃ issuer ∈ steps, run = issuer.allocated := by
  induction history with
  | nil state => exact .inl member
  | cons head tail ih =>
    rcases ih member with retained | created
    · rcases head.source run (.inr retained) with old | fresh
      · exact .inl old
      · exact .inr ⟨head, by simp, fresh⟩
    · obtain ⟨issuer, belongs, source⟩ := created
      exact .inr ⟨issuer, by simp [belongs], source⟩

theorem History.held_origin (history : History initial steps final) (empty : initial.held = [])
    (run : S.Run Meta) (member : run ∈ final.held) :
    ∃ issuer ∈ steps, run = issuer.allocated := by
  rcases history.held_origin_or_initial run member with old | created
  · simp [empty] at old
  · exact created

structure ReleasedOrigin (steps : List (Accepted Meta Tag)) (release : Accepted Meta Tag) (run : S.Run Meta) where
  prior : List (Accepted Meta Tag)
  later : List (Accepted Meta Tag)
  split : steps = prior ++ release :: later
  issuer : Accepted Meta Tag
  place : issuer ∈ prior ∨ issuer = release
  allocated : run = issuer.allocated

theorem History.released_origin (history : History initial steps final) (empty : initial.held = [])
    (release : Accepted Meta Tag) (member : release ∈ steps) (run : S.Run Meta)
    (released : run ∈ release.result.released) : Nonempty (ReleasedOrigin steps release run) := by
  obtain ⟨prior, later, split, preceding, _⟩ := history.split release member
  rcases release.source run (.inl released) with held | current
  · obtain ⟨issuer, belongs, allocated⟩ := preceding.held_origin empty run held
    exact ⟨⟨prior, later, split, issuer, .inl belongs, allocated⟩⟩
  · exact ⟨⟨prior, later, split, release, .inr rfl, current⟩⟩

theorem ReleasedOrigin.issuer_member (origin : ReleasedOrigin steps release run) : origin.issuer ∈ steps := by
  have member : origin.issuer ∈ origin.prior ++ release :: origin.later := by
    rcases origin.place with prior | current
    · exact List.mem_append_left _ prior
    · rw [current]
      simp
  exact Eq.mpr (congrArg (fun list => origin.issuer ∈ list) origin.split) member

theorem ReleasedOrigin.fields (origin : ReleasedOrigin steps release run) :
    run.position = origin.issuer.position ∧ run.bytes = origin.issuer.payload ∧
      run.receipt = origin.issuer.before.nextID ∧ run.metadata = origin.issuer.metadata := by
  exact ⟨congrArg ReceiveStore.Run.position origin.allocated, congrArg ReceiveStore.Run.bytes origin.allocated,
    congrArg ReceiveStore.Run.receipt origin.allocated, congrArg ReceiveStore.Run.metadata origin.allocated⟩

theorem ReleasedOrigin.no_later (origin : ReleasedOrigin steps release run)
    (history : History initial steps final) : run.receipt ≤ release.before.nextID := by
  rw [origin.fields.2.2.1]
  rcases origin.place with prior | current
  · have scope := history
    rw [origin.split] at scope
    exact Nat.le_of_lt (scope.cut.1.counter_upper origin.issuer prior)
  · rw [current]
    exact Nat.le_refl _

theorem ReleasedOrigin.old_before (origin : ReleasedOrigin steps release run)
    (old : run.receipt < release.before.nextID) :
    origin.issuer ∈ origin.prior := by
  rcases origin.place with prior | current
  · exact prior
  · have same := origin.fields.2.2.1
    rw [current] at same
    omega

theorem ReleasedOrigin.held_earlier (origin : ReleasedOrigin steps release run)
    (held : run ∈ release.before.held) : origin.issuer ∈ origin.prior :=
  origin.old_before (release.held_before run held)

def StreamRange (base : Nat) (stream : List UInt8) (run : S.Run Meta) : Prop :=
  ∃ prefixBytes : List UInt8, base + prefixBytes.length = run.position ∧ prefixBytes ++ run.bytes <+: stream

theorem contiguous_prefix (base : Nat) (stream accumulated : List UInt8) (runs : List (S.Run Meta))
    (aligned : ReceiveStore.Contiguous (base + accumulated.length) runs)
    (prior : accumulated <+: stream) (sources : ∀ run ∈ runs, StreamRange base stream run) :
    accumulated ++ ReceiveStore.bytes runs <+: stream := by
  induction runs generalizing accumulated with
  | nil => simpa only [ReceiveStore.bytes, List.flatMap_nil, List.append_nil] using prior
  | cons head tail ih =>
    obtain ⟨position, rest⟩ := aligned
    obtain ⟨prefixBytes, prefixPosition, ranged⟩ := sources head (by simp)
    have sameLength : accumulated.length = prefixBytes.length := by omega
    have prefixBefore : prefixBytes <+: stream := (List.prefix_append _ _).trans ranged
    have sameBytes : accumulated = prefixBytes :=
      (List.prefix_of_prefix_length_le prior prefixBefore (Nat.le_of_eq sameLength)).eq_of_length sameLength
    have added : accumulated ++ head.bytes <+: stream := by rw [sameBytes]; exact ranged
    have next : head.limit = base + (accumulated ++ head.bytes).length := by
      simp only [ReceiveStore.Run.limit, position, List.length_append]
      omega
    have alignedTail : ReceiveStore.Contiguous (base + (accumulated ++ head.bytes).length) tail := by
      rw [← next]
      exact rest
    have result := ih (accumulated ++ head.bytes) alignedTail added (fun run member => sources run (by simp [member]))
    simpa only [ReceiveStore.bytes, List.flatMap_cons, List.append_assoc] using result

theorem Accepted.prefix_step (step : Accepted Meta Tag) (base : Nat) (stream accumulated : List UInt8)
    (cursor : step.before.frontier = base + accumulated.length) (prior : accumulated <+: stream)
    (held : ∀ run ∈ step.before.held, StreamRange base stream run)
    (incoming : StreamRange base stream step.allocated) :
    accumulated ++ ReceiveStore.bytes step.result.released <+: stream ∧
      ∀ run ∈ step.after.held, StreamRange base stream run := by
  have sources : ∀ run, run ∈ step.result.released ∨ run ∈ step.after.held → StreamRange base stream run := by
    intro run member
    rcases step.source run member with previous | current
    · exact held run previous
    · exact Eq.mpr (congrArg (StreamRange base stream) current) incoming
  refine ⟨?_, fun run member => sources run (.inr member)⟩
  have aligned : ReceiveStore.Contiguous (base + accumulated.length) step.result.released := by
    rw [← cursor]
    exact step.contiguous
  exact contiguous_prefix base stream accumulated step.result.released aligned prior
    (fun run member => sources run (.inl member))

theorem History.prefix_aux (history : History initial steps final) (base : Nat) (stream : List UInt8)
    (sources : ∀ step ∈ steps, ∀ run ∈ step.result.released, StreamRange base stream run) :
    ∀ accumulated : List UInt8, accumulated <+: stream → initial.frontier = base + accumulated.length →
      accumulated ++ steps.flatMap (fun step => ReceiveStore.bytes step.result.released) <+: stream := by
  induction history with
  | nil state => intro accumulated prior _; simpa using prior
  | cons head tail ih =>
    intro accumulated prior cursor
    have aligned : ReceiveStore.Contiguous (base + accumulated.length) head.result.released := by
      rw [← cursor]
      exact head.contiguous
    have added := contiguous_prefix base stream accumulated head.result.released aligned prior (sources head (by simp))
    have next : head.after.frontier = base + (accumulated ++ ReceiveStore.bytes head.result.released).length := by
      rw [head.frontier, cursor, List.length_append]
      omega
    have result := ih (fun step member => sources step (by simp [member]))
      (accumulated ++ ReceiveStore.bytes head.result.released) added next
    simpa only [List.flatMap_cons, List.append_assoc] using result

theorem History.released_prefix (history : History initial steps final) (empty : initial.held = [])
    (stream : List UInt8) (sources : ∀ step ∈ steps, StreamRange initial.frontier stream step.allocated) :
    steps.flatMap (fun step => ReceiveStore.bytes step.result.released) <+: stream := by
  have released : ∀ step ∈ steps, ∀ run ∈ step.result.released, StreamRange initial.frontier stream run := by
    intro step member run present
    obtain ⟨origin⟩ := history.released_origin empty step member run present
    have ranged := sources origin.issuer origin.issuer_member
    exact Eq.mpr (congrArg (StreamRange initial.frontier stream) origin.allocated) ranged
  have result := history.prefix_aux initial.frontier stream released [] (by simp) (by simp)
  simpa only [List.nil_append] using result

theorem bytes_location (runs : List (S.Run Meta)) (index : Nat) (byte : UInt8)
    (selected : (ReceiveStore.bytes runs)[index]? = some byte) :
    ∃ prior run later localIndex, runs = prior ++ run :: later ∧
      index = ReceiveStore.size prior + localIndex ∧ run.bytes[localIndex]? = some byte := by
  induction runs generalizing index with
  | nil => simp [ReceiveStore.bytes] at selected
  | cons head tail ih =>
    have found : (head.bytes ++ ReceiveStore.bytes tail)[index]? = some byte := selected
    by_cases inside : index < head.bytes.length
    · rw [List.getElem?_append_left inside] at found
      exact ⟨[], head, tail, index, rfl, by simp [ReceiveStore.size], found⟩
    · have outside : head.bytes.length ≤ index := by omega
      rw [List.getElem?_append_right outside] at found
      obtain ⟨prior, run, later, localIndex, same, position, present⟩ := ih _ found
      refine ⟨head :: prior, run, later, localIndex, by simp [same], ?_, present⟩
      simp only [ReceiveStore.size, List.map_cons, List.sum_cons]
      unfold ReceiveStore.size at position
      omega

theorem contiguous_position (frontier : Nat) (runs prior later : List (S.Run Meta)) (run : S.Run Meta)
    (aligned : ReceiveStore.Contiguous frontier runs) (split : runs = prior ++ run :: later) :
    run.position = frontier + ReceiveStore.size prior := by
  subst runs
  induction prior generalizing frontier with
  | nil => simpa only [List.nil_append, ReceiveStore.size, List.map_nil, List.sum_nil, Nat.add_zero] using aligned.1
  | cons head prior ih =>
    have next := ih head.limit aligned.2
    simp only [ReceiveStore.size, List.map_cons, List.sum_cons]
    unfold ReceiveStore.Run.limit ReceiveStore.size at next
    have start := aligned.1
    omega

structure ReleasedByteOrigin (steps : List (Accepted Meta Tag)) (release : Accepted Meta Tag)
    (index : Nat) (byte : UInt8) where
  prior : List (S.Run Meta)
  run : S.Run Meta
  later : List (S.Run Meta)
  split : release.result.released = prior ++ run :: later
  localIndex : Nat
  position : index = ReceiveStore.size prior + localIndex
  selected : run.bytes[localIndex]? = some byte
  origin : ReleasedOrigin steps release run
  coordinate : run.position + localIndex = release.before.frontier + index

theorem History.released_byte_origin (history : History initial steps final) (empty : initial.held = [])
    (release : Accepted Meta Tag) (member : release ∈ steps) (index : Nat) (byte : UInt8)
    (selected : (ReceiveStore.bytes release.result.released)[index]? = some byte) :
    Nonempty (ReleasedByteOrigin steps release index byte) := by
  obtain ⟨prior, run, later, localIndex, split, position, present⟩ := bytes_location _ index byte selected
  have belongs : run ∈ release.result.released := by rw [split]; simp
  obtain ⟨origin⟩ := history.released_origin empty release member run belongs
  have coordinate := contiguous_position _ _ prior later run release.contiguous split
  refine ⟨⟨prior, run, later, split, localIndex, position, present, origin, ?_⟩⟩
  omega

theorem ReleasedByteOrigin.input_byte (value : ReleasedByteOrigin steps release index byte) :
    value.origin.issuer.payload[value.localIndex]? = some byte := by
  rw [← value.origin.fields.2.1]
  exact value.selected

theorem ReleasedByteOrigin.input_position (value : ReleasedByteOrigin steps release index byte) :
    value.origin.issuer.position + value.localIndex = release.before.frontier + index := by
  rw [← value.origin.fields.1]
  exact value.coordinate

structure AllocationAt (steps : List (Accepted Meta Tag)) (id : Nat) where
  prior : List (Accepted Meta Tag)
  step : Accepted Meta Tag
  later : List (Accepted Meta Tag)
  split : steps = prior ++ step :: later
  identity : step.before.nextID = id

def findAllocation : (steps : List (Accepted Meta Tag)) → (id : Nat) → Except String (AllocationAt steps id)
  | [], _ => .error "The actual receipt allocation is absent from this history."
  | head :: tail, id => do
    if same : head.before.nextID = id then
      return ⟨[], head, tail, rfl, same⟩
    else
      let rest ← findAllocation tail id
      return ⟨head :: rest.prior, rest.step, rest.later,
        by simp only [rest.split, List.cons_append], rest.identity⟩

theorem AllocationAt.member {id : Nat} (value : AllocationAt steps id) : value.step ∈ steps := by
  have member : value.step ∈ value.prior ++ value.step :: value.later := by simp
  exact Eq.mpr (congrArg (fun list => value.step ∈ list) value.split) member

def releasedOrigin (history : History initial steps final) (empty : initial.held = [])
    (release : Accepted Meta Tag) (member : release ∈ steps) (run : S.Run Meta)
    (released : run ∈ release.result.released) : Except String (ReleasedOrigin steps release run) := do
  let releaseAt ← findAllocation steps release.before.nextID
  let issuerAt ← findAllocation steps run.receipt
  have sameRelease : releaseAt.step = release :=
    history.allocation_unique releaseAt.step release releaseAt.member member releaseAt.identity
  have split : steps = releaseAt.prior ++ release :: releaseAt.later := by
    have selected := releaseAt.split
    rw [sameRelease] at selected
    exact selected
  have allocated : run = issuerAt.step.allocated := by
    obtain ⟨origin⟩ := history.released_origin empty release member run released
    have sameIssuer : origin.issuer = issuerAt.step :=
      history.allocation_unique origin.issuer issuerAt.step origin.issuer_member issuerAt.member
        (origin.fields.2.2.1.symm.trans issuerAt.identity.symm)
    exact origin.allocated.trans (congrArg Accepted.allocated sameIssuer)
  have noLater : run.receipt ≤ release.before.nextID := by
    obtain ⟨origin⟩ := history.released_origin empty release member run released
    exact origin.no_later history
  have place : issuerAt.step ∈ releaseAt.prior ∨ issuerAt.step = release := by
    have whole : issuerAt.step ∈ releaseAt.prior ++ release :: releaseAt.later :=
      Eq.mp (congrArg (fun list => issuerAt.step ∈ list) split) issuerAt.member
    rcases List.mem_append.mp whole with prior | remaining
    · exact .inl prior
    · rcases List.mem_cons.mp remaining with current | later
      · exact .inr current
      · have scope := history
        rw [split] at scope
        have lower := scope.cut.2.counter_lower issuerAt.step later
        rw [release.identity.2, issuerAt.identity] at lower
        omega
  return ⟨releaseAt.prior, releaseAt.later, split, issuerAt.step, place, allocated⟩

end Netlib.Protocol.TCP.ReceiveStoreHistory
