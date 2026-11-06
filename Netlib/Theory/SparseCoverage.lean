import Std

/-!
# Sparse byte coverage and original sources

The ledger retains original runs.
It does not hold or release packets.
An exact contained slice keeps the first source.
It adds no coverage.
-/

namespace Netlib.Theory.SparseCoverage

structure Run (Meta : Type) where
  position : Nat
  bytes : List UInt8
  sourceID : Nat
  metadata : Meta
  deriving Repr, BEq, DecidableEq

def Run.limit (run : Run Meta) : Nat := run.position + run.bytes.length

def Run.Before (first second : Run Meta) : Prop := first.limit ≤ second.position

def size (runs : List (Run Meta)) : Nat := (runs.map (fun run => run.bytes.length)).sum

def highEnd : List (Run Meta) → Nat
  | [] => 0
  | head :: tail => max head.limit (highEnd tail)

def frontierFrom (cursor : Nat) : List (Run Meta) → Nat
  | [] => cursor
  | head :: tail => if head.position = cursor then frontierFrom head.limit tail else cursor

structure State (Meta : Type) where
  runs : List (Run Meta) := []
  nextID : Nat := 0
  deriving Repr, BEq, DecidableEq

def initial : State Meta := {}

def State.frontier (state : State Meta) : Nat := frontierFrom 0 state.runs

def State.highEnd (state : State Meta) : Nat := SparseCoverage.highEnd state.runs

def State.count (state : State Meta) : Nat := size state.runs

def State.Covers (state : State Meta) (position : Nat) : Prop :=
  ∃ run ∈ state.runs, run.position ≤ position ∧ position < run.limit

instance (state : State Meta) (position : Nat) : Decidable (state.Covers position) := by
  unfold State.Covers
  infer_instance

def State.Valid (state : State Meta) (bound : Nat) : Prop :=
  state.runs.Pairwise Run.Before ∧
    (∀ run ∈ state.runs, run.bytes ≠ [] ∧ run.limit ≤ bound ∧ run.sourceID < state.nextID) ∧
    (state.runs.map (·.sourceID)).Nodup

instance (state : State Meta) (bound : Nat) : Decidable (state.Valid bound) := by
  unfold State.Valid Run.Before
  infer_instance

inductive Stop where
  | invalid | empty | bounds | overlap | conflict
  deriving Repr, BEq, DecidableEq

structure Placement (Meta : Type) where
  runs : List (Run Meta)
  source : Run Meta
  offset : Nat
  duplicate : Bool
  deriving Repr, BEq, DecidableEq

def Slice (source : Run Meta) (position : Nat) (payload : List UInt8) (offset : Nat) : Prop :=
  source.position + offset = position ∧ offset + payload.length ≤ source.bytes.length ∧
    (source.bytes.drop offset).take payload.length = payload

def place (incoming : Run Meta) : List (Run Meta) → Except Stop (Placement Meta)
  | [] => .ok ⟨[incoming], incoming, 0, false⟩
  | head :: tail =>
    if incoming.limit ≤ head.position then .ok ⟨incoming :: head :: tail, incoming, 0, false⟩
    else if head.limit ≤ incoming.position then do
      let rest ← place incoming tail
      return ⟨head :: rest.runs, rest.source, rest.offset, rest.duplicate⟩
    else if head.position ≤ incoming.position ∧ incoming.limit ≤ head.limit then
      if (head.bytes.drop (incoming.position - head.position)).take incoming.bytes.length = incoming.bytes then
        .ok ⟨head :: tail, head, incoming.position - head.position, true⟩
      else .error .conflict
    else .error .overlap

structure Result (Meta : Type) where
  state : State Meta
  source : Run Meta
  offset : Nat
  novel : Nat
  deriving Repr, BEq, DecidableEq

def current (state : State Meta) (position : Nat) (payload : List UInt8) (metadata : Meta) : Run Meta :=
  ⟨position, payload, state.nextID, metadata⟩

def commit (state : State Meta) (payload : List UInt8) (placed : Placement Meta) : Result Meta :=
  ⟨⟨placed.runs, state.nextID + if placed.duplicate then 0 else 1⟩,
    placed.source, placed.offset, if placed.duplicate then 0 else payload.length⟩

def accept (state : State Meta) (position : Nat) (payload : List UInt8) (metadata : Meta)
    (bound : Nat) : Except Stop (Result Meta) :=
  if ¬state.Valid bound then .error .invalid
  else if payload = [] then .error .empty
  else if bound < position + payload.length then .error .bounds
  else match place (current state position payload metadata) state.runs with
    | .error reason => .error reason
    | .ok placed => .ok (commit state payload placed)

theorem initial_valid (bound : Nat) : (initial : State Meta).Valid bound := by
  simp [initial, State.Valid]

theorem size_append (first second : List (Run Meta)) : size (first ++ second) = size first + size second := by
  simp [size]

theorem place_shape (incoming : Run Meta) (runs : List (Run Meta)) (placed : Placement Meta)
    (accepted : place incoming runs = .ok placed) :
    (placed.duplicate = true ∧ placed.runs = runs) ∨
      (placed.duplicate = false ∧ placed.runs.Perm (runs ++ [incoming])) := by
  induction runs generalizing placed with
  | nil =>
    cases accepted
    exact .inr ⟨rfl, .refl _⟩
  | cons head tail ih =>
    unfold place at accepted
    split at accepted
    · cases accepted
      exact .inr ⟨rfl, by simpa only [List.singleton_append] using
        (List.perm_append_comm : ([incoming] ++ (head :: tail)).Perm ((head :: tail) ++ [incoming]))⟩
    · split at accepted
      · cases chosen : place incoming tail with
        | error reason => simp [chosen, bind, Except.bind] at accepted
        | ok rest =>
          simp only [chosen, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at accepted
          cases accepted
          rcases ih rest chosen with ⟨duplicate, same⟩ | ⟨fresh, permutation⟩
          · exact .inl ⟨duplicate, by simp only [same]⟩
          · exact .inr ⟨fresh, permutation.cons head⟩
      · split at accepted
        · split at accepted
          · cases accepted
            exact .inl ⟨rfl, rfl⟩
          · cases accepted
        · cases accepted

theorem place_members (incoming : Run Meta) (runs : List (Run Meta)) (placed : Placement Meta)
    (accepted : place incoming runs = .ok placed) (run : Run Meta) (member : run ∈ placed.runs) :
    run ∈ runs ∨ run = incoming := by
  rcases place_shape incoming runs placed accepted with ⟨_, same⟩ | ⟨_, permutation⟩
  · exact .inl (same ▸ member)
  · simpa only [List.mem_append, List.mem_singleton] using permutation.mem_iff.mp member

theorem place_old_member (incoming : Run Meta) (runs : List (Run Meta)) (placed : Placement Meta)
    (accepted : place incoming runs = .ok placed) (run : Run Meta) (member : run ∈ runs) : run ∈ placed.runs := by
  rcases place_shape incoming runs placed accepted with ⟨_, same⟩ | ⟨_, permutation⟩
  · exact same ▸ member
  · exact permutation.mem_iff.mpr (List.mem_append_left _ member)

theorem place_size (incoming : Run Meta) (runs : List (Run Meta)) (placed : Placement Meta)
    (accepted : place incoming runs = .ok placed) :
    size placed.runs = size runs + if placed.duplicate then 0 else incoming.bytes.length := by
  rcases place_shape incoming runs placed accepted with ⟨duplicate, same⟩ | ⟨fresh, permutation⟩
  · simp only [same, duplicate, ite_true, Nat.add_zero]
  · have total := List.Perm.sum_nat (permutation.map (fun run => run.bytes.length))
    simpa only [size, List.map_append, List.map_singleton, List.sum_append, List.sum_singleton,
      fresh, Bool.false_eq_true, ite_false] using total

theorem place_pairwise (incoming : Run Meta) (runs : List (Run Meta)) (placed : Placement Meta)
    (ordered : runs.Pairwise Run.Before) (accepted : place incoming runs = .ok placed) :
    placed.runs.Pairwise Run.Before := by
  induction runs generalizing placed with
  | nil => cases accepted; simp
  | cons head tail ih =>
    have order := List.pairwise_cons.mp ordered
    unfold place at accepted
    split at accepted
    · rename_i before
      cases accepted
      apply List.pairwise_cons.mpr
      refine ⟨?_, ordered⟩
      intro run member
      rcases List.mem_cons.mp member with rfl | member
      · exact before
      · have after := order.1 run member
        unfold Run.Before Run.limit at *
        omega
    · split at accepted
      · rename_i after
        cases chosen : place incoming tail with
        | error reason => simp [chosen, bind, Except.bind] at accepted
        | ok rest =>
          simp only [chosen, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at accepted
          cases accepted
          apply List.pairwise_cons.mpr
          refine ⟨?_, ih rest order.2 chosen⟩
          intro run member
          rcases place_members incoming tail rest chosen run member with member | rfl
          · exact order.1 run member
          · exact after
      · split at accepted
        · split at accepted
          · cases accepted; exact ordered
          · cases accepted
        · cases accepted

theorem place_ids (incoming : Run Meta) (runs : List (Run Meta)) (placed : Placement Meta)
    (unique : (runs.map (·.sourceID)).Nodup) (allocated : ∀ run ∈ runs, run.sourceID < incoming.sourceID)
    (accepted : place incoming runs = .ok placed) : (placed.runs.map (·.sourceID)).Nodup := by
  rcases place_shape incoming runs placed accepted with ⟨_, same⟩ | ⟨_, permutation⟩
  · rw [same]
    exact unique
  · have target : ((runs ++ [incoming]).map (·.sourceID)).Nodup := by
      rw [List.map_append]
      apply List.nodup_append.mpr
      refine ⟨unique, by simp, ?_⟩
      intro first firstMember second secondMember same
      obtain ⟨run, member, value⟩ := List.mem_map.mp firstMember
      have bound := allocated run member
      have equal : second = incoming.sourceID := by simpa using secondMember
      rw [value, same, equal] at bound
      exact Nat.lt_irrefl _ bound
    exact (permutation.map (·.sourceID)).nodup_iff.mpr target

theorem place_source (incoming : Run Meta) (runs : List (Run Meta)) (placed : Placement Meta)
    (accepted : place incoming runs = .ok placed) :
    Slice placed.source incoming.position incoming.bytes placed.offset ∧
      ((placed.duplicate = true ∧ placed.source ∈ runs) ∨
        (placed.duplicate = false ∧ placed.source = incoming ∧ placed.offset = 0)) := by
  induction runs generalizing placed with
  | nil =>
    cases accepted
    exact ⟨by simp [Slice], .inr ⟨rfl, rfl, rfl⟩⟩
  | cons head tail ih =>
    unfold place at accepted
    split at accepted
    · cases accepted
      exact ⟨by simp [Slice], .inr ⟨rfl, rfl, rfl⟩⟩
    · split at accepted
      · cases chosen : place incoming tail with
        | error reason => simp [chosen, bind, Except.bind] at accepted
        | ok rest =>
          simp only [chosen, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at accepted
          cases accepted
          obtain ⟨slice, duplicate | fresh⟩ := ih rest chosen
          · exact ⟨slice, .inl ⟨duplicate.1, List.mem_cons_of_mem _ duplicate.2⟩⟩
          · exact ⟨slice, .inr fresh⟩
      · split at accepted
        · rename_i contained
          split at accepted
          · rename_i same
            cases accepted
            refine ⟨⟨?_, ?_, same⟩, .inl ⟨rfl, by simp⟩⟩
            · dsimp only
              omega
            · dsimp only
              unfold Run.limit at contained
              omega
          · cases accepted
        · cases accepted

def Compatible (incoming : Run Meta) (runs : List (Run Meta)) : Prop :=
  ∀ run ∈ runs, incoming.Before run ∨ run.Before incoming ∨
    (run.position ≤ incoming.position ∧ incoming.limit ≤ run.limit ∧
      (run.bytes.drop (incoming.position - run.position)).take incoming.bytes.length = incoming.bytes)

theorem place_exists (incoming : Run Meta) (runs : List (Run Meta)) (compatible : Compatible incoming runs) :
    ∃ placed, place incoming runs = .ok placed := by
  induction runs with
  | nil => exact ⟨⟨[incoming], incoming, 0, false⟩, rfl⟩
  | cons head tail ih =>
    have selected := compatible head (by simp)
    by_cases before : incoming.limit ≤ head.position
    · exact ⟨⟨incoming :: head :: tail, incoming, 0, false⟩, by simp only [place, before, ite_true]⟩
    · by_cases after : head.limit ≤ incoming.position
      · obtain ⟨rest, chosen⟩ := ih (by intro run member; exact compatible run (by simp [member]))
        exact ⟨⟨head :: rest.runs, rest.source, rest.offset, rest.duplicate⟩,
          by simp only [place, before, after, ite_true, ite_false, chosen, bind, Except.bind, pure, Except.pure]⟩
      · obtain ⟨left, right, same⟩ : head.position ≤ incoming.position ∧ incoming.limit ≤ head.limit ∧
          (head.bytes.drop (incoming.position - head.position)).take incoming.bytes.length = incoming.bytes := by
          rcases selected with first | second | contained
          · exact False.elim (before first)
          · exact False.elim (after second)
          · exact contained
        exact ⟨⟨head :: tail, head, incoming.position - head.position, true⟩, by
          simp only [place, before, after, ite_false, left, right, and_self, ite_true, same]⟩

theorem commit_valid (state : State Meta) (position : Nat) (payload : List UInt8) (metadata : Meta)
    (bound : Nat) (placed : Placement Meta) (valid : state.Valid bound) (nonempty : payload ≠ [])
    (inside : position + payload.length ≤ bound)
    (accepted : place (current state position payload metadata) state.runs = .ok placed) :
    (commit state payload placed).state.Valid bound := by
  refine ⟨place_pairwise _ _ _ valid.1 accepted, ?_, place_ids _ _ _ valid.2.2
    (by intro run member; exact (valid.2.1 run member).2.2) accepted⟩
  intro run member
  rcases place_members _ _ _ accepted run member with old | rfl
  · obtain ⟨positive, bounded, allocated⟩ := valid.2.1 run old
    refine ⟨positive, bounded, ?_⟩
    change run.sourceID < state.nextID + _
    omega
  · have fresh : placed.duplicate = false := by
      rcases place_shape _ _ _ accepted with ⟨duplicate, same⟩ | ⟨fresh, _⟩
      · have member : current state position payload metadata ∈ state.runs := same ▸ member
        have allocated := (valid.2.1 _ member).2.2
        exact False.elim (Nat.lt_irrefl _ allocated)
      · exact fresh
    exact ⟨nonempty, inside, by simp only [commit, current, fresh, Bool.false_eq_true, ite_false]; omega⟩

theorem accept_exists (state : State Meta) (position : Nat) (payload : List UInt8) (metadata : Meta)
    (bound : Nat) (valid : state.Valid bound) (nonempty : payload ≠ [])
    (inside : position + payload.length ≤ bound)
    (compatible : Compatible (current state position payload metadata) state.runs) :
    ∃ result, accept state position payload metadata bound = .ok result := by
  obtain ⟨placed, chosen⟩ := place_exists _ _ compatible
  exact ⟨commit state payload placed, by
    simp only [accept, valid, not_true_eq_false, ite_false, nonempty, Nat.not_lt.mpr inside, chosen]⟩

theorem accept_stages (state : State Meta) (position : Nat) (payload : List UInt8) (metadata : Meta)
    (bound : Nat) (result : Result Meta) (accepted : accept state position payload metadata bound = .ok result) :
    state.Valid bound ∧ payload ≠ [] ∧ position + payload.length ≤ bound ∧
      ∃ placed, place (current state position payload metadata) state.runs = .ok placed ∧
        result = commit state payload placed := by
  unfold accept at accepted
  split at accepted
  · cases accepted
  · rename_i valid
    split at accepted
    · cases accepted
    · rename_i nonempty
      split at accepted
      · cases accepted
      · rename_i inside
        cases chosen : place (current state position payload metadata) state.runs with
        | error reason => simp only [chosen] at accepted; cases accepted
        | ok placed =>
          simp only [chosen, Except.ok.injEq] at accepted
          exact ⟨Decidable.not_not.mp valid, nonempty, Nat.le_of_not_lt inside, placed, rfl, accepted.symm⟩

theorem accept_valid (state : State Meta) (position : Nat) (payload : List UInt8) (metadata : Meta)
    (bound : Nat) (result : Result Meta) (accepted : accept state position payload metadata bound = .ok result) :
    result.state.Valid bound := by
  obtain ⟨valid, nonempty, inside, placed, chosen, rfl⟩ := accept_stages _ _ _ _ _ _ accepted
  exact commit_valid state position payload metadata bound placed valid nonempty inside chosen


theorem highEnd_mem (runs : List (Run Meta)) (run : Run Meta) (member : run ∈ runs) :
    run.limit ≤ highEnd runs := by
  induction runs with
  | nil => simp at member
  | cons head tail ih =>
    rcases List.mem_cons.mp member with rfl | member
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih member) (Nat.le_max_right _ _)

theorem highEnd_le (runs : List (Run Meta)) (bound : Nat)
    (bounded : ∀ run ∈ runs, run.limit ≤ bound) : highEnd runs ≤ bound := by
  induction runs with
  | nil => exact Nat.zero_le _
  | cons head tail ih =>
    exact Nat.max_le.mpr ⟨bounded head (by simp), ih (by intro run member; exact bounded run (by simp [member]))⟩

theorem State.limit_le_highEnd (state : State Meta) (run : Run Meta) (member : run ∈ state.runs) :
    run.limit ≤ state.highEnd := highEnd_mem _ _ member

theorem State.highEnd_bound (state : State Meta) (bound : Nat) (valid : state.Valid bound) :
    state.highEnd ≤ bound := highEnd_le _ _ (by intro run member; exact (valid.2.1 run member).2.1)

theorem frontierFrom_le_highEnd (cursor : Nat) (runs : List (Run Meta)) :
    frontierFrom cursor runs ≤ max cursor (highEnd runs) := by
  induction runs generalizing cursor with
  | nil => simp [frontierFrom, highEnd]
  | cons head tail ih =>
    unfold frontierFrom
    split
    · exact Nat.le_trans (ih head.limit) (Nat.le_max_right _ _)
    · exact Nat.le_max_left _ _

theorem State.frontier_le_highEnd (state : State Meta) : state.frontier ≤ state.highEnd := by
  simpa only [State.frontier, State.highEnd, Nat.zero_max] using frontierFrom_le_highEnd 0 state.runs

theorem frontierFrom_le_size (cursor : Nat) (runs : List (Run Meta)) :
    frontierFrom cursor runs ≤ cursor + size runs := by
  induction runs generalizing cursor with
  | nil => simp [frontierFrom, size]
  | cons head tail ih =>
    unfold frontierFrom
    split
    · rename_i same
      have bound := ih head.limit
      simp only [size, List.map_cons, List.sum_cons] at *
      unfold Run.limit at bound ⊢
      omega
    · exact Nat.le_add_right _ _

theorem State.frontier_le_count (state : State Meta) : state.frontier ≤ state.count := by
  simpa only [State.frontier, State.count, Nat.zero_add] using frontierFrom_le_size 0 state.runs

theorem size_bound (cursor bound : Nat) (runs : List (Run Meta)) (ordered : runs.Pairwise Run.Before)
    (forward : ∀ run ∈ runs, cursor ≤ run.position) (bounded : ∀ run ∈ runs, run.limit ≤ bound) :
    size runs ≤ bound - cursor := by
  induction runs generalizing cursor with
  | nil => simp [size]
  | cons head tail ih =>
    obtain ⟨after, sorted⟩ := List.pairwise_cons.mp ordered
    have first := forward head (by simp)
    have last := bounded head (by simp)
    have remaining := ih head.limit sorted after (by intro run member; exact bounded run (by simp [member]))
    simp only [size, List.map_cons, List.sum_cons]
    unfold size Run.limit at remaining
    unfold Run.limit at last
    omega

theorem State.count_le_highEnd (state : State Meta) (bound : Nat) (valid : state.Valid bound) :
    state.count ≤ state.highEnd := by
  simpa only [State.count, Nat.sub_zero] using size_bound 0 state.highEnd state.runs valid.1
    (by intro run member; exact Nat.zero_le _) (by intro run member; exact state.limit_le_highEnd run member)

theorem place_source_member (incoming : Run Meta) (runs : List (Run Meta)) (placed : Placement Meta)
    (accepted : place incoming runs = .ok placed) : placed.source ∈ placed.runs := by
  rcases (place_source _ _ _ accepted).2 with ⟨_, old⟩ | ⟨fresh, same, _⟩
  · exact place_old_member _ _ _ accepted _ old
  · rcases place_shape _ _ _ accepted with ⟨duplicate, _⟩ | ⟨_, permutation⟩
    · simp only [fresh, Bool.false_eq_true] at duplicate
    · rw [same]
      exact permutation.mem_iff.mpr (by simp)

theorem accept_source (state : State Meta) (position : Nat) (payload : List UInt8) (metadata : Meta)
    (bound : Nat) (result : Result Meta) (accepted : accept state position payload metadata bound = .ok result) :
    result.source ∈ result.state.runs ∧ Slice result.source position payload result.offset := by
  obtain ⟨_, _, _, placed, chosen, rfl⟩ := accept_stages _ _ _ _ _ _ accepted
  exact ⟨place_source_member _ _ _ chosen, (place_source _ _ _ chosen).1⟩

theorem accept_cases (state : State Meta) (position : Nat) (payload : List UInt8) (metadata : Meta)
    (bound : Nat) (result : Result Meta) (accepted : accept state position payload metadata bound = .ok result) :
    (result.novel = 0 ∧ result.state = state ∧ result.source ∈ state.runs) ∨
      (result.novel = payload.length ∧ result.source = current state position payload metadata ∧
        result.offset = 0 ∧ result.state.nextID = state.nextID + 1) := by
  obtain ⟨_, _, _, placed, chosen, rfl⟩ := accept_stages _ _ _ _ _ _ accepted
  rcases (place_source _ _ _ chosen).2 with ⟨duplicate, old⟩ | ⟨fresh, same, offset⟩
  · have runs : placed.runs = state.runs := by
      rcases place_shape _ _ _ chosen with ⟨_, same⟩ | ⟨fresh, _⟩
      · exact same
      · simp only [duplicate, Bool.true_eq_false] at fresh
    exact .inl ⟨by simp [commit, duplicate], by simp [commit, duplicate, runs], old⟩
  · exact .inr ⟨by simp [commit, fresh], same, offset, by simp [commit, fresh]⟩

theorem accept_old_member (state : State Meta) (position : Nat) (payload : List UInt8) (metadata : Meta)
    (bound : Nat) (result : Result Meta) (accepted : accept state position payload metadata bound = .ok result)
    (run : Run Meta) (member : run ∈ state.runs) : run ∈ result.state.runs := by
  obtain ⟨_, _, _, placed, chosen, rfl⟩ := accept_stages _ _ _ _ _ _ accepted
  exact place_old_member _ _ _ chosen _ member

theorem accept_count (state : State Meta) (position : Nat) (payload : List UInt8) (metadata : Meta)
    (bound : Nat) (result : Result Meta) (accepted : accept state position payload metadata bound = .ok result) :
    result.state.count = state.count + result.novel := by
  obtain ⟨_, _, _, placed, chosen, rfl⟩ := accept_stages _ _ _ _ _ _ accepted
  exact place_size _ _ _ chosen

theorem accept_count_mono (state : State Meta) (position : Nat) (payload : List UInt8) (metadata : Meta)
    (bound : Nat) (result : Result Meta) (accepted : accept state position payload metadata bound = .ok result) :
    state.count ≤ result.state.count := by
  rw [accept_count _ _ _ _ _ _ accepted]
  exact Nat.le_add_right _ _

theorem accept_coverage_mono (state : State Meta) (position : Nat) (payload : List UInt8) (metadata : Meta)
    (bound : Nat) (result : Result Meta) (accepted : accept state position payload metadata bound = .ok result)
    (index : Nat) (covered : state.Covers index) : result.state.Covers index := by
  obtain ⟨run, member, inside⟩ := covered
  exact ⟨run, accept_old_member _ _ _ _ _ _ accepted _ member, inside⟩

theorem accept_highEnd_mono (state : State Meta) (position : Nat) (payload : List UInt8) (metadata : Meta)
    (bound : Nat) (result : Result Meta) (accepted : accept state position payload metadata bound = .ok result) :
    state.highEnd ≤ result.state.highEnd := highEnd_le _ _ (by
  intro run member
  exact result.state.limit_le_highEnd run (accept_old_member _ _ _ _ _ _ accepted _ member))

theorem Slice.limit (source : Run Meta) (position : Nat) (payload : List UInt8) (offset : Nat)
    (slice : Slice source position payload offset) : position + payload.length ≤ source.limit := by
  unfold Slice Run.limit at *
  omega

theorem Slice.index (source : Run Meta) (position : Nat) (payload : List UInt8) (offset : Nat)
    (slice : Slice source position payload offset) (index : Nat) (byte : UInt8)
    (selected : payload[index]? = some byte) : source.bytes[offset + index]? = some byte := by
  have inside := (List.getElem?_eq_some_iff.mp selected).1
  rw [← slice.2.2, List.getElem?_take_of_lt inside, List.getElem?_drop] at selected
  exact selected

theorem accept_index (state : State Meta) (position : Nat) (payload : List UInt8) (metadata : Meta)
    (bound : Nat) (result : Result Meta) (accepted : accept state position payload metadata bound = .ok result)
    (index : Nat) (byte : UInt8) (selected : payload[index]? = some byte) :
    result.source.bytes[result.offset + index]? = some byte :=
  Slice.index _ _ _ _ (accept_source _ _ _ _ _ _ accepted).2 index byte selected

theorem accept_highEnd (state : State Meta) (position : Nat) (payload : List UInt8) (metadata : Meta)
    (bound : Nat) (result : Result Meta) (accepted : accept state position payload metadata bound = .ok result) :
    result.state.highEnd = max state.highEnd (position + payload.length) := by
  apply Nat.le_antisymm
  · obtain ⟨_, _, _, placed, chosen, rfl⟩ := accept_stages _ _ _ _ _ _ accepted
    apply highEnd_le
    intro run member
    rcases place_members _ _ _ chosen run member with old | rfl
    · exact Nat.le_trans (state.limit_le_highEnd run old) (Nat.le_max_left _ _)
    · exact Nat.le_max_right _ _
  · apply Nat.max_le.mpr
    refine ⟨accept_highEnd_mono _ _ _ _ _ _ accepted, ?_⟩
    obtain ⟨member, slice⟩ := accept_source _ _ _ _ _ _ accepted
    exact Nat.le_trans (Slice.limit _ _ _ _ slice) (result.state.limit_le_highEnd _ member)


theorem frontierFrom_ge (cursor : Nat) (runs : List (Run Meta)) : cursor ≤ frontierFrom cursor runs := by
  induction runs generalizing cursor with
  | nil => exact Nat.le_refl _
  | cons head tail ih =>
    unfold frontierFrom
    split
    · rename_i same
      have next := ih head.limit
      unfold Run.limit at next ⊢
      omega
    · exact Nat.le_refl _

theorem frontierFrom_spec (cursor : Nat) (runs : List (Run Meta))
    (ordered : runs.Pairwise Run.Before) (forward : ∀ run ∈ runs, cursor ≤ run.position) :
    (∀ index, cursor ≤ index → index < frontierFrom cursor runs →
      ∃ run ∈ runs, run.position ≤ index ∧ index < run.limit) ∧
      ¬(∃ run ∈ runs, run.position ≤ frontierFrom cursor runs ∧ frontierFrom cursor runs < run.limit) := by
  induction runs generalizing cursor with
  | nil =>
    constructor
    · intro index lower upper
      simp only [frontierFrom] at upper
      omega
    · rintro ⟨run, member, _⟩
      cases member
  | cons head tail ih =>
    obtain ⟨after, sorted⟩ := List.pairwise_cons.mp ordered
    by_cases same : head.position = cursor
    · simp only [frontierFrom, same, ite_true]
      obtain ⟨covered, hole⟩ := ih head.limit sorted after
      constructor
      · intro index lower upper
        by_cases inside : index < head.limit
        · exact ⟨head, by simp, by omega, inside⟩
        · obtain ⟨run, member, included⟩ := covered index (by omega) upper
          exact ⟨run, List.mem_cons_of_mem _ member, included⟩
      · rintro ⟨run, member, lower, upper⟩
        rcases List.mem_cons.mp member with rfl | member
        · have first := frontierFrom_ge run.limit tail
          omega
        · exact hole ⟨run, member, lower, upper⟩
    · simp only [frontierFrom, same, ite_false]
      constructor
      · intro index lower upper
        omega
      · rintro ⟨run, member, lower, upper⟩
        rcases List.mem_cons.mp member with rfl | member
        · have first := forward run (by simp)
          omega
        · have first := forward head (by simp)
          have later := after run member
          unfold Run.Before Run.limit at later
          omega

theorem State.covered_of_lt_frontier (state : State Meta) (bound : Nat) (valid : state.Valid bound)
    (position : Nat) (before : position < state.frontier) : state.Covers position :=
  (frontierFrom_spec 0 state.runs valid.1 (by intro run member; exact Nat.zero_le _)).1
    position (Nat.zero_le _) before

theorem State.frontier_not_covered (state : State Meta) (bound : Nat) (valid : state.Valid bound) :
    ¬state.Covers state.frontier :=
  (frontierFrom_spec 0 state.runs valid.1 (by intro run member; exact Nat.zero_le _)).2

theorem State.frontier_le_of_not_covered (state : State Meta) (bound : Nat) (valid : state.Valid bound)
    (position : Nat) (hole : ¬state.Covers position) : state.frontier ≤ position := by
  by_cases earlier : state.frontier ≤ position
  · exact earlier
  · exact False.elim (hole (state.covered_of_lt_frontier bound valid position (by omega)))

theorem accept_frontier_mono (state : State Meta) (position : Nat) (payload : List UInt8) (metadata : Meta)
    (bound : Nat) (result : Result Meta) (accepted : accept state position payload metadata bound = .ok result) :
    state.frontier ≤ result.state.frontier := by
  have beforeValid := (accept_stages _ _ _ _ _ _ accepted).1
  have afterValid := accept_valid _ _ _ _ _ _ accepted
  by_cases earlier : state.frontier ≤ result.state.frontier
  · exact earlier
  · have before : result.state.frontier < state.frontier := by omega
    have old := state.covered_of_lt_frontier bound beforeValid _ before
    exact False.elim (result.state.frontier_not_covered bound afterValid
      (accept_coverage_mono _ _ _ _ _ _ accepted _ old))


theorem accept_members (state : State Meta) (position : Nat) (payload : List UInt8) (metadata : Meta)
    (bound : Nat) (result : Result Meta) (accepted : accept state position payload metadata bound = .ok result)
    (run : Run Meta) (member : run ∈ result.state.runs) :
    run ∈ state.runs ∨ run = current state position payload metadata := by
  obtain ⟨_, _, _, placed, chosen, rfl⟩ := accept_stages _ _ _ _ _ _ accepted
  exact place_members _ _ _ chosen _ member

theorem Slice.covers (source : Run Meta) (position : Nat) (payload : List UInt8) (offset index : Nat)
    (slice : Slice source position payload offset) (lower : position ≤ index)
    (upper : index < position + payload.length) : source.position ≤ index ∧ index < source.limit := by
  have limit := Slice.limit _ _ _ _ slice
  obtain ⟨start, _, _⟩ := slice
  omega

theorem accept_coverage (state : State Meta) (position : Nat) (payload : List UInt8) (metadata : Meta)
    (bound : Nat) (result : Result Meta) (accepted : accept state position payload metadata bound = .ok result)
    (index : Nat) : result.state.Covers index ↔ state.Covers index ∨ position ≤ index ∧ index < position + payload.length := by
  constructor
  · rintro ⟨run, member, lower, upper⟩
    rcases accept_members _ _ _ _ _ _ accepted run member with old | rfl
    · exact .inl ⟨run, old, lower, upper⟩
    · exact .inr ⟨lower, upper⟩
  · rintro (old | ⟨lower, upper⟩)
    · exact accept_coverage_mono _ _ _ _ _ _ accepted index old
    · obtain ⟨member, slice⟩ := accept_source _ _ _ _ _ _ accepted
      exact ⟨result.source, member, Slice.covers _ _ _ _ _ slice lower upper⟩


theorem covering_unique (runs : List (Run Meta)) (ordered : runs.Pairwise Run.Before)
    (first second : Run Meta) (firstMember : first ∈ runs) (secondMember : second ∈ runs)
    (position : Nat) (firstCover : first.position ≤ position ∧ position < first.limit)
    (secondCover : second.position ≤ position ∧ position < second.limit) : first = second := by
  induction runs with
  | nil => cases firstMember
  | cons head tail ih =>
    obtain ⟨after, sorted⟩ := List.pairwise_cons.mp ordered
    rcases List.mem_cons.mp firstMember with rfl | firstTail
    · rcases List.mem_cons.mp secondMember with rfl | secondTail
      · rfl
      · have before := after second secondTail
        unfold Run.Before at before
        omega
    · rcases List.mem_cons.mp secondMember with rfl | secondTail
      · have before := after first firstTail
        unfold Run.Before at before
        omega
      · exact ih sorted firstTail secondTail

theorem State.covering_unique (state : State Meta) (bound : Nat) (valid : state.Valid bound)
    (first second : Run Meta) (firstMember : first ∈ state.runs) (secondMember : second ∈ state.runs)
    (position : Nat) (firstCover : first.position ≤ position ∧ position < first.limit)
    (secondCover : second.position ≤ position ∧ position < second.limit) : first = second :=
  SparseCoverage.covering_unique state.runs valid.1 first second firstMember secondMember position firstCover secondCover

theorem accept_first_source (state : State Meta) (position : Nat) (payload : List UInt8) (metadata : Meta)
    (bound : Nat) (result : Result Meta) (accepted : accept state position payload metadata bound = .ok result)
    (source : Run Meta) (member : source ∈ state.runs) (offset : Nat)
    (slice : Slice source position payload offset) :
    result.state = state ∧ result.source = source ∧ result.offset = offset ∧ result.novel = 0 := by
  obtain ⟨beforeValid, nonempty, _, _⟩ := accept_stages _ _ _ _ _ _ accepted
  obtain ⟨sourceMember, actualSlice⟩ := accept_source _ _ _ _ _ _ accepted
  have positive : 0 < payload.length := List.length_pos_iff.mpr nonempty
  have same : result.source = source := result.state.covering_unique bound (accept_valid _ _ _ _ _ _ accepted)
    result.source source sourceMember (accept_old_member _ _ _ _ _ _ accepted source member) position
    (Slice.covers _ _ _ _ _ actualSlice (Nat.le_refl _) (by omega))
    (Slice.covers _ _ _ _ _ slice (Nat.le_refl _) (by omega))
  have offsetEq : result.offset = offset := by
    have actual := actualSlice.1
    rw [same] at actual
    have original := slice.1
    omega
  rcases accept_cases _ _ _ _ _ _ accepted with ⟨novel, stateEq, _⟩ | ⟨_, fresh, _, _⟩
  · exact ⟨stateEq, same, offsetEq, novel⟩
  · have allocated := (beforeValid.2.1 source member).2.2
    have identity := congrArg Run.sourceID (same.symm.trans fresh)
    change source.sourceID = state.nextID at identity
    omega

theorem accept_source_bounds (state : State Meta) (position : Nat) (payload : List UInt8) (metadata : Meta)
    (bound : Nat) (result : Result Meta) (accepted : accept state position payload metadata bound = .ok result) :
    result.source.limit ≤ result.state.highEnd ∧ result.state.highEnd ≤ bound :=
  ⟨result.state.limit_le_highEnd result.source (accept_source _ _ _ _ _ _ accepted).1,
    result.state.highEnd_bound bound (accept_valid _ _ _ _ _ _ accepted)⟩

theorem accept_source_position (state : State Meta) (position : Nat) (payload : List UInt8) (metadata : Meta)
    (bound : Nat) (result : Result Meta) (accepted : accept state position payload metadata bound = .ok result)
    (index : Nat) : result.source.position + (result.offset + index) = position + index := by
  have coordinate := (accept_source _ _ _ _ _ _ accepted).2.1
  omega


theorem accept_fresh_exists (state : State Meta) (position : Nat) (payload : List UInt8) (metadata : Meta)
    (bound : Nat) (valid : state.Valid bound) (nonempty : payload ≠ [])
    (inside : position + payload.length ≤ bound)
    (disjoint : ∀ run ∈ state.runs, (current state position payload metadata).Before run ∨
      run.Before (current state position payload metadata)) :
    ∃ result, accept state position payload metadata bound = .ok result ∧ result.novel = payload.length ∧
      result.source = current state position payload metadata ∧ result.offset = 0 ∧
      result.state.nextID = state.nextID + 1 := by
  obtain ⟨result, accepted⟩ := accept_exists state position payload metadata bound valid nonempty inside (by
    intro run member
    rcases disjoint run member with before | after
    · exact .inl before
    · exact .inr (.inl after))
  rcases accept_cases _ _ _ _ _ _ accepted with ⟨_, _, member⟩ | fresh
  · have positive : 0 < payload.length := List.length_pos_iff.mpr nonempty
    have slice := (accept_source _ _ _ _ _ _ accepted).2
    obtain ⟨lower, upper⟩ := Slice.covers _ _ _ _ position slice (Nat.le_refl _) (by omega)
    rcases disjoint result.source member with before | after
    · change position + payload.length ≤ result.source.position at before
      omega
    · change result.source.limit ≤ position at after
      omega
  · exact ⟨result, accepted, fresh⟩

end Netlib.Theory.SparseCoverage
