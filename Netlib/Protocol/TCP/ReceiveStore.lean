import Std

/-!
# Bounded receive spans with receipt provenance

The store retains whole non-overlapping payloads and their first receipt metadata.
It allocates receipt identities while processing actual nonempty input.
Release preserves those identities across a gap.
The budget excludes ordered unread bytes. Held bytes consume physical storage separately.
-/

namespace Netlib.Protocol.TCP.ReceiveStore

structure Run (Meta : Type) where
  position : Nat
  bytes : List UInt8
  receipt : Nat
  metadata : Meta
  deriving Repr, BEq, DecidableEq

def Run.limit (run : Run Meta) : Nat := run.position + run.bytes.length

def Run.Before (first second : Run Meta) : Prop := first.limit ≤ second.position

def bytes (runs : List (Run Meta)) : List UInt8 := runs.flatMap (·.bytes)

def size (runs : List (Run Meta)) : Nat := (runs.map (fun run => run.bytes.length)).sum

def Contiguous : Nat → List (Run Meta) → Prop
  | _, [] => True
  | frontier, run :: rest => run.position = frontier ∧ Contiguous run.limit rest

structure State (Meta : Type) where
  frontier : Nat := 0
  nextID : Nat := 0
  held : List (Run Meta) := []
  seenGap : Bool := false
  deriving Repr, BEq, DecidableEq

def initial : State Meta := {}

def State.heldBytes (state : State Meta) : Nat := size state.held

def State.physicalFree (state : State Meta) (budget : Nat) : Nat := budget - state.heldBytes

def State.Valid (state : State Meta) (edge budget : Nat) : Prop :=
  state.frontier ≤ edge ∧ edge - state.frontier ≤ budget ∧
    state.held.Pairwise Run.Before ∧
    (∀ run ∈ state.held, run.bytes ≠ [] ∧ state.frontier < run.position ∧
      run.limit ≤ edge ∧ run.receipt < state.nextID) ∧
    (state.held.map (·.receipt)).Nodup ∧ state.heldBytes ≤ budget

instance (state : State Meta) (edge budget : Nat) : Decidable (state.Valid edge budget) := by
  unfold State.Valid Run.Before
  infer_instance

inductive Stop where
  | invalid | empty | left | right | overlap | conflict | capacity
  deriving Repr, BEq, DecidableEq

structure Placed (Meta : Type) where
  runs : List (Run Meta)
  duplicate : Bool
  deriving Repr, BEq, DecidableEq

def place (incoming : Run Meta) : List (Run Meta) → Except Stop (Placed Meta)
  | [] => .ok ⟨[incoming], false⟩
  | head :: tail =>
    if incoming.limit ≤ head.position then .ok ⟨incoming :: head :: tail, false⟩
    else if head.limit ≤ incoming.position then do
      let rest ← place incoming tail
      return ⟨head :: rest.runs, rest.duplicate⟩
    else if incoming.position = head.position ∧ incoming.bytes = head.bytes then
      .ok ⟨head :: tail, true⟩
    else if incoming.position = head.position ∧ incoming.limit = head.limit then .error .conflict
    else .error .overlap

structure Drain (Meta : Type) where
  frontier : Nat
  released : List (Run Meta)
  held : List (Run Meta)
  deriving Repr, BEq, DecidableEq

def drain (frontier : Nat) : List (Run Meta) → Drain Meta
  | [] => ⟨frontier, [], []⟩
  | head :: tail =>
    if head.position = frontier then
      let next := drain head.limit tail
      ⟨next.frontier, head :: next.released, next.held⟩
    else ⟨frontier, [], head :: tail⟩

structure Result (Meta : Type) where
  state : State Meta
  receiptID : Nat
  novel : Nat
  released : List (Run Meta)
  duplicate : Bool
  deriving Repr, BEq, DecidableEq

def current (state : State Meta) (position : Nat) (payload : List UInt8) (metadata : Meta) : Run Meta :=
  ⟨position, payload, state.nextID, metadata⟩

def accept (state : State Meta) (position : Nat) (payload : List UInt8) (metadata : Meta)
    (edge budget : Nat) : Except Stop (Result Meta) :=
  if ¬state.Valid edge budget then .error .invalid
  else if payload = [] then .error .empty
  else if position < state.frontier then .error .left
  else if edge < position + payload.length then .error .right
  else match place (current state position payload metadata) state.held with
    | .error reason => .error reason
    | .ok placed =>
      let novel := if placed.duplicate then 0 else payload.length
      if budget < state.heldBytes + novel then .error .capacity
      else
        let released := drain state.frontier placed.runs
        let after : State Meta := ⟨released.frontier, state.nextID + 1, released.held,
          state.seenGap || decide (state.frontier < position)⟩
        if after.Valid edge (budget - size released.released) then
          .ok ⟨after, state.nextID, novel, released.released, placed.duplicate⟩
        else .error .invalid

theorem size_append (first second : List (Run Meta)) : size (first ++ second) = size first + size second := by
  simp [size]

theorem size_bytes (runs : List (Run Meta)) : (bytes runs).length = size runs := by
  simp [bytes, size, List.length_flatMap]

theorem initial_valid (edge budget : Nat) (bounded : edge ≤ budget) :
    (initial : State Meta).Valid edge budget := by
  simp [initial, State.Valid, State.heldBytes, size, bounded]

theorem State.valid_mono (state : State Meta) (oldEdge oldBudget newEdge newBudget : Nat)
    (valid : state.Valid oldEdge oldBudget) (edge : oldEdge ≤ newEdge) (budget : oldBudget ≤ newBudget)
    (reservation : newEdge - state.frontier ≤ newBudget) : state.Valid newEdge newBudget := by
  refine ⟨Nat.le_trans valid.1 edge, reservation, valid.2.2.1, ?_, valid.2.2.2.2.1,
    Nat.le_trans valid.2.2.2.2.2 budget⟩
  intro run member
  obtain ⟨nonempty, forward, before, allocated⟩ := valid.2.2.2.1 run member
  exact ⟨nonempty, forward, Nat.le_trans before edge, allocated⟩

theorem size_bound (frontier edge : Nat) (runs : List (Run Meta)) (ordered : runs.Pairwise Run.Before)
    (forward : ∀ run ∈ runs, frontier ≤ run.position) (bounded : ∀ run ∈ runs, run.limit ≤ edge) :
    size runs ≤ edge - frontier := by
  induction runs generalizing frontier with
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

theorem State.heldBytes_bound (state : State Meta) (edge budget : Nat) (valid : state.Valid edge budget) :
    state.heldBytes ≤ edge - state.frontier := by
  apply size_bound state.frontier edge state.held valid.2.2.1
  · intro run member
    exact Nat.le_of_lt (valid.2.2.2.1 run member).2.1
  · intro run member
    exact (valid.2.2.2.1 run member).2.2.1

theorem drain_partition (frontier : Nat) (runs : List (Run Meta)) :
    (drain frontier runs).released ++ (drain frontier runs).held = runs := by
  induction runs generalizing frontier with
  | nil => rfl
  | cons head tail ih =>
    unfold drain
    split
    · simp only [List.cons_append]
      rw [ih]
    · rfl

theorem drain_contiguous (frontier : Nat) (runs : List (Run Meta)) :
    Contiguous frontier (drain frontier runs).released := by
  induction runs generalizing frontier with
  | nil => trivial
  | cons head tail ih =>
    unfold drain
    split
    · rename_i same
      exact ⟨same, ih _⟩
    · trivial

theorem drain_frontier (frontier : Nat) (runs : List (Run Meta)) :
    (drain frontier runs).frontier = frontier + size (drain frontier runs).released := by
  induction runs generalizing frontier with
  | nil => simp [drain, size]
  | cons head tail ih =>
    unfold drain
    split
    · rename_i same
      simp only [size, List.map_cons, List.sum_cons]
      have step := ih head.limit
      unfold size at step
      rw [step, Run.limit, same]
      omega
    · simp [size]

theorem place_shape (incoming : Run Meta) (runs : List (Run Meta)) (placed : Placed Meta)
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
        · cases accepted
          exact .inl ⟨rfl, rfl⟩
        · split at accepted <;> cases accepted

theorem place_members (incoming : Run Meta) (runs : List (Run Meta)) (placed : Placed Meta)
    (accepted : place incoming runs = .ok placed) (run : Run Meta) (member : run ∈ placed.runs) :
    run ∈ runs ∨ run = incoming := by
  rcases place_shape incoming runs placed accepted with ⟨_, same⟩ | ⟨_, permutation⟩
  · exact .inl (same ▸ member)
  · simpa only [List.mem_append, List.mem_singleton] using permutation.mem_iff.mp member

theorem place_old_member (incoming : Run Meta) (runs : List (Run Meta)) (placed : Placed Meta)
    (accepted : place incoming runs = .ok placed) (run : Run Meta) (member : run ∈ runs) : run ∈ placed.runs := by
  rcases place_shape incoming runs placed accepted with ⟨_, same⟩ | ⟨_, permutation⟩
  · exact same ▸ member
  · exact permutation.mem_iff.mpr (List.mem_append_left _ member)

theorem place_size (incoming : Run Meta) (runs : List (Run Meta)) (placed : Placed Meta)
    (accepted : place incoming runs = .ok placed) :
    size placed.runs = size runs + if placed.duplicate then 0 else incoming.bytes.length := by
  rcases place_shape incoming runs placed accepted with ⟨duplicate, same⟩ | ⟨fresh, permutation⟩
  · simp only [same, duplicate, ite_true, Nat.add_zero]
  · have lengths := permutation.map (fun run => run.bytes.length)
    have total := List.Perm.sum_nat lengths
    simpa only [size, List.map_append, List.map_singleton, List.sum_append, List.sum_singleton,
      fresh, Bool.false_eq_true, ite_false] using total

theorem place_pairwise (incoming : Run Meta) (runs : List (Run Meta)) (placed : Placed Meta)
    (ordered : runs.Pairwise Run.Before) (accepted : place incoming runs = .ok placed) :
    placed.runs.Pairwise Run.Before := by
  induction runs generalizing placed with
  | nil =>
    cases accepted
    simp
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
        · cases accepted
          exact ordered
        · split at accepted <;> cases accepted

theorem drain_pairwise (frontier : Nat) (runs : List (Run Meta)) (ordered : runs.Pairwise Run.Before) :
    (drain frontier runs).released.Pairwise Run.Before ∧ (drain frontier runs).held.Pairwise Run.Before := by
  rw [← drain_partition frontier runs] at ordered
  exact ⟨(List.pairwise_append.mp ordered).1, (List.pairwise_append.mp ordered).2.1⟩

theorem drain_bound (frontier edge : Nat) (runs : List (Run Meta)) (initialBound : frontier ≤ edge)
    (bounded : ∀ run ∈ runs, run.limit ≤ edge) : (drain frontier runs).frontier ≤ edge := by
  induction runs generalizing frontier with
  | nil => exact initialBound
  | cons head tail ih =>
    unfold drain
    split
    · apply ih
      · exact bounded head (by simp)
      · intro run member
        exact bounded run (by simp [member])
    · exact initialBound

theorem drain_normalized (frontier : Nat) (runs : List (Run Meta)) (ordered : runs.Pairwise Run.Before)
    (forward : ∀ run ∈ runs, frontier ≤ run.position) :
    ∀ run ∈ (drain frontier runs).held, (drain frontier runs).frontier < run.position := by
  induction runs generalizing frontier with
  | nil => intro run member; simp [drain] at member
  | cons head tail ih =>
    have order := List.pairwise_cons.mp ordered
    unfold drain
    split
    · apply ih _ order.2
      intro run member
      exact order.1 run member
    · rename_i different
      intro run member
      change frontier < run.position
      have first := forward head (by simp)
      rcases List.mem_cons.mp member with rfl | member
      · omega
      · have later := order.1 run member
        unfold Run.Before Run.limit at later
        omega

theorem drain_members (frontier : Nat) (runs : List (Run Meta)) (run : Run Meta)
    (member : run ∈ (drain frontier runs).released ∨ run ∈ (drain frontier runs).held) : run ∈ runs := by
  rw [← drain_partition frontier runs]
  exact List.mem_append.mpr member

theorem Contiguous.position (frontier : Nat) (runs : List (Run Meta)) (contiguous : Contiguous frontier runs)
    (run : Run Meta) (member : run ∈ runs) :
    ∃ prior later, runs = prior ++ run :: later ∧ run.position = frontier + size prior := by
  induction runs generalizing frontier with
  | nil => simp at member
  | cons head tail ih =>
    rcases contiguous with ⟨first, rest⟩
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨[], tail, rfl, by simpa [size] using first⟩
    · obtain ⟨prior, later, split, position⟩ := ih head.limit rest member
      refine ⟨head :: prior, later, by simp only [split, List.cons_append], ?_⟩
      simp only [size, List.map_cons, List.sum_cons]
      rw [position, Run.limit, first]
      simp only [size]
      omega

theorem accept_stages (state : State Meta) (position : Nat) (payload : List UInt8) (metadata : Meta)
    (edge budget : Nat) (result : Result Meta)
    (accepted : accept state position payload metadata edge budget = .ok result) :
    ∃ placed, place (current state position payload metadata) state.held = .ok placed ∧
      result = ⟨⟨(drain state.frontier placed.runs).frontier, state.nextID + 1,
        (drain state.frontier placed.runs).held, state.seenGap || decide (state.frontier < position)⟩,
        state.nextID, (if placed.duplicate then 0 else payload.length),
        (drain state.frontier placed.runs).released, placed.duplicate⟩ ∧
      state.Valid edge budget ∧ payload ≠ [] ∧ state.frontier ≤ position ∧
      position + payload.length ≤ edge ∧
      state.heldBytes + (if placed.duplicate then 0 else payload.length) ≤ budget ∧
      result.state.Valid edge (budget - size result.released) := by
  unfold accept at accepted
  split at accepted
  · cases accepted
  · rename_i valid
    split at accepted
    · cases accepted
    · rename_i nonempty
      split at accepted
      · cases accepted
      · rename_i forward
        split at accepted
        · cases accepted
        · rename_i inside
          cases chosen : place (current state position payload metadata) state.held with
          | error reason => simp [chosen] at accepted
          | ok placed =>
            simp only [chosen] at accepted
            generalize novelEq : (if placed.duplicate then 0 else payload.length) = novel at accepted
            split at accepted
            · cases accepted
            · rename_i fits
              split at accepted
              · rename_i resultValid
                cases accepted
                exact ⟨placed, rfl, by simp only [novelEq], by simpa using valid, nonempty, by omega,
                  by omega, by omega, resultValid⟩
              · cases accepted

theorem accept_valid (state : State Meta) (position : Nat) (payload : List UInt8) (metadata : Meta)
    (edge budget : Nat) (result : Result Meta)
    (accepted : accept state position payload metadata edge budget = .ok result) :
    result.state.Valid edge (budget - size result.released) := by
  obtain ⟨_, _, _, _, _, _, _, _, valid⟩ := accept_stages state position payload metadata edge budget result accepted
  exact valid

theorem accept_identity (state : State Meta) (position : Nat) (payload : List UInt8) (metadata : Meta)
    (edge budget : Nat) (result : Result Meta)
    (accepted : accept state position payload metadata edge budget = .ok result) :
    result.receiptID = state.nextID ∧ result.state.nextID = state.nextID + 1 := by
  obtain ⟨_, _, shape, _⟩ := accept_stages state position payload metadata edge budget result accepted
  rw [shape]
  exact ⟨rfl, rfl⟩

theorem accept_frontier (state : State Meta) (position : Nat) (payload : List UInt8) (metadata : Meta)
    (edge budget : Nat) (result : Result Meta)
    (accepted : accept state position payload metadata edge budget = .ok result) :
    result.state.frontier = state.frontier + size result.released := by
  obtain ⟨placed, _, shape, _⟩ := accept_stages state position payload metadata edge budget result accepted
  rw [shape]
  exact drain_frontier state.frontier placed.runs

theorem accept_contiguous (state : State Meta) (position : Nat) (payload : List UInt8) (metadata : Meta)
    (edge budget : Nat) (result : Result Meta)
    (accepted : accept state position payload metadata edge budget = .ok result) :
    Contiguous state.frontier result.released := by
  obtain ⟨placed, _, shape, _⟩ := accept_stages state position payload metadata edge budget result accepted
  rw [shape]
  exact drain_contiguous state.frontier placed.runs

theorem accept_source (state : State Meta) (position : Nat) (payload : List UInt8) (metadata : Meta)
    (edge budget : Nat) (result : Result Meta)
    (accepted : accept state position payload metadata edge budget = .ok result)
    (run : Run Meta) (member : run ∈ result.released ∨ run ∈ result.state.held) :
    run ∈ state.held ∨ run = current state position payload metadata := by
  obtain ⟨placed, placedEq, shape, _⟩ := accept_stages state position payload metadata edge budget result accepted
  rw [shape] at member
  have belongs : run ∈ placed.runs := by
    rw [← drain_partition state.frontier placed.runs]
    exact List.mem_append.mpr member
  exact place_members _ _ _ placedEq run belongs

theorem accept_conservation (state : State Meta) (position : Nat) (payload : List UInt8) (metadata : Meta)
    (edge budget : Nat) (result : Result Meta)
    (accepted : accept state position payload metadata edge budget = .ok result) :
    state.heldBytes + result.novel = size result.released + result.state.heldBytes := by
  obtain ⟨placed, placedEq, shape, _⟩ := accept_stages state position payload metadata edge budget result accepted
  rw [shape]
  have partition := congrArg size (drain_partition state.frontier placed.runs)
  rw [size_append, place_size _ _ _ placedEq] at partition
  exact partition.symm

theorem accept_pairwise (state : State Meta) (position : Nat) (payload : List UInt8) (metadata : Meta)
    (edge budget : Nat) (result : Result Meta)
    (accepted : accept state position payload metadata edge budget = .ok result) :
    result.released.Pairwise Run.Before ∧ result.state.held.Pairwise Run.Before := by
  obtain ⟨placed, placedEq, shape, valid, _⟩ := accept_stages state position payload metadata edge budget result accepted
  rw [shape]
  exact drain_pairwise state.frontier placed.runs (place_pairwise _ _ _ valid.2.2.1 placedEq)

theorem accept_nonempty (state : State Meta) (position : Nat) (payload : List UInt8) (metadata : Meta)
    (edge budget : Nat) (result : Result Meta)
    (accepted : accept state position payload metadata edge budget = .ok result)
    (run : Run Meta) (member : run ∈ result.released ∨ run ∈ result.state.held) : run.bytes ≠ [] := by
  obtain ⟨_, _, _, valid, nonempty, _⟩ := accept_stages state position payload metadata edge budget result accepted
  rcases accept_source state position payload metadata edge budget result accepted run member with old | rfl
  · exact (valid.2.2.2.1 run old).1
  · exact nonempty

theorem accept_ref (state : State Meta) (position : Nat) (payload : List UInt8) (metadata : Meta)
    (edge budget : Nat) (result : Result Meta)
    (accepted : accept state position payload metadata edge budget = .ok result)
    (run : Run Meta) (member : run ∈ result.released ∨ run ∈ result.state.held) :
    run.receipt < state.nextID ∨ run = current state position payload metadata := by
  obtain ⟨_, _, _, valid, _⟩ := accept_stages state position payload metadata edge budget result accepted
  rcases accept_source state position payload metadata edge budget result accepted run member with old | fresh
  · exact .inl (valid.2.2.2.1 run old).2.2.2
  · exact .inr fresh

theorem accept_current_source (state : State Meta) (position : Nat) (payload : List UInt8) (metadata : Meta)
    (edge budget : Nat) (result : Result Meta)
    (accepted : accept state position payload metadata edge budget = .ok result)
    (run : Run Meta) (member : run ∈ result.released ∨ run ∈ result.state.held)
    (fresh : run.receipt = result.receiptID) : run = current state position payload metadata := by
  have allocated := (accept_identity state position payload metadata edge budget result accepted).1
  rcases accept_ref state position payload metadata edge budget result accepted run member with old | freshRun
  · rw [fresh, allocated] at old
    exact False.elim (Nat.lt_irrefl _ old)
  · exact freshRun

theorem accept_seenGap (state : State Meta) (position : Nat) (payload : List UInt8) (metadata : Meta)
    (edge budget : Nat) (result : Result Meta)
    (accepted : accept state position payload metadata edge budget = .ok result) :
    result.state.seenGap = (state.seenGap || decide (state.frontier < position)) := by
  obtain ⟨_, _, shape, _⟩ := accept_stages state position payload metadata edge budget result accepted
  rw [shape]

theorem drain_of_normalized (frontier : Nat) (runs : List (Run Meta))
    (normalized : ∀ run ∈ runs, frontier < run.position) : drain frontier runs = ⟨frontier, [], runs⟩ := by
  cases runs with
  | nil => rfl
  | cons head tail =>
    have after := normalized head (by simp)
    simp only [drain, Nat.ne_of_gt after, ite_false]

theorem accept_duplicate (state : State Meta) (position : Nat) (payload : List UInt8) (metadata : Meta)
    (edge budget : Nat) (result : Result Meta)
    (accepted : accept state position payload metadata edge budget = .ok result) (duplicate : result.duplicate = true) :
    result.released = [] ∧ result.state.frontier = state.frontier ∧
      result.state.held = state.held ∧ result.novel = 0 := by
  obtain ⟨placed, placedEq, shape, valid, _⟩ := accept_stages state position payload metadata edge budget result accepted
  have placedDuplicate : placed.duplicate = true := by simpa only [shape] using duplicate
  have same : placed.runs = state.held := by
    rcases place_shape _ _ _ placedEq with ⟨_, same⟩ | ⟨fresh, _⟩
    · exact same
    · simp_all
  have normalized : ∀ run ∈ state.held, state.frontier < run.position := by
    intro run member
    exact (valid.2.2.2.1 run member).2.1
  rw [shape, same, drain_of_normalized _ _ normalized]
  simp only [placedDuplicate, ite_true, and_self]


theorem place_receipts (incoming : Run Meta) (runs : List (Run Meta)) (placed : Placed Meta)
    (unique : (runs.map (·.receipt)).Nodup) (allocated : ∀ run ∈ runs, run.receipt < incoming.receipt)
    (accepted : place incoming runs = .ok placed) : (placed.runs.map (·.receipt)).Nodup := by
  rcases place_shape incoming runs placed accepted with ⟨_, same⟩ | ⟨_, permutation⟩
  · rw [same]
    exact unique
  · have target : ((runs ++ [incoming]).map (·.receipt)).Nodup := by
      rw [List.map_append]
      apply List.nodup_append.mpr
      refine ⟨unique, by simp, ?_⟩
      intro first firstMember second secondMember same
      obtain ⟨run, member, value⟩ := List.mem_map.mp firstMember
      have bound := allocated run member
      have equal : second = incoming.receipt := by simpa using secondMember
      rw [value, same, equal] at bound
      exact Nat.lt_irrefl _ bound
    exact (permutation.map (·.receipt)).nodup_iff.mpr target

theorem after_valid (state : State Meta) (position : Nat) (payload : List UInt8) (metadata : Meta)
    (edge budget : Nat) (placed : Placed Meta) (valid : state.Valid edge budget) (nonempty : payload ≠ [])
    (forward : state.frontier ≤ position) (inside : position + payload.length ≤ edge)
    (accepted : place (current state position payload metadata) state.held = .ok placed)
    (fits : state.heldBytes + (if placed.duplicate then 0 else payload.length) ≤ budget) :
    (⟨(drain state.frontier placed.runs).frontier, state.nextID + 1, (drain state.frontier placed.runs).held,
      state.seenGap || decide (state.frontier < position)⟩ : State Meta).Valid
      edge (budget - size (drain state.frontier placed.runs).released) := by
  have ordered := place_pairwise _ _ _ valid.2.2.1 accepted
  have bounds : ∀ run ∈ placed.runs, run.bytes ≠ [] ∧ state.frontier ≤ run.position ∧
      run.limit ≤ edge ∧ run.receipt < state.nextID + 1 := by
    intro run member
    rcases place_members _ _ _ accepted run member with old | rfl
    · obtain ⟨positive, later, bound, allocated⟩ := valid.2.2.2.1 run old
      exact ⟨positive, Nat.le_of_lt later, bound, by omega⟩
    · exact ⟨nonempty, forward, inside, by simp [current]⟩
  have endBound := drain_bound state.frontier edge placed.runs valid.1
    (by intro run member; exact (bounds run member).2.2.1)
  have normalized := drain_normalized state.frontier placed.runs ordered
    (by intro run member; exact (bounds run member).2.1)
  have unique := place_receipts _ _ _ valid.2.2.2.2.1
    (by intro run member; exact (valid.2.2.2.1 run member).2.2.2) accepted
  have partition := drain_partition state.frontier placed.runs
  have sizeEq := congrArg size partition
  rw [size_append, place_size _ _ _ accepted] at sizeEq
  change size (drain state.frontier placed.runs).released + size (drain state.frontier placed.runs).held =
    state.heldBytes + (if placed.duplicate then 0 else payload.length) at sizeEq
  have frontier := drain_frontier state.frontier placed.runs
  refine ⟨endBound, ?_, (drain_pairwise state.frontier placed.runs ordered).2, ?_, ?_, ?_⟩
  · have room := valid.2.1
    change edge - (drain state.frontier placed.runs).frontier ≤ _
    omega
  · intro run member
    have old := drain_members state.frontier placed.runs run (.inr member)
    obtain ⟨positive, _, bound, allocated⟩ := bounds run old
    exact ⟨positive, normalized run member, bound, allocated⟩
  · rw [← partition, List.map_append] at unique
    exact (List.nodup_append.mp unique).2.1
  · change size (drain state.frontier placed.runs).held ≤ _
    omega


def Compatible (incoming : Run Meta) (runs : List (Run Meta)) : Prop :=
  ∀ run ∈ runs, incoming.Before run ∨ run.Before incoming ∨
    (incoming.position = run.position ∧ incoming.bytes = run.bytes)

theorem place_exists (incoming : Run Meta) (runs : List (Run Meta)) (compatible : Compatible incoming runs) :
    ∃ placed, place incoming runs = .ok placed := by
  induction runs with
  | nil => exact ⟨⟨[incoming], false⟩, rfl⟩
  | cons head tail ih =>
    have selected := compatible head (by simp)
    by_cases before : incoming.limit ≤ head.position
    · exact ⟨⟨incoming :: head :: tail, false⟩, by simp only [place, before, ite_true]⟩
    · by_cases after : head.limit ≤ incoming.position
      · obtain ⟨rest, chosen⟩ := ih (by intro run member; exact compatible run (by simp [member]))
        exact ⟨⟨head :: rest.runs, rest.duplicate⟩,
          by simp only [place, before, after, ite_true, ite_false, chosen, bind, Except.bind, pure, Except.pure]⟩
      · have same : incoming.position = head.position ∧ incoming.bytes = head.bytes := by
          rcases selected with first | second | same
          · exact False.elim (before first)
          · exact False.elim (after second)
          · exact same
        exact ⟨⟨head :: tail, true⟩, by
          simp only [place, before, ite_false]
          rw [ite_eq_right after, ite_eq_left same]⟩

theorem place_fits (state : State Meta) (position : Nat) (payload : List UInt8) (metadata : Meta)
    (edge budget : Nat) (placed : Placed Meta) (valid : state.Valid edge budget)
    (forward : state.frontier ≤ position) (inside : position + payload.length ≤ edge)
    (accepted : place (current state position payload metadata) state.held = .ok placed) :
    state.heldBytes + (if placed.duplicate then 0 else payload.length) ≤ budget := by
  have order := place_pairwise _ _ _ valid.2.2.1 accepted
  have forwardAll : ∀ run ∈ placed.runs, state.frontier ≤ run.position := by
    intro run member
    rcases place_members _ _ _ accepted run member with old | rfl
    · exact Nat.le_of_lt (valid.2.2.2.1 run old).2.1
    · exact forward
  have insideAll : ∀ run ∈ placed.runs, run.limit ≤ edge := by
    intro run member
    rcases place_members _ _ _ accepted run member with old | rfl
    · exact (valid.2.2.2.1 run old).2.2.1
    · exact inside
  have bound := size_bound state.frontier edge placed.runs order forwardAll insideAll
  rw [place_size _ _ _ accepted] at bound
  exact Nat.le_trans bound valid.2.1

theorem accept_exists (state : State Meta) (position : Nat) (payload : List UInt8) (metadata : Meta)
    (edge budget : Nat) (valid : state.Valid edge budget) (nonempty : payload ≠ [])
    (forward : state.frontier ≤ position) (inside : position + payload.length ≤ edge)
    (compatible : Compatible (current state position payload metadata) state.held) :
    ∃ result, accept state position payload metadata edge budget = .ok result := by
  obtain ⟨placed, chosen⟩ := place_exists _ _ compatible
  have fits := place_fits state position payload metadata edge budget placed valid forward inside chosen
  have after := after_valid state position payload metadata edge budget placed valid nonempty forward inside chosen fits
  refine ⟨⟨⟨(drain state.frontier placed.runs).frontier, state.nextID + 1,
    (drain state.frontier placed.runs).held, state.seenGap || decide (state.frontier < position)⟩,
    state.nextID, (if placed.duplicate then 0 else payload.length),
    (drain state.frontier placed.runs).released, placed.duplicate⟩, ?_⟩
  simp only [accept, valid, not_true_eq_false, ite_false, nonempty, Nat.not_lt.mpr forward,
    Nat.not_lt.mpr inside, chosen, Nat.not_lt.mpr fits, after, ite_true]


theorem accept_receipts (state : State Meta) (position : Nat) (payload : List UInt8) (metadata : Meta)
    (edge budget : Nat) (result : Result Meta)
    (accepted : accept state position payload metadata edge budget = .ok result) :
    ((result.released ++ result.state.held).map (·.receipt)).Nodup := by
  obtain ⟨placed, placedEq, shape, valid, _⟩ := accept_stages state position payload metadata edge budget result accepted
  rw [shape]
  change (((drain state.frontier placed.runs).released ++ (drain state.frontier placed.runs).held).map (·.receipt)).Nodup
  rw [drain_partition]
  exact place_receipts _ _ _ valid.2.2.2.2.1
    (by intro run member; exact (valid.2.2.2.1 run member).2.2.2) placedEq

theorem accept_positions (state : State Meta) (position : Nat) (payload : List UInt8) (metadata : Meta)
    (edge budget : Nat) (result : Result Meta)
    (accepted : accept state position payload metadata edge budget = .ok result) :
    (result.released.map (·.position)).Nodup := by
  have order := (accept_pairwise state position payload metadata edge budget result accepted).1
  apply List.nodup_iff_pairwise_ne.mpr
  apply List.pairwise_map.mpr
  apply List.Pairwise.imp_of_mem (p := order)
  intro first second firstMember _ before same
  have positive := List.length_pos_iff.mpr
    (accept_nonempty state position payload metadata edge budget result accepted first (.inl firstMember))
  unfold Run.Before Run.limit at before
  omega

theorem accept_fresh_member (state : State Meta) (position : Nat) (payload : List UInt8) (metadata : Meta)
    (edge budget : Nat) (result : Result Meta)
    (accepted : accept state position payload metadata edge budget = .ok result)
    (fresh : result.duplicate = false) :
    current state position payload metadata ∈ result.released ++ result.state.held := by
  obtain ⟨placed, placedEq, shape, _⟩ := accept_stages state position payload metadata edge budget result accepted
  have allocated : placed.duplicate = false := by simpa only [shape] using fresh
  rw [shape]
  change current state position payload metadata ∈
    (drain state.frontier placed.runs).released ++ (drain state.frontier placed.runs).held
  rw [drain_partition]
  rcases place_shape _ _ _ placedEq with ⟨duplicate, _⟩ | ⟨_, permutation⟩
  · simp_all
  · exact permutation.mem_iff.mpr (by simp)

end Netlib.Protocol.TCP.ReceiveStore
