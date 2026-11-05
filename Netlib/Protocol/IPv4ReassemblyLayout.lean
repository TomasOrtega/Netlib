import Netlib.Protocol.IPv4ReassemblyFacts

namespace Netlib.Protocol.IPv4Reassembly

theorem Coverage.append (first : Coverage start pieces)
    (second : Coverage (start + (pieces.flatMap (·.data)).length) rest) : Coverage start (pieces ++ rest) := by
  induction first with
  | nil => exact second
  | cons piece tail covered ih =>
    apply Coverage.cons
    apply ih
    simpa only [List.flatMap_cons, List.length_append, Piece.stop, Nat.add_assoc] using second

def Run.Layout (run : Run) : Prop := Coverage run.start run.pieces

@[simp] theorem Run.single_layout (piece : Piece) : (⟨piece, []⟩ : Run).Layout :=
  Coverage.cons piece [] (Coverage.nil _)

@[simp] theorem Run.single_start (piece : Piece) : (⟨piece, []⟩ : Run).start = piece.start := rfl

@[simp] theorem Run.single_stop (piece : Piece) : (⟨piece, []⟩ : Run).stop = piece.stop := by
  simp [Run.stop, Run.start, Run.pieces, Piece.stop]

@[simp] theorem Run.start_le_stop (run : Run) : run.start ≤ run.stop := by
  unfold Run.stop
  omega

@[simp] theorem Run.append_start (run : Run) (piece : Piece) : (run.append piece).start = run.start := rfl

theorem Run.append_layout (run : Run) (piece : Piece) (layout : run.Layout)
    (adjacent : piece.start = run.stop) : (run.append piece).Layout := by
  unfold Run.Layout
  rw [Run.append_start, Run.append_pieces]
  apply layout.append
  change Coverage run.stop [piece]
  rw [← adjacent]
  exact Coverage.cons piece [] (Coverage.nil _)

theorem Run.append_stop (run : Run) (piece : Piece) (adjacent : piece.start = run.stop) :
    (run.append piece).stop = piece.stop := by
  unfold Run.stop
  rw [Run.append_start, Run.append_pieces]
  simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.length_append]
  unfold Piece.stop
  change piece.start = run.start + (run.pieces.flatMap (·.data)).length at adjacent
  omega

theorem insert_run_source (piece : Piece) (runs : List Run) (value : Run)
    (member : value ∈ insert piece runs) :
    value = ⟨piece, []⟩ ∨ ∃ old ∈ runs, value = old ∨ value = old.append piece ∧ piece.start = old.stop := by
  induction runs with
  | nil => simp only [insert, List.mem_singleton] at member; exact Or.inl member
  | cons run rest ih =>
    rw [insert.eq_def] at member
    by_cases before : piece.start < run.start
    · simp only [before, ↓reduceIte, List.mem_cons] at member
      rcases member with rfl | previous
      · exact Or.inl rfl
      · exact Or.inr ⟨value, List.mem_cons.mpr previous, Or.inl rfl⟩
    · simp only [before, ↓reduceIte] at member
      cases rest with
      | nil =>
        by_cases adjacent : piece.start = run.stop
        · simp only [adjacent, ↓reduceIte, List.mem_singleton] at member
          exact Or.inr ⟨run, by simp, Or.inr ⟨member, adjacent⟩⟩
        · simp only [adjacent, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with head | current
          · exact Or.inr ⟨run, by simp, Or.inl head⟩
          · exact Or.inl current
      | cons next tail =>
        simp only [List.mem_cons] at member
        rcases member with head | inserted
        · exact Or.inr ⟨run, by simp, Or.inl head⟩
        · rcases ih inserted with current | previous
          · exact Or.inl current
          · obtain ⟨old, belongs, same⟩ := previous
            exact Or.inr ⟨old, List.mem_cons_of_mem _ belongs, same⟩

theorem insert_layout (piece : Piece) (runs : List Run) (layouts : ∀ run ∈ runs, run.Layout) :
    ∀ run ∈ insert piece runs, run.Layout := by
  intro value member
  rcases insert_run_source _ _ _ member with current | previous
  · rw [current]
    exact Run.single_layout piece
  · obtain ⟨old, belongs, same⟩ := previous
    rcases same with same | ⟨same, adjacent⟩
    · rw [same]
      exact layouts old belongs
    · rw [same]
      exact old.append_layout piece (layouts old belongs) adjacent

theorem insert_extent (piece : Piece) (runs : List Run) (limit : Nat)
    (bounds : ∀ run ∈ runs, run.stop ≤ limit) (bounded : piece.stop ≤ limit) :
    ∀ run ∈ insert piece runs, run.stop ≤ limit := by
  intro value member
  rcases insert_run_source _ _ _ member with current | previous
  · simpa only [current, Run.single_stop] using bounded
  · obtain ⟨old, belongs, same⟩ := previous
    rcases same with same | ⟨same, adjacent⟩
    · rw [same]
      exact bounds old belongs
    · rw [same, Run.append_stop _ _ adjacent]
      exact bounded

theorem insert_ordered (piece : Piece) (runs : List Run)
    (ordered : runs.Pairwise (fun first second => first.stop ≤ second.start))
    (positive : 0 < piece.data.length)
    (disjoint : ∀ run ∈ runs, ¬(piece.start < run.stop ∧ run.start < piece.stop)) :
    (insert piece runs).Pairwise (fun first second => first.stop ≤ second.start) := by
  induction runs with
  | nil => simp [insert]
  | cons run rest ih =>
    obtain ⟨beforeRest, restOrdered⟩ := List.pairwise_cons.mp ordered
    have separated := disjoint run (by simp)
    have range := run.start_le_stop
    rw [insert.eq_def]
    by_cases before : piece.start < run.start
    · simp only [before, ↓reduceIte]
      apply List.pairwise_cons.mpr
      constructor
      · intro next member
        simp only [Run.single_stop]
        have bound : piece.stop ≤ run.start := by omega
        rcases List.mem_cons.mp member with rfl | later
        · exact bound
        · have nextBound := beforeRest next later
          change piece.stop ≤ next.start
          omega
      · exact List.pairwise_cons.mpr ⟨beforeRest, restOrdered⟩
    · simp only [before, ↓reduceIte]
      have after : run.stop ≤ piece.start := by unfold Piece.stop at separated; omega
      cases rest with
      | nil =>
        by_cases adjacent : piece.start = run.stop
        · simp [adjacent]
        · simp [adjacent, Run.start, after]
      | cons next tail =>
        apply List.pairwise_cons.mpr
        constructor
        · intro value member
          rcases insert_run_source _ _ _ member with rfl | previous
          · exact after
          · obtain ⟨old, belongs, same⟩ := previous
            rcases same with same | ⟨same, _⟩
            · rw [same]
              exact beforeRest old belongs
            · rw [same, Run.append_start]
              exact beforeRest old belongs
        · exact ih restOrdered (fun value member => disjoint value (List.mem_cons_of_mem _ member))

theorem runs_length_bound (runs : List Run) (start limit : Nat)
    (ordered : runs.Pairwise (fun first second => first.stop ≤ second.start))
    (after : ∀ run ∈ runs, start ≤ run.start) (before : ∀ run ∈ runs, run.stop ≤ limit) :
    ((runs.flatMap Run.pieces).flatMap (·.data)).length ≤ limit - start := by
  induction runs generalizing start with
  | nil => simp
  | cons run rest ih =>
    obtain ⟨headBefore, tailOrdered⟩ := List.pairwise_cons.mp ordered
    have tail := ih run.stop tailOrdered headBefore (fun value member => before value (List.mem_cons_of_mem _ member))
    have headAfter := after run (by simp)
    have headBound := before run (by simp)
    simp only [List.flatMap_cons, List.flatMap_append, List.length_append]
    unfold Run.stop at tail headBound
    omega

theorem runs_exact_cover (runs : List Run) (start limit : Nat)
    (layouts : ∀ run ∈ runs, run.Layout)
    (ordered : runs.Pairwise (fun first second => first.stop ≤ second.start))
    (after : ∀ run ∈ runs, start ≤ run.start) (before : ∀ run ∈ runs, run.stop ≤ limit)
    (complete : ((runs.flatMap Run.pieces).flatMap (·.data)).length = limit - start) :
    Coverage start (runs.flatMap Run.pieces) := by
  induction runs generalizing start with
  | nil => exact Coverage.nil _
  | cons run rest ih =>
    obtain ⟨headBefore, tailOrdered⟩ := List.pairwise_cons.mp ordered
    have tailBefore := fun value member => before value (List.mem_cons_of_mem _ member)
    have tailBound := runs_length_bound rest run.stop limit tailOrdered headBefore tailBefore
    have headAfter := after run (by simp)
    have headBound := before run (by simp)
    simp only [List.flatMap_cons, List.flatMap_append, List.length_append] at complete
    have same : start = run.start := by unfold Run.stop at tailBound headBound; omega
    have tailComplete : ((rest.flatMap Run.pieces).flatMap (·.data)).length = limit - run.stop := by
      unfold Run.stop at *
      omega
    have covered := ih run.stop (fun value member => layouts value (List.mem_cons_of_mem _ member))
      tailOrdered headBefore tailBefore tailComplete
    rw [same]
    exact (layouts run (by simp)).append covered

structure Queue.LayoutValid (queue : Queue) : Prop where
  runs : ∀ run ∈ queue.runs, run.Layout
  ordered : queue.runs.Pairwise (fun first second => first.stop ≤ second.start)
  extent : ∀ run ∈ queue.runs, run.stop ≤ queue.length

structure State.LayoutValid (state : State) : Prop where
  unique : (state.queues.map Queue.key).Nodup
  queues : ∀ queue ∈ state.queues, queue.LayoutValid

theorem Queue.fresh_layout (wanted : Key) (expires : Nat) :
    (⟨wanted, expires, [], 0, false, none, 0, 0, 0⟩ : Queue).LayoutValid := by constructor <;> simp

theorem State.initial_layout : State.initial.LayoutValid := by constructor <;> simp [State.initial]

theorem State.age_layout (state : State) (now : Nat) (valid : state.LayoutValid) : (state.age now).LayoutValid := by
  constructor
  · exact List.Nodup.sublist (List.filter_sublist.map Queue.key) valid.unique
  · intro queue member
    exact valid.queues queue ((State.age_member _ _ _).mp member).1

theorem State.erase_layout (state : State) (wanted : Key) (valid : state.LayoutValid) :
    (state.erase wanted).LayoutValid := by
  constructor
  · exact List.Nodup.sublist (List.filter_sublist.map Queue.key) valid.unique
  · intro queue member
    exact valid.queues queue ((State.erase_member _ _ _).mp member).1

theorem State.put_layout (state : State) (queue : Queue) (valid : state.LayoutValid) (inserted : queue.LayoutValid) :
    (state.put queue).LayoutValid := by
  constructor
  · apply List.nodup_cons.mpr
    constructor
    · intro member
      obtain ⟨old, belongs, same⟩ := List.mem_map.mp member
      exact ((State.erase_member _ _ _).mp belongs).2 same
    · exact (state.erase_layout queue.key valid).unique
  · intro value member
    rcases (State.put_member _ _ _).mp member with rfl | previous
    · exact inserted
    · exact valid.queues value previous.1

theorem queuedLength_bounds (queue next : Queue) (piece : Piece)
    (updated : queuedLength queue piece = some next) : queue.length ≤ next.length ∧ piece.stop ≤ next.length := by
  unfold queuedLength at updated
  split at updated
  · split at updated
    · cases updated
    · cases updated
      exact ⟨Nat.le_max_left _ _, Nat.le_max_right _ _⟩
  · split at updated
    · cases updated
    · rename_i consistent
      cases updated
      change queue.length ≤ piece.stop ∧ piece.stop ≤ piece.stop
      exact ⟨by omega, Nat.le_refl _⟩

theorem queuedLength_layout (queue next : Queue) (piece : Piece)
    (updated : queuedLength queue piece = some next) (valid : queue.LayoutValid) : next.LayoutValid := by
  have same := (queuedLength_fields _ _ _ updated).2.2.1
  have bounds := queuedLength_bounds _ _ _ updated
  constructor
  · rw [same]
    exact valid.runs
  · rw [same]
    exact valid.ordered
  · intro run member
    rw [same] at member
    exact Nat.le_trans (valid.extent run member) bounds.1

theorem store_layout (queue : Queue) (piece : Piece) (valid : queue.LayoutValid)
    (positive : 0 < piece.data.length) (bounded : piece.stop ≤ queue.length)
    (disjoint : ∀ run ∈ queue.runs, ¬(piece.start < run.stop ∧ run.start < piece.stop)) :
    (store queue piece).LayoutValid :=
  ⟨insert_layout _ _ valid.runs, insert_ordered _ _ valid.ordered positive disjoint,
    insert_extent _ _ _ valid.extent bounded⟩

theorem Queue.complete_coverage (queue : Queue) (valid : queue.LayoutValid) (full : queue.meat = queue.length) :
    Coverage 0 queue.pieces := by
  apply runs_exact_cover queue.runs 0 queue.length valid.runs valid.ordered
    (fun _ _ => Nat.zero_le _) valid.extent
  exact full

theorem Queue.no_invalidLayout (queue : Queue) (valid : queue.LayoutValid) :
    queue.complete ≠ .rejected .invalidLayout := by
  intro rejected
  unfold Queue.complete at rejected
  split at rejected
  · cases rejected
  · split at rejected
    · rename_i ready
      have readyParts : queue.last = true ∧ queue.meat = queue.length := by
        simpa only [Bool.and_eq_true, decide_eq_true_eq] using ready
      have joined := (queue.complete_coverage valid readyParts.2).joinAt
      split at rejected
      · cases rejected
      · split at rejected
        · cases rejected
        · rw [joined] at rejected
          cases rejected
    · cases rejected

theorem Queue.complete_ready (queue : Queue) (valid : queue.LayoutValid) (header : IPv4.Packet)
    (first : queue.first = some header) (last : queue.last = true) (full : queue.meat = queue.length)
    (ecn : ¬(queue.ecn % 2 = 1 ∧ 1 < queue.ecn)) (bounded : queue.length + 20 ≤ 65535) :
    ∃ output, queue.complete = .accepted output := by
  have joined := (queue.complete_coverage valid full).joinAt
  simp [Queue.complete, first, last, full, ecn, Nat.not_lt.mpr bounded, joined]

theorem accept_layout (state : State) (queue : Queue) (piece : Piece)
    (stateValid : state.LayoutValid) (queueValid : queue.LayoutValid) (bounded : piece.stop ≤ queue.length) :
    (accept state queue piece).state.LayoutValid := by
  unfold accept
  split
  · exact state.erase_layout _ stateValid
  · rename_i nonempty
    split
    · exact state.put_layout _ stateValid queueValid
    · split
      · exact state.erase_layout _ stateValid
      · rename_i noOverlap
        have positive : 0 < piece.data.length := by
          cases data : piece.data with
          | nil => simp [data] at nonempty
          | cons head tail => simp
        have disjoint : ∀ run ∈ queue.runs, ¬(piece.start < run.stop ∧ run.start < piece.stop) := by
          intro run member overlap
          apply noOverlap
          exact List.any_eq_true.mpr ⟨run, member, by simpa only [Run.overlaps, decide_eq_true_eq] using overlap⟩
        have stored := store_layout queue piece queueValid positive bounded disjoint
        dsimp only
        cases done : (store queue piece).complete with
        | waiting => exact state.put_layout _ stateValid stored
        | rejected reason => exact state.erase_layout _ stateValid
        | accepted output => exact state.erase_layout _ stateValid

theorem process_layout (policy : Policy) (before : State) (now : Nat) (domain : Domain)
    (fragment : IPv4Fragment.Decoded) (valid : before.LayoutValid) :
    (process policy before now domain fragment).state.LayoutValid := by
  let state : State := { before.age now with lastTime := now }
  let wanted := key domain fragment
  let old := (state.lookup wanted).getD { key := wanted, expires := now + policy.timeout }
  have stateValid : state.LayoutValid := ⟨(before.age_layout now valid).unique, (before.age_layout now valid).queues⟩
  have oldValid : old.LayoutValid := by
    cases found : state.lookup wanted with
    | none => simpa only [old, found, Option.getD_none] using Queue.fresh_layout wanted (now + policy.timeout)
    | some queue => simpa only [old, found, Option.getD_some] using stateValid.queues queue (state.lookup_member _ _ found)
  unfold process
  split
  · exact stateValid
  · dsimp only
    split
    · exact state.erase_layout _ stateValid
    · rename_i queue lengthUpdated
      exact accept_layout _ _ _ stateValid (queuedLength_layout _ _ _ lengthUpdated oldValid)
        (queuedLength_bounds _ _ _ lengthUpdated).2

theorem arrive_layout (policy : Policy) (before : State) (now : Nat) (domain : Domain)
    (fragment : IPv4Fragment.Decoded) (result : Result)
    (accepted : arrive policy before now domain fragment = .ok result) (valid : before.LayoutValid) : result.state.LayoutValid := by
  obtain ⟨processed, _, _, _⟩ := arrive_processed _ _ _ _ _ _ accepted
  rw [processed]
  exact process_layout _ _ _ _ _ valid

theorem accept_no_invalidLayout (state : State) (queue : Queue) (piece : Piece)
    (queueValid : queue.LayoutValid) (bounded : piece.stop ≤ queue.length) :
    (accept state queue piece).disposition ≠ .invalidLayout := by
  unfold accept
  split
  · intro impossible; cases impossible
  · rename_i nonempty
    split
    · intro impossible; cases impossible
    · split
      · intro impossible; cases impossible
      · rename_i noOverlap
        have positive : 0 < piece.data.length := by
          cases data : piece.data with
          | nil => simp [data] at nonempty
          | cons head tail => simp
        have disjoint : ∀ run ∈ queue.runs, ¬(piece.start < run.stop ∧ run.start < piece.stop) := by
          intro run member overlap
          apply noOverlap
          exact List.any_eq_true.mpr ⟨run, member, by simpa only [Run.overlaps, decide_eq_true_eq] using overlap⟩
        have stored := store_layout queue piece queueValid positive bounded disjoint
        dsimp only
        cases done : (store queue piece).complete with
        | waiting => intro impossible; cases impossible
        | rejected reason =>
          intro same
          cases same
          exact (store queue piece).no_invalidLayout stored done
        | accepted output => intro impossible; cases impossible

theorem process_no_invalidLayout (policy : Policy) (before : State) (now : Nat) (domain : Domain)
    (fragment : IPv4Fragment.Decoded) (valid : before.LayoutValid) :
    (process policy before now domain fragment).disposition ≠ .invalidLayout := by
  let state : State := { before.age now with lastTime := now }
  let wanted := key domain fragment
  let old := (state.lookup wanted).getD { key := wanted, expires := now + policy.timeout }
  have stateValid : state.LayoutValid := ⟨(before.age_layout now valid).unique, (before.age_layout now valid).queues⟩
  have oldValid : old.LayoutValid := by
    cases found : state.lookup wanted with
    | none => simpa only [old, found, Option.getD_none] using Queue.fresh_layout wanted (now + policy.timeout)
    | some queue => simpa only [old, found, Option.getD_some] using stateValid.queues queue (state.lookup_member _ _ found)
  unfold process
  split
  · intro impossible; cases impossible
  · dsimp only
    split
    · intro impossible; cases impossible
    · rename_i queue lengthUpdated
      exact accept_no_invalidLayout _ _ _ (queuedLength_layout _ _ _ lengthUpdated oldValid)
        (queuedLength_bounds _ _ _ lengthUpdated).2

theorem arrive_no_invalidLayout (policy : Policy) (before : State) (now : Nat) (domain : Domain)
    (fragment : IPv4Fragment.Decoded) (result : Result)
    (accepted : arrive policy before now domain fragment = .ok result) (valid : before.LayoutValid) :
    result.disposition ≠ .invalidLayout := by
  obtain ⟨processed, _, _, _⟩ := arrive_processed _ _ _ _ _ _ accepted
  rw [processed]
  exact process_no_invalidLayout _ _ _ _ _ valid

theorem execute_layout (policy : Policy) (before final : State) (events : List Arrival) (results : List Result)
    (accepted : execute policy before events = .ok (final, results)) (valid : before.LayoutValid) :
    final.LayoutValid ∧ ∀ result ∈ results, result.state.LayoutValid ∧ result.disposition ≠ .invalidLayout := by
  induction events generalizing before final results with
  | nil =>
    simp only [execute, Except.ok.injEq, Prod.mk.injEq] at accepted
    obtain ⟨rfl, rfl⟩ := accepted
    exact ⟨valid, by simp⟩
  | cons event rest ih =>
    cases computed : arrive policy before event.now event.domain event.fragment with
    | error error => simp [execute, computed, bind, Except.bind] at accepted
    | ok result =>
      have current := arrive_layout _ _ _ _ _ _ computed valid
      have possible := arrive_no_invalidLayout _ _ _ _ _ _ computed valid
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
          · exact ⟨current, possible⟩
          · exact tailValid value later⟩

theorem accept_completes_ready (state : State) (queue : Queue) (piece : Piece)
    (layout : queue.LayoutValid) (positive : 0 < piece.data.length) (bounded : piece.stop ≤ queue.length)
    (notDuplicate : queue.runs.any (·.contains piece) = false)
    (notOverlap : queue.runs.any (·.overlaps piece) = false)
    (header : IPv4.Packet) (first : (store queue piece).first = some header)
    (last : (store queue piece).last = true) (full : (store queue piece).meat = (store queue piece).length)
    (ecn : ¬((store queue piece).ecn % 2 = 1 ∧ 1 < (store queue piece).ecn))
    (length : (store queue piece).length + 20 ≤ 65535) :
    ∃ output, accept state queue piece = ⟨state.erase queue.key, .complete, some output⟩ := by
  have disjoint : ∀ run ∈ queue.runs, ¬(piece.start < run.stop ∧ run.start < piece.stop) := by
    intro run member overlap
    have found : queue.runs.any (·.overlaps piece) = true :=
      List.any_eq_true.mpr ⟨run, member, by simpa only [Run.overlaps, decide_eq_true_eq] using overlap⟩
    rw [notOverlap] at found
    cases found
  have stored := store_layout _ _ layout positive bounded disjoint
  obtain ⟨output, completed⟩ := (store queue piece).complete_ready stored header first last full ecn length
  have nonempty : piece.data.isEmpty = false := by
    cases data : piece.data with
    | nil => simp [data] at positive
    | cons head tail => rfl
  exact ⟨output, by simp [accept, nonempty, notDuplicate, notOverlap, completed]⟩

end Netlib.Protocol.IPv4Reassembly
