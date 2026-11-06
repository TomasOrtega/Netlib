import Netlib.Check.CampusTCPTwoProgressGateway

/-!
# Exact range insertion after old TCP coverage

Old runs and their source identifiers remain in the ledger.
New lower and upper runs can arrive in either order.
-/

namespace Netlib.Check.CampusTCPTwoProgressCoverage

open Protocol.TCP
open Theory.SparseCoverage

variable {Meta : Type}

theorem place_after (incoming : Run Meta) (prior rest : List (Run Meta)) (placed : Placement Meta)
    (nonempty : incoming.bytes ≠ []) (before : ∀ run ∈ prior, run.limit ≤ incoming.position)
    (accepted : place incoming rest = .ok placed) :
    place incoming (prior ++ rest) = .ok { placed with runs := prior ++ placed.runs } := by
  induction prior with
  | nil => simpa only [List.nil_append] using accepted
  | cons head tail ih =>
    have first := before head List.mem_cons_self
    have positive := List.length_pos_iff.mpr nonempty
    have notBefore : ¬incoming.limit ≤ head.position := by
      unfold Run.limit at *
      omega
    have later := ih (fun run member => before run (List.mem_cons_of_mem _ member))
    simp only [List.cons_append, place, notBefore, ite_false, first, ite_true, later,
      bind, Except.bind, pure, Except.pure]

def appendResult (state : State Meta) (position : Nat) (payload : List UInt8) (metadata : Meta) : Result Meta :=
  ⟨⟨state.runs ++ [current state position payload metadata], state.nextID + 1⟩,
    current state position payload metadata, 0, payload.length⟩

theorem accept_append (state : State Meta) (position : Nat) (payload : List UInt8) (metadata : Meta) (bound : Nat)
    (valid : state.Valid bound) (nonempty : payload ≠ []) (inside : position + payload.length ≤ bound)
    (before : state.highEnd ≤ position) :
    accept state position payload metadata bound = .ok (appendResult state position payload metadata) := by
  have placed := place_after (current state position payload metadata) state.runs []
    ⟨[current state position payload metadata], current state position payload metadata, 0, false⟩
    nonempty (fun run member => Nat.le_trans (state.limit_le_highEnd run member) before) rfl
  have actual : place (current state position payload metadata) state.runs = .ok
      ⟨state.runs ++ [current state position payload metadata], current state position payload metadata, 0, false⟩ := by
    simpa only [List.append_nil] using placed
  simp only [accept, valid, not_true_eq_false, ite_false, nonempty, Nat.not_lt.mpr inside, actual]
  rfl

def insertResult (state : State Meta) (prior rest : List (Run Meta))
    (position : Nat) (payload : List UInt8) (metadata : Meta) : Result Meta :=
  ⟨⟨prior ++ current state position payload metadata :: rest, state.nextID + 1⟩,
    current state position payload metadata, 0, payload.length⟩

theorem accept_before_run (state : State Meta) (prior : List (Run Meta)) (head : Run Meta) (rest : List (Run Meta))
    (position : Nat) (payload : List UInt8) (metadata : Meta) (bound : Nat)
    (valid : state.Valid bound) (nonempty : payload ≠ []) (inside : position + payload.length ≤ bound)
    (runs : state.runs = prior ++ head :: rest)
    (before : ∀ run ∈ prior, run.limit ≤ position) (after : position + payload.length ≤ head.position) :
    accept state position payload metadata bound = .ok (insertResult state prior (head :: rest) position payload metadata) := by
  have placed := place_after (current state position payload metadata) prior (head :: rest)
    ⟨current state position payload metadata :: head :: rest, current state position payload metadata, 0, false⟩
    nonempty before (by simp only [place, current, Run.limit, after, ite_true])
  simp only [accept, valid, not_true_eq_false, ite_false, nonempty, Nat.not_lt.mpr inside]
  rw [runs, placed]
  rfl

theorem highEnd_append (first second : List (Run Meta)) :
    Theory.SparseCoverage.highEnd (first ++ second) = max (Theory.SparseCoverage.highEnd first) (Theory.SparseCoverage.highEnd second) := by
  induction first with
  | nil => simp only [List.nil_append, Theory.SparseCoverage.highEnd, Nat.zero_max]
  | cons head tail ih =>
    simp only [List.cons_append, Theory.SparseCoverage.highEnd, ih, Nat.max_assoc]

theorem frontierFrom_append (cursor finish : Nat) (prior extra : List (Run Meta))
    (ordered : prior.Pairwise Run.Before) (nonempty : ∀ run ∈ prior, run.bytes ≠ [])
    (forward : ∀ run ∈ prior, cursor ≤ run.position) (bounded : ∀ run ∈ prior, run.limit ≤ finish)
    (complete : frontierFrom cursor prior = finish) :
    frontierFrom cursor (prior ++ extra) = frontierFrom finish extra := by
  induction prior generalizing cursor with
  | nil => simpa only [frontierFrom, List.nil_append] using congrArg (fun value => frontierFrom value extra) complete
  | cons head tail ih =>
    obtain ⟨headBefore, tailOrdered⟩ := List.pairwise_cons.mp ordered
    have same : head.position = cursor := by
      by_cases selected : head.position = cursor
      · exact selected
      · have stopped : finish = cursor := by simpa only [frontierFrom, selected, ite_false] using complete.symm
        have positive := List.length_pos_iff.mpr (nonempty head List.mem_cons_self)
        have lower := forward head List.mem_cons_self
        have upper := bounded head List.mem_cons_self
        unfold Run.limit at upper
        omega
    have remaining : frontierFrom head.limit tail = finish := by
      simpa only [frontierFrom, same, ite_true] using complete
    simp only [List.cons_append, frontierFrom, same, ite_true]
    exact ih head.limit tailOrdered
      (fun run member => nonempty run (List.mem_cons_of_mem _ member)) headBefore
      (fun run member => bounded run (List.mem_cons_of_mem _ member)) remaining

theorem frontier_append_complete (state : State Meta) (bound finish : Nat) (extra : List (Run Meta))
    (valid : state.Valid bound) (complete : state.frontier = finish) (highEnd : state.highEnd = finish) :
    (⟨state.runs ++ extra, state.nextID⟩ : State Meta).frontier = frontierFrom finish extra := by
  exact frontierFrom_append 0 finish state.runs extra valid.1
    (fun run member => (valid.2.1 run member).1) (fun _ _ => Nat.zero_le _)
    (fun run member => by rw [← highEnd]; exact state.limit_le_highEnd run member) complete

structure TwoRanges (before after : State Meta) (finish : Nat) (lower upper : List UInt8) where
  lowerRun : Option (Run Meta)
  upperRun : Option (Run Meta)
  lowerFields : ∀ run ∈ lowerRun.toList, run.position = finish ∧ run.bytes = lower
  upperFields : ∀ run ∈ upperRun.toList, run.position = finish + lower.length ∧ run.bytes = upper
  runs : after.runs = before.runs ++ lowerRun.toList ++ upperRun.toList
  nextID : after.nextID = before.nextID + lowerRun.toList.length + upperRun.toList.length

def TwoRanges.initial (state : State Meta) (finish : Nat) (lower upper : List UInt8) :
    TwoRanges state state finish lower upper :=
  ⟨none, none, by simp, by simp, by simp, by simp⟩

variable {before after : State Meta} {finish : Nat} {lower upper : List UInt8}

theorem TwoRanges.highEnd (ranges : TwoRanges before after finish lower upper)
    (complete : before.highEnd = finish) :
    after.highEnd = if ranges.upperRun.isSome then finish + lower.length + upper.length
      else if ranges.lowerRun.isSome then finish + lower.length else finish := by
  unfold State.highEnd
  rw [ranges.runs, highEnd_append, highEnd_append]
  change max (max before.highEnd _) _ = _
  rw [complete]
  cases first : ranges.lowerRun with
  | none =>
    cases second : ranges.upperRun with
    | none => simp only [Option.toList_none, Theory.SparseCoverage.highEnd, Nat.max_zero, Option.isSome_none, Bool.false_eq_true, ite_false]
    | some run =>
      have fields := ranges.upperFields run (by simp [second])
      simp only [Option.toList_none, Option.toList_some, Theory.SparseCoverage.highEnd,
        Nat.max_zero, Option.isSome_some, ite_true, Run.limit, fields.1, fields.2]
      omega
  | some run =>
    have fields := ranges.lowerFields run (by simp [first])
    cases second : ranges.upperRun with
    | none =>
      simp only [Option.toList_none, Option.toList_some, Theory.SparseCoverage.highEnd,
        Nat.max_zero, Option.isSome_some, Option.isSome_none, Bool.false_eq_true, ite_false, ite_true,
        Run.limit, fields.1, fields.2]
      omega
    | some later =>
      have laterFields := ranges.upperFields later (by simp [second])
      simp only [Option.toList_some, Theory.SparseCoverage.highEnd, Nat.max_zero,
        Option.isSome_some, ite_true, Run.limit, fields.1, fields.2, laterFields.1, laterFields.2]
      omega

theorem TwoRanges.frontier (ranges : TwoRanges before after finish lower upper) (bound : Nat)
    (valid : before.Valid bound) (complete : before.frontier = finish) (highEnd : before.highEnd = finish)
    (lowerNonempty : lower ≠ []) :
    after.frontier = if ranges.lowerRun.isSome then
      finish + lower.length + (if ranges.upperRun.isSome then upper.length else 0) else finish := by
  have appended := frontier_append_complete before bound finish (ranges.lowerRun.toList ++ ranges.upperRun.toList)
    valid complete highEnd
  change frontierFrom 0 after.runs = _
  rw [ranges.runs, List.append_assoc]
  change (⟨before.runs ++ (ranges.lowerRun.toList ++ ranges.upperRun.toList), before.nextID⟩ : State Meta).frontier = _
  rw [appended]
  cases first : ranges.lowerRun with
  | none =>
    cases second : ranges.upperRun with
    | none => rfl
    | some run =>
      have fields := ranges.upperFields run (by simp [second])
      have positive := List.length_pos_iff.mpr lowerNonempty
      have gap : finish + lower.length ≠ finish := by omega
      simp only [Option.toList_none, Option.toList_some, List.nil_append,
        frontierFrom, fields.1, gap, ite_false, Option.isSome_none, Bool.false_eq_true]
  | some run =>
    have fields := ranges.lowerFields run (by simp [first])
    cases second : ranges.upperRun with
    | none =>
      simp only [Option.toList_none, Option.toList_some, List.append_nil,
        frontierFrom, fields.1, ite_true, Run.limit, fields.2, Option.isSome_some,
        Option.isSome_none, Bool.false_eq_true, ite_false, Nat.add_zero]
    | some later =>
      have laterFields := ranges.upperFields later (by simp [second])
      simp only [Option.toList_some, List.cons_append, List.nil_append,
        frontierFrom, fields.1, ite_true, Run.limit, fields.2, laterFields.1, laterFields.2,
        Option.isSome_some]

theorem TwoRanges.add_upper (ranges : TwoRanges before after finish lower upper) (metadata : Meta) (bound : Nat)
    (highEnd : before.highEnd = finish) (valid : after.Valid bound)
    (missing : ranges.upperRun = none) (nonempty : upper ≠ [])
    (inside : finish + lower.length + upper.length ≤ bound) :
    ∃ result, accept after (finish + lower.length) upper metadata bound = .ok result ∧
      ∃ next : TwoRanges before result.state finish lower upper,
        next.lowerRun = ranges.lowerRun ∧ next.upperRun = some result.source ∧
        result.source = current after (finish + lower.length) upper metadata ∧ result.offset = 0 ∧
        result.novel = upper.length := by
  have oldBound : after.highEnd ≤ finish + lower.length := by
    rw [ranges.highEnd highEnd, missing]
    simp only [Option.isSome_none, Bool.false_eq_true, ite_false]
    split <;> omega
  let result := appendResult after (finish + lower.length) upper metadata
  have accepted := accept_append after (finish + lower.length) upper metadata bound valid nonempty inside oldBound
  refine ⟨result, accepted, ?_⟩
  let next : TwoRanges before result.state finish lower upper := {
    lowerRun := ranges.lowerRun
    upperRun := some result.source
    lowerFields := ranges.lowerFields
    upperFields := by intro run member; simp only [Option.toList_some, List.mem_singleton] at member; subst run; exact ⟨rfl, rfl⟩
    runs := by
      change after.runs ++ [result.source] = _
      rw [ranges.runs, missing]
      simp only [Option.toList_none, List.append_nil, Option.toList_some]
    nextID := by
      change after.nextID + 1 = _
      rw [ranges.nextID, missing]
      simp only [Option.toList_none, List.length_nil, Option.toList_some, List.length_singleton, Nat.add_zero]
  }
  exact ⟨next, rfl, rfl, rfl, rfl, rfl⟩

theorem TwoRanges.add_lower (ranges : TwoRanges before after finish lower upper) (metadata : Meta) (bound : Nat)
    (highEnd : before.highEnd = finish) (valid : after.Valid bound)
    (missing : ranges.lowerRun = none) (nonempty : lower ≠ [])
    (inside : finish + lower.length ≤ bound) :
    ∃ result, accept after finish lower metadata bound = .ok result ∧
      ∃ next : TwoRanges before result.state finish lower upper,
        next.lowerRun = some result.source ∧ next.upperRun = ranges.upperRun ∧
        result.source = current after finish lower metadata ∧ result.offset = 0 ∧
        result.novel = lower.length := by
  let source := current after finish lower metadata
  let result : Result Meta := ⟨⟨before.runs ++ source :: ranges.upperRun.toList, after.nextID + 1⟩, source, 0, lower.length⟩
  have accepted : accept after finish lower metadata bound = .ok result := by
    cases selected : ranges.upperRun with
    | none =>
      have oldBound : after.highEnd ≤ finish := by
        rw [ranges.highEnd highEnd, selected, missing]
        exact Nat.le_refl _
      have accepted := accept_append after finish lower metadata bound valid nonempty inside oldBound
      simpa only [appendResult, ranges.runs, missing, selected, Option.toList_none, List.append_nil,
        result, source, List.nil_append] using accepted
    | some run =>
      have fields := ranges.upperFields run (by simp [selected])
      have runs : after.runs = before.runs ++ run :: [] := by
        simpa only [missing, selected, Option.toList_none, Option.toList_some, List.append_nil] using ranges.runs
      have accepted := accept_before_run after before.runs run [] finish lower metadata bound valid nonempty inside runs
        (fun old member => by rw [← highEnd]; exact before.limit_le_highEnd old member) (by omega)
      simpa only [insertResult, result, source, selected, Option.toList_some] using accepted
  refine ⟨result, accepted, ?_⟩
  let next : TwoRanges before result.state finish lower upper := {
    lowerRun := some source
    upperRun := ranges.upperRun
    lowerFields := by intro run member; simp only [Option.toList_some, List.mem_singleton] at member; subst run; exact ⟨rfl, rfl⟩
    upperFields := ranges.upperFields
    runs := by simp only [result, Option.toList_some, List.append_assoc, List.singleton_append]
    nextID := by
      change after.nextID + 1 = _
      rw [ranges.nextID, missing]
      simp only [Option.toList_none, List.length_nil, Option.toList_some, List.length_singleton, Nat.add_zero]
      omega
  }
  exact ⟨next, rfl, rfl, rfl, rfl, rfl⟩

end Netlib.Check.CampusTCPTwoProgressCoverage
