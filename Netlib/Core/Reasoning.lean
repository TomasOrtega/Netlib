import Netlib.Core.Logic

namespace Netlib.Reasoning

variable {Atom : Type u} [DecidableEq Atom]

private def unique : List Atom → List Atom
  | [] => []
  | a :: as => let tail := unique as; if a ∈ tail then tail else a :: tail

@[simp] private theorem mem_unique (a : Atom) (as : List Atom) :
    a ∈ unique as ↔ a ∈ as := by
  induction as generalizing a with
  | nil => simp [unique]
  | cons b bs ih =>
    simp only [unique]
    split <;> simp_all

/-- Every atom is assigned independently; no network assumptions are implicit. -/
def valuations : List Atom → List (Atom → Bool)
  | [] => [fun _ => false]
  | a :: as => (valuations as).flatMap fun v =>
      [fun x => if x = a then false else v x,
       fun x => if x = a then true else v x]

theorem valuations_complete (as : List Atom) (v : Atom → Bool) :
    ∃ w ∈ valuations as, ∀ a ∈ as, w a = v a := by
  induction as with
  | nil => exact ⟨fun _ => false, by simp [valuations], by simp⟩
  | cons a as ih =>
    obtain ⟨w, hw, hagree⟩ := ih
    refine ⟨fun x => if x = a then v a else w x, ?_, ?_⟩
    · simp only [valuations, List.mem_flatMap]
      refine ⟨w, hw, ?_⟩
      cases v a <;> simp
    · intro x hx
      by_cases h : x = a
      · simp [h]
      · have hx' : x ∈ as := by simpa [h] using hx
        simpa [h] using hagree x hx'

def support (policy : List (Formula Atom)) : List Atom :=
  unique (policy.flatMap Formula.atoms)

theorem atom_mem_support {p : Formula Atom} {a : Atom}
    (hp : p ∈ policy) (ha : a ∈ p.atoms) : a ∈ support policy := by
  simp only [support, mem_unique, List.mem_flatMap]
  exact ⟨p, hp, ha⟩

def satisfies (v : Atom → Bool) (policy : List (Formula Atom)) : Bool :=
  policy.all (Formula.eval v)

def Models (v : Atom → Bool) (policy : List (Formula Atom)) : Prop :=
  ∀ p ∈ policy, p.Holds v

omit [DecidableEq Atom] in
@[simp] theorem satisfies_eq_true_iff (v : Atom → Bool) (policy : List (Formula Atom)) :
    satisfies v policy = true ↔ Models v policy := by
  simp [satisfies, Models]

omit [DecidableEq Atom] in
@[simp] theorem models_nil (v : Atom → Bool) : Models v [] := by simp [Models]

omit [DecidableEq Atom] in
@[simp] theorem models_cons (v : Atom → Bool) (p : Formula Atom)
    (policy : List (Formula Atom)) :
    Models v (p :: policy) ↔ p.Holds v ∧ Models v policy := by
  simp [Models]

omit [DecidableEq Atom] in
@[simp] theorem models_append (v : Atom → Bool) (ps qs : List (Formula Atom)) :
    Models v (ps ++ qs) ↔ Models v ps ∧ Models v qs := by
  constructor
  · intro h
    exact ⟨fun p hp => h p (List.mem_append_left _ hp),
      fun p hp => h p (List.mem_append_right _ hp)⟩
  · rintro ⟨hp, hq⟩ p h
    exact (List.mem_append.mp h).elim (hp p) (hq p)

theorem satisfies_eq_of_agree (policy : List (Formula Atom)) (v w : Atom → Bool)
    (h : ∀ a ∈ support policy, v a = w a) : satisfies v policy = satisfies w policy := by
  unfold satisfies
  have hf : ∀ p ∈ policy, p.eval v = p.eval w := by
    intro p hp
    exact p.eval_eq_of_agree v w (fun a ha => h a (atom_mem_support hp ha))
  apply Bool.eq_iff_iff.mpr
  simp only [List.all_eq_true]
  constructor
  · intro hv p hp
    rw [← hf p hp]
    exact hv p hp
  · intro hw p hp
    rw [hf p hp]
    exact hw p hp

def model? (policy : List (Formula Atom)) : Option (Atom → Bool) :=
  (valuations (support policy)).find? (fun v => satisfies v policy)

def satisfiable (policy : List (Formula Atom)) : Bool :=
  (model? policy).isSome

theorem model?_sound (policy : List (Formula Atom)) (v : Atom → Bool)
    (h : model? policy = some v) : Models v policy := by
  apply (satisfies_eq_true_iff _ _).mp
  exact List.find?_some (p := fun w => satisfies w policy) h

theorem satisfiable_iff (policy : List (Formula Atom)) :
    satisfiable policy = true ↔ ∃ v, Models v policy := by
  simp only [satisfiable, model?, List.find?_isSome]
  constructor
  · rintro ⟨v, _, hv⟩
    exact ⟨v, (satisfies_eq_true_iff _ _).mp hv⟩
  · rintro ⟨v, hv⟩
    obtain ⟨w, hw, hagree⟩ := valuations_complete (support policy) v
    refine ⟨w, hw, ?_⟩
    rw [satisfies_eq_of_agree policy w v hagree]
    exact (satisfies_eq_true_iff _ _).mpr hv

theorem model?_eq_none_iff (policy : List (Formula Atom)) :
    model? policy = none ↔ ¬∃ v, Models v policy := by
  rw [← satisfiable_iff]
  cases h : model? policy <;> simp [satisfiable, h]

/-- Entailment checks all valuations over premises and conclusion together. -/
def entails (policy : List (Formula Atom)) (goal : Formula Atom) : Bool :=
  (valuations (support (goal :: policy))).all
    (fun v => !satisfies v policy || goal.eval v)

theorem entails_iff (policy : List (Formula Atom)) (goal : Formula Atom) :
    entails policy goal = true ↔ ∀ v, Models v policy → goal.Holds v := by
  constructor
  · intro h v hv
    obtain ⟨w, hw, hagree⟩ := valuations_complete (support (goal :: policy)) v
    have hpolicy : satisfies w policy = satisfies v policy :=
      satisfies_eq_of_agree policy w v (by
        intro a ha
        apply hagree a
        simp only [support, mem_unique, List.flatMap_cons, List.mem_append] at ha ⊢
        exact Or.inr ha)
    have hgoal : goal.eval w = goal.eval v :=
      goal.eval_eq_of_agree w v (fun a ha => hagree a (atom_mem_support (by simp) ha))
    have hall := List.all_eq_true.mp h w hw
    rw [hpolicy, hgoal, (satisfies_eq_true_iff _ _).mpr hv] at hall
    exact (Formula.eval_eq_true_iff _ _).mp (by simpa using hall)
  · intro h
    apply List.all_eq_true.mpr
    intro v _
    cases hp : satisfies v policy with
    | false => simp
    | true =>
      have hg := (Formula.eval_eq_true_iff _ _).mpr (h v ((satisfies_eq_true_iff _ _).mp hp))
      simp [hg]

theorem entails_mono {small large : List (Formula Atom)} {goal : Formula Atom}
    (hsub : ∀ p ∈ small, p ∈ large) (h : entails small goal = true) :
    entails large goal = true := by
  apply (entails_iff _ _).mpr
  intro v hv
  exact (entails_iff _ _).mp h v (fun p hp => hv p (hsub p hp))

theorem not_entails_of_subset {small large : List (Formula Atom)} {goal : Formula Atom}
    (hsub : ∀ p ∈ small, p ∈ large) (h : entails large goal = false) :
    entails small goal = false := by
  cases he : entails small goal with
  | false => rfl
  | true => have := entails_mono hsub he; simp_all

def countermodel? (policy : List (Formula Atom)) (goal : Formula Atom) :
    Option (Atom → Bool) :=
  (valuations (support (goal :: policy))).find?
    (fun v => satisfies v policy && !goal.eval v)

theorem countermodel?_sound (policy : List (Formula Atom)) (goal : Formula Atom)
    (v : Atom → Bool) (h : countermodel? policy goal = some v) :
    Models v policy ∧ ¬goal.Holds v := by
  have hv := List.find?_some h
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hv
  exact ⟨(satisfies_eq_true_iff _ _).mp hv.1, by
    intro hg
    have := (Formula.eval_eq_true_iff _ _).mpr hg
    simp_all⟩

theorem countermodel?_eq_none_iff (policy : List (Formula Atom)) (goal : Formula Atom) :
    countermodel? policy goal = none ↔ entails policy goal = true := by
  simp only [countermodel?, entails, List.find?_eq_none, List.all_eq_true]
  apply forall_congr'
  intro v
  apply forall_congr'
  intro _
  cases satisfies v policy <;> cases goal.eval v <;> simp

theorem not_entails_iff (policy : List (Formula Atom)) (goal : Formula Atom) :
    entails policy goal = false ↔ ∃ v, Models v policy ∧ ¬goal.Holds v := by
  constructor
  · intro h
    cases hc : countermodel? policy goal with
    | none =>
      have := (countermodel?_eq_none_iff _ _).mp hc
      simp_all
    | some v => exact ⟨v, countermodel?_sound policy goal v hc⟩
  · rintro ⟨v, hv, hgoal⟩
    cases he : entails policy goal with
    | false => rfl
    | true => exact False.elim (hgoal ((entails_iff _ _).mp he v hv))

def missingGoals (policy goals : List (Formula Atom)) : List (Formula Atom) :=
  goals.filter (fun goal => !entails policy goal)

theorem mem_missingGoals (policy goals : List (Formula Atom)) (goal : Formula Atom) :
    goal ∈ missingGoals policy goals ↔
      goal ∈ goals ∧ ∃ v, Models v policy ∧ ¬goal.Holds v := by
  simp [missingGoals, not_entails_iff]

/-- A requirement is deleted only against the policy remaining at that step. -/
private def prune (kept : List (Formula Atom)) : List (Formula Atom) → List (Formula Atom)
  | [] => kept
  | p :: ps =>
    if entails (kept ++ ps) p then prune kept ps else prune (kept ++ [p]) ps

private theorem prune_preserves (v : Atom → Bool) (todo kept : List (Formula Atom)) :
    Models v (prune kept todo) ↔ Models v (kept ++ todo) := by
  induction todo generalizing kept with
  | nil => simp [prune]
  | cons p ps ih =>
    simp only [prune]
    split
    next h =>
      rw [ih]
      have hp := (entails_iff _ _).mp h v
      simp only [models_append, models_cons] at hp ⊢
      constructor
      · intro hmodels
        exact ⟨hmodels.1, hp hmodels, hmodels.2⟩
      · intro hmodels
        exact ⟨hmodels.1, hmodels.2.2⟩
    next _ =>
      rw [ih]
      simp [List.append_assoc]

private theorem prune_subset (todo kept : List (Formula Atom)) :
    ∀ p ∈ prune kept todo, p ∈ kept ++ todo := by
  induction todo generalizing kept with
  | nil => simp [prune]
  | cons p ps ih =>
    simp only [prune]
    split
    next _ =>
      intro q hq
      rcases List.mem_append.mp (ih kept q hq) with hq | hq
      · exact List.mem_append_left _ hq
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ hq)
    next _ =>
      simpa [List.append_assoc] using ih (kept ++ [p])

def minimize (policy : List (Formula Atom)) : List (Formula Atom) :=
  prune [] policy

theorem minimize_preserves (v : Atom → Bool) (policy : List (Formula Atom)) :
    Models v (minimize policy) ↔ Models v policy := by
  simpa [minimize] using prune_preserves v policy []

theorem minimize_subset (policy : List (Formula Atom)) :
    ∀ p ∈ minimize policy, p ∈ policy := by
  simpa [minimize] using prune_subset policy []

private theorem prune_irredundant (todo kept : List (Formula Atom))
    (hinv : ∀ p ∈ kept, entails (kept.erase p ++ todo) p = false) :
    ∀ p ∈ prune kept todo, entails ((prune kept todo).erase p) p = false := by
  induction todo generalizing kept with
  | nil => simpa [prune] using hinv
  | cons p ps ih =>
    simp only [prune]
    split
    next _ =>
      apply ih kept
      intro q hq
      apply not_entails_of_subset (large := kept.erase q ++ p :: ps) _ (hinv q hq)
      intro f hf
      rcases List.mem_append.mp hf with hf | hf
      · exact List.mem_append_left _ hf
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ hf)
    next h =>
      apply ih (kept ++ [p])
      intro q hq
      rcases List.mem_append.mp hq with hq | hq
      · rw [List.erase_append_left _ hq, List.append_assoc]
        exact hinv q hq
      · have hqp : q = p := by simpa using hq
        subst q
        have hp : p ∉ kept := by
          intro hp
          apply h
          apply (entails_iff _ _).mpr
          intro v hv
          exact hv p (List.mem_append_left _ hp)
        rw [List.erase_append_right _ hp]
        simpa using h

/-- Every remaining occurrence is essential, including when inputs contain duplicates. -/
theorem minimize_irredundant (policy : List (Formula Atom)) :
    ∀ p ∈ minimize policy, entails ((minimize policy).erase p) p = false := by
  exact prune_irredundant policy [] (by simp)

/-- Completion is relative to explicit goals and rejects inconsistent additions. -/
def completion? (policy goals : List (Formula Atom)) : Option (List (Formula Atom)) :=
  if satisfiable (policy ++ goals) then some (minimize (policy ++ goals)) else none

theorem completion?_sound (policy goals result : List (Formula Atom))
    (h : completion? policy goals = some result) :
    (∃ v, Models v result) ∧
      (∀ v, Models v result ↔ Models v policy ∧ Models v goals) := by
  unfold completion? at h
  split at h
  next hs =>
    cases h
    constructor
    · obtain ⟨v, hv⟩ := (satisfiable_iff _).mp hs
      exact ⟨v, (minimize_preserves v _).mpr hv⟩
    · intro v
      rw [minimize_preserves, models_append]
  next _ => contradiction

end Netlib.Reasoning
