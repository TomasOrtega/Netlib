import Netlib.Policy.Language
import Netlib.Network.Basic
import Netlib.Core.Reasoning

namespace Netlib.Observation

universe u
variable {Node : Type u}

/-- Selector meanings and traffic-specific forwarding graphs determine each observation. -/
def Denotes (select : Selector → Node → Prop) (network : String → Network Node) :
    Observation → Prop
  | .reach source target service true =>
    ∀ a b, select source a → select target b → (network service).Reachable a b
  | .reach source target service false =>
    ∃ a b, select source a ∧ select target b ∧ (network service).Reachable a b
  | .mediated source target gateways service =>
    (network service).Mediated (select source) (select target) (select gateways)

variable {select : Selector → Node → Prop} {network : String → Network Node}
variable {source target gateways : Selector} {service : String}

theorem some_of_all
    (sourceNonempty : ∃ a, select source a) (targetNonempty : ∃ b, select target b)
    (all : Denotes select network (.reach source target service true)) :
    Denotes select network (.reach source target service false) := by
  obtain ⟨a, ha⟩ := sourceNonempty
  obtain ⟨b, hb⟩ := targetNonempty
  exact ⟨a, b, ha, hb, all a b ha hb⟩

/-- Existential reachability implies universal reachability only for singleton endpoint sets. -/
theorem all_of_some_singletons
    (sourceUnique : ∀ a b, select source a → select source b → a = b)
    (targetUnique : ∀ a b, select target a → select target b → a = b)
    (some : Denotes select network (.reach source target service false)) :
    Denotes select network (.reach source target service true) := by
  obtain ⟨a, b, ha, hb, path⟩ := some
  intro x y hx hy
  have sourceSame := sourceUnique a x ha hx
  have targetSame := targetUnique b y hb hy
  simpa [← sourceSame, ← targetSame] using path

/-- Isolation excludes bypasses through every possible gateway set. -/
theorem mediated_of_not_some
    (isolated : ¬Denotes select network (.reach source target service false)) :
    Denotes select network (.mediated source target gateways service) := by
  intro a b ha hb bypass
  apply isolated
  exact ⟨a, b, ha, hb, Network.reachable_restrict _ bypass.2.2⟩

/-- An ordinary interpretation supplies Boolean observations exactly when their meanings hold. -/
def Faithful (observe : Observation → Bool) (select : Selector → Node → Prop)
    (network : String → Network Node) : Prop :=
  ∀ observation, observe observation = true ↔ Denotes select network observation

private theorem mem_of_mem_eraseDups {Atom : Type v} [BEq Atom] (atoms : List Atom)
    {atom : Atom} (member : atom ∈ atoms.eraseDups) : atom ∈ atoms := by
  match atoms with
  | [] => simp at member
  | a :: tail =>
    rw [List.eraseDups_cons] at member
    rcases List.mem_cons.mp member with rfl | member
    · simp
    · exact List.mem_cons_of_mem _
        (List.mem_filter.mp (mem_of_mem_eraseDups _ member)).1
termination_by atoms.length
decreasing_by exact Nat.lt_succ_of_le (List.length_filter_le _ _)

/-- Every generated propositional law is valid for any faithful network interpretation. -/
theorem laws_sound (observations : List Observation) (observe : Observation → Bool)
    (faithful : Faithful observe select network)
    (nonempty : ∀ observation ∈ observations, ∀ selector ∈ observation.selectors,
      ∃ node, select selector node)
    (nodeUnique : ∀ name a b, select (.node name) a → select (.node name) b → a = b) :
    ∀ law ∈ Language.laws observations, law.Holds observe := by
  intro law member
  unfold Language.laws at member
  have member := mem_of_mem_eraseDups _ member
  simp only [List.mem_flatMap] at member
  obtain ⟨observation, observed, member⟩ := member
  cases observation with
  | reach source target service universal =>
    have forward : (Formula.impl (.atom (.reach source target service true))
        (.atom (.reach source target service false))).Holds observe := by
      intro all
      apply (faithful _).mpr
      apply some_of_all
      · exact nonempty _ observed source (by simp [selectors])
      · exact nonempty _ observed target (by simp [selectors])
      · exact (faithful _).mp all
    have singletonBackward (s t : String) :
        (Formula.impl (.atom (.reach (.node s) (.node t) service false))
          (.atom (.reach (.node s) (.node t) service true))).Holds observe := by
      intro some
      apply (faithful _).mpr
      exact all_of_some_singletons (nodeUnique s) (nodeUnique t) ((faithful _).mp some)
    cases source <;> cases target <;>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    all_goals first
      | subst law; exact forward
      | rcases member with rfl | rfl
        · exact forward
        · exact singletonBackward _ _
  | mediated source target gateways service =>
    simp only [List.mem_singleton] at member
    subst law
    intro notSome
    apply (faithful _).mpr
    apply mediated_of_not_some
    intro some
    exact notSome ((faithful _).mpr some)

/-- An abstract entailment holds in each faithful network interpretation. -/
theorem entails_sound (observations : List Observation) (observe : Observation → Bool)
    (faithful : Faithful observe select network)
    (nonempty : ∀ observation ∈ observations, ∀ selector ∈ observation.selectors,
      ∃ node, select selector node)
    (nodeUnique : ∀ name a b, select (.node name) a → select (.node name) b → a = b)
    (policy : List (Formula Observation)) (goal : Formula Observation)
    (entails : Reasoning.entails (Language.laws observations ++ policy) goal = true)
    (compliant : Reasoning.Models observe policy) : goal.Holds observe := by
  apply (Reasoning.entails_iff _ _).mp entails observe
  exact (Reasoning.models_append _ _ _).mpr
    ⟨laws_sound observations observe faithful nonempty nodeUnique, compliant⟩

/-- An inconsistent abstract policy has no faithful network interpretation. -/
theorem inconsistent_excludes_interpretation (observations : List Observation)
    (observe : Observation → Bool) (faithful : Faithful observe select network)
    (nonempty : ∀ observation ∈ observations, ∀ selector ∈ observation.selectors,
      ∃ node, select selector node)
    (nodeUnique : ∀ name a b, select (.node name) a → select (.node name) b → a = b)
    (policy : List (Formula Observation))
    (inconsistent : Reasoning.satisfiable (Language.laws observations ++ policy) = false) :
    ¬Reasoning.Models observe policy := by
  intro compliant
  have satisfiable := (Reasoning.satisfiable_iff _).mpr
    ⟨observe, (Reasoning.models_append _ _ _).mpr
      ⟨laws_sound observations observe faithful nonempty nodeUnique, compliant⟩⟩
  simp_all

end Netlib.Observation
