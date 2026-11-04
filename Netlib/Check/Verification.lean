import Netlib.Check.Compliance
import Netlib.Policy.Observation

namespace Netlib.Verification

open Certificate Compliance

/-- The executable gateway filter removes every incident forwarding edge. -/
def bypassEdge (edge : String → String → Bool) (gateways : List String)
    (a b : String) : Bool :=
  edge a b && !gateways.contains a && !gateways.contains b

theorem bypass_network_eq (nodes gateways : List String) (edge : String → String → Bool) :
    finiteNetwork nodes (bypassEdge edge gateways) =
      (finiteNetwork nodes edge).without (fun node => node ∈ gateways) := by
  unfold finiteNetwork Network.without Network.restrict
  congr 1
  funext a b
  apply propext
  simp [bypassEdge, and_assoc, and_left_comm, and_comm]

/-- The endpoint shortcut and bypass certificate together decide formal gateway mediation. -/
theorem mediation_pair_correct (nodes gateways : List String)
    (edge : String → String → Bool) (source target : String)
    (result : Decision nodes (bypassEdge edge gateways) source target) :
    (gateways.contains source || gateways.contains target || !result.value) = true ↔
      ¬Network.Bypass (finiteNetwork nodes edge) (fun node => node ∈ gateways) source target := by
  have reach := result.correct
  rw [bypass_network_eq] at reach
  simp only [Network.Bypass]
  by_cases sourceGateway : source ∈ gateways
  · simp [sourceGateway]
  · by_cases targetGateway : target ∈ gateways
    · simp [targetGateway]
    · have sourceAbsent : gateways.contains source = false := by simp [sourceGateway]
      have targetAbsent : gateways.contains target = false := by simp [targetGateway]
      simp only [sourceAbsent, targetAbsent, Bool.false_or,
        sourceGateway, targetGateway, not_false_eq_true, true_and]
      cases value : result.value <;> simp_all

/-- Universal compliance checks every ordered endpoint pair. -/
def allPairs (sources targets : List Node) (check : Node → Node → Bool) : Bool :=
  sources.all fun source => targets.all fun target => check source target

/-- Existential reachability requires at least one ordered endpoint pair. -/
def somePairs (sources targets : List Node) (check : Node → Node → Bool) : Bool :=
  sources.any fun source => targets.any fun target => check source target

theorem allPairs_eq_true_iff (sources targets : List Node) (check : Node → Node → Bool) :
    allPairs sources targets check = true ↔
      ∀ source ∈ sources, ∀ target ∈ targets, check source target = true := by
  simp [allPairs, List.all_eq_true]

theorem somePairs_eq_true_iff (sources targets : List Node) (check : Node → Node → Bool) :
    somePairs sources targets check = true ↔
      ∃ source ∈ sources, ∃ target ∈ targets, check source target = true := by
  simp [somePairs, List.any_eq_true]

/-- Reachability certificates lift from individual pairs to the universal observation. -/
theorem all_reach_denotes (sources targets : List String) (net : Network String)
    (check : String → String → Bool)
    (correct : ∀ source ∈ sources, ∀ target ∈ targets,
      check source target = true ↔ net.Reachable source target) :
    allPairs sources targets check = true ↔
      ∀ source target, source ∈ sources → target ∈ targets → net.Reachable source target := by
  rw [allPairs_eq_true_iff]
  constructor
  · intro all source target hs ht
    exact (correct source hs target ht).mp (all source hs target ht)
  · intro all source hs target ht
    exact (correct source hs target ht).mpr (all source target hs ht)

/-- The isolation predicate is the negation of existential, rather than universal, reachability. -/
theorem isolated_iff_not_some (sources targets : List String) (net : Network String)
    (check : String → String → Bool)
    (correct : ∀ source ∈ sources, ∀ target ∈ targets,
      check source target = true ↔ net.Reachable source target) :
    somePairs sources targets check = false ↔
      net.Isolated (fun node => node ∈ sources) (fun node => node ∈ targets) := by
  constructor
  · intro none source target hs ht path
    have some := (somePairs_eq_true_iff _ _ _).mpr
      ⟨source, hs, target, ht, (correct source hs target ht).mpr path⟩
    simp_all
  · intro isolated
    cases value : somePairs sources targets check with
    | false => rfl
    | true =>
      obtain ⟨source, hs, target, ht, reached⟩ := (somePairs_eq_true_iff _ _ _).mp value
      exact False.elim (isolated source target hs ht ((correct source hs target ht).mp reached))

/-- This form matches the executable shortcut before bypass search. -/
theorem mediation_pair_if_correct (nodes gateways : List String)
    (edge : String → String → Bool) (source target : String)
    (result : Decision nodes (bypassEdge edge gateways) source target) :
    (if gateways.contains source || gateways.contains target then true else !result.value) = true ↔
      ¬Network.Bypass (finiteNetwork nodes edge) (fun node => node ∈ gateways) source target := by
  have shape : (if gateways.contains source || gateways.contains target then true
      else !result.value) =
      (gateways.contains source || gateways.contains target || !result.value) := by
    cases gateways.contains source <;> cases gateways.contains target <;> rfl
  rw [shape]
  exact mediation_pair_correct nodes gateways edge source target result

/-- All-pair aggregation of certified non-bypasses is exactly the architecture mediation property. -/
theorem mediated_pairs_correct (sources targets : List String) (net : Network String)
    (gateways : String → Prop) (check : String → String → Bool)
    (correct : ∀ source ∈ sources, ∀ target ∈ targets,
      check source target = true ↔ ¬net.Bypass gateways source target) :
    allPairs sources targets check = true ↔
      net.Mediated (fun node => node ∈ sources) (fun node => node ∈ targets) gateways := by
  rw [allPairs_eq_true_iff]
  constructor
  · intro all source target hs ht
    exact (correct source hs target ht).mp (all source hs target ht)
  · intro mediated source hs target ht
    exact (correct source hs target ht).mpr (mediated source target hs ht)

/-- Universal and existential aggregation agree with the requirement observation semantics. -/
theorem reach_observation_correct (select : Selector → List String)
    (network : String → Network String) (source target : Selector) (service : String)
    (universal : Bool) (check : String → String → Bool)
    (correct : ∀ a ∈ select source, ∀ b ∈ select target,
      check a b = true ↔ (network service).Reachable a b) :
    (if universal then allPairs (select source) (select target) check
      else somePairs (select source) (select target) check) = true ↔
      Observation.Denotes (fun selector node => node ∈ select selector) network
        (.reach source target service universal) := by
  cases universal with
  | true => exact all_reach_denotes _ _ _ _ correct
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte, Observation.Denotes, somePairs_eq_true_iff]
    constructor
    · rintro ⟨a, ha, b, hb, reached⟩
      exact ⟨a, b, ha, hb, (correct a ha b hb).mp reached⟩
    · rintro ⟨a, b, ha, hb, reached⟩
      exact ⟨a, ha, b, hb, (correct a ha b hb).mpr reached⟩

/-- A Boolean value has a proof of its meaning. -/
structure CertifiedValue (meaning : Prop) where
  value : Bool
  correct : value = true ↔ meaning

private def certifyAll {Item : Type u} (meaning : Item → Prop)
    (check : (item : Item) → Except String (CertifiedValue (meaning item))) :
    (items : List Item) → Except String (CertifiedValue (∀ item ∈ items, meaning item))
  | [] => .ok ⟨true, by simp⟩
  | item :: items => do
    let head ← check item
    let tail ← certifyAll meaning check items
    return ⟨head.value && tail.value, by
      simp only [Bool.and_eq_true, head.correct, tail.correct, List.forall_mem_cons]⟩

private def certifySome {Item : Type u} (meaning : Item → Prop)
    (check : (item : Item) → Except String (CertifiedValue (meaning item))) :
    (items : List Item) → Except String (CertifiedValue (∃ item ∈ items, meaning item))
  | [] => .ok ⟨false, by simp⟩
  | item :: items => do
    let head ← check item
    let tail ← certifySome meaning check items
    return ⟨head.value || tail.value, by
      simp only [Bool.or_eq_true, head.correct, tail.correct]
      constructor
      · rintro (here | ⟨other, member, there⟩)
        · exact ⟨item, by simp, here⟩
        · exact ⟨other, List.mem_cons_of_mem _ member, there⟩
      · rintro ⟨other, member, holds⟩
        rcases List.mem_cons.mp member with rfl | member
        · exact .inl holds
        · exact .inr ⟨other, member, holds⟩⟩

private def certifyEveryPair {Item : Type u} (sources targets : List Item)
    (relation : Item → Item → Prop)
    (check : (source target : Item) → Except String (CertifiedValue (relation source target))) :
    Except String (CertifiedValue
      (∀ source target, source ∈ sources → target ∈ targets → relation source target)) := do
  let result ← certifyAll (fun source => ∀ target ∈ targets, relation source target)
    (fun source => certifyAll (relation source) (check source) targets) sources
  return ⟨result.value, by
    rw [result.correct]
    constructor
    · exact fun every source target hs ht => every source hs target ht
    · exact fun every source hs target ht => every source target hs ht⟩

private def certifySomePair {Item : Type u} (sources targets : List Item)
    (relation : Item → Item → Prop)
    (check : (source target : Item) → Except String (CertifiedValue (relation source target))) :
    Except String (CertifiedValue
      (∃ source target, source ∈ sources ∧ target ∈ targets ∧ relation source target)) := do
  let result ← certifySome (fun source => ∃ target ∈ targets, relation source target)
    (fun source => certifySome (relation source) (check source) targets) sources
  return ⟨result.value, by
    rw [result.correct]
    constructor
    · rintro ⟨source, hs, target, ht, related⟩
      exact ⟨source, target, hs, ht, related⟩
    · rintro ⟨source, target, hs, ht, related⟩
      exact ⟨source, hs, target, ht, related⟩⟩

/-- The precise finite model used by the executable certificate checker. -/
def model (config : Config) (service : String) : Network String :=
  finiteNetwork config.ids (config.edge service)

/-- Configuration selectors retain all members, including every HA replica. -/
def selection (config : Config) (selector : Selector) (node : String) : Prop :=
  node ∈ config.select selector

private def certifiedReach (config : Config) (service source target : String) :
    Except String (CertifiedValue ((model config service).Reachable source target)) := do
  let result ← decideReach config.ids (config.edge service) source target
  return ⟨result.value, result.correct⟩

private def certifiedMediation (config : Config) (service : String) (gateways : List String)
    (source target : String) :
    Except String (CertifiedValue
      (¬(model config service).Bypass (fun node => node ∈ gateways) source target)) := do
  if endpoint : (gateways.contains source || gateways.contains target) = true then
    have member : source ∈ gateways ∨ target ∈ gateways := by simpa using endpoint
    return ⟨true, by
      constructor
      · intro _ bypass
        rcases member with sourceGateway | targetGateway
        · exact bypass.1 sourceGateway
        · exact bypass.2.1 targetGateway
      · intro _; rfl⟩
  else
    let result ← decideReach config.ids (bypassEdge (config.edge service) gateways) source target
    return ⟨!result.value, by
      have correct := mediation_pair_if_correct config.ids gateways (config.edge service)
        source target result
      simpa only [ite_eq_right endpoint, model] using correct⟩

/-- Each successful result has a proof for every selected endpoint pair. -/
def evaluate (config : Config) (observation : Observation) :
    Except String (CertifiedValue
      (Observation.Denotes (selection config) (model config) observation)) :=
  match observation with
  | .reach source target service true =>
    certifyEveryPair (config.select source) (config.select target)
      (Network.Reachable (model config service)) (certifiedReach config service)
  | .reach source target service false =>
    certifySomePair (config.select source) (config.select target)
      (Network.Reachable (model config service)) (certifiedReach config service)
  | .mediated source target gateways service =>
    certifyEveryPair (config.select source) (config.select target)
      (fun a b => ¬(model config service).Bypass (selection config gateways) a b)
      (certifiedMediation config service (config.select gateways))

/-- Requirements retain the logical meaning of their network observations. -/
def formulaMeaning (config : Config) : Formula Observation → Prop
  | .atom observation => Observation.Denotes (selection config) (model config) observation
  | .top => True
  | .bot => False
  | .neg formula => ¬formulaMeaning config formula
  | .conj left right => formulaMeaning config left ∧ formulaMeaning config right
  | .disj left right => formulaMeaning config left ∨ formulaMeaning config right
  | .impl left right => formulaMeaning config left → formulaMeaning config right

/-- Successful requirement evaluation carries a proof through every logical connective. -/
def evaluateFormula (config : Config) :
    (formula : Formula Observation) → Except String (CertifiedValue (formulaMeaning config formula))
  | .atom observation => evaluate config observation
  | .top => .ok ⟨true, by simp [formulaMeaning]⟩
  | .bot => .ok ⟨false, by simp [formulaMeaning]⟩
  | .neg formula => do
    let result ← evaluateFormula config formula
    return ⟨!result.value, by
      simp only [formulaMeaning, ← result.correct]
      cases result.value <;> simp⟩
  | .conj left right => do
    let lhs ← evaluateFormula config left
    let rhs ← evaluateFormula config right
    return ⟨lhs.value && rhs.value, by
      simp only [formulaMeaning, Bool.and_eq_true, lhs.correct, rhs.correct]⟩
  | .disj left right => do
    let lhs ← evaluateFormula config left
    let rhs ← evaluateFormula config right
    return ⟨lhs.value || rhs.value, by
      simp only [formulaMeaning, Bool.or_eq_true, lhs.correct, rhs.correct]⟩
  | .impl left right => do
    let lhs ← evaluateFormula config left
    let rhs ← evaluateFormula config right
    return ⟨!lhs.value || rhs.value, by
      simp only [formulaMeaning, ← lhs.correct, ← rhs.correct]
      cases lhs.value <;> cases rhs.value <;> simp⟩

end Netlib.Verification
