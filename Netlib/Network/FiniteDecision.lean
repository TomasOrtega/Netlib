import Netlib.Network.Certificate

/-!
# Finite graph decisions on typed nodes

Search proposes a full path or a closed cut. The certificate checker validates
that evidence against the exact queried graph before a decision is returned.
-/

namespace Netlib.FiniteDecision

universe u

open Certificate

variable {Node : Type u} [DecidableEq Node]

inductive Decision (nodes : List Node) (edge : Node → Node → Bool) (source target : Node) where
  | reachable (trace : List Node) (valid : validPath nodes edge source target trace = true)
  | isolated (region : List Node) (valid : validCut nodes edge source target region = true)

namespace Decision

variable {nodes : List Node} {edge : Node → Node → Bool} {source target : Node}

def value : Decision nodes edge source target → Bool
  | .reachable _ _ => true
  | .isolated _ _ => false

def path? : Decision nodes edge source target → Option (List Node)
  | .reachable trace _ => some trace
  | .isolated _ _ => none

def cut? : Decision nodes edge source target → Option (List Node)
  | .reachable _ _ => none
  | .isolated region _ => some region

theorem correct (result : Decision nodes edge source target) :
    result.value = true ↔ Network.Reachable (finiteNetwork nodes edge) source target := by
  cases result with
  | reachable trace valid => exact ⟨fun _ => validPath_sound _ _ _ _ _ valid, fun _ => rfl⟩
  | isolated region valid =>
    constructor
    · intro impossible; cases impossible
    · intro reached
      exact False.elim (validCut_sound nodes edge source target region valid reached)

theorem path_valid (result : Decision nodes edge source target) (trace : List Node)
    (selected : result.path? = some trace) : validPath nodes edge source target trace = true := by
  cases result with
  | reachable actual valid =>
    have same : actual = trace := Option.some.inj selected
    exact same ▸ valid
  | isolated region valid => cases selected

theorem cut_valid (result : Decision nodes edge source target) (region : List Node)
    (selected : result.cut? = some region) : validCut nodes edge source target region = true := by
  cases result with
  | reachable trace valid => cases selected
  | isolated actual valid =>
    have same : actual = region := Option.some.inj selected
    exact same ▸ valid

end Decision

private def discover (nodes : List Node) (edge : Node → Node → Bool) (source : Node) :
    List (Node × List Node) := Id.run do
  let mut known := [(source, [source])]
  for _ in List.range nodes.length do
    let snapshot := known
    for (current, path) in snapshot do
      for next in nodes do
        if edge current next && !(known.any (fun entry => decide (entry.1 = next))) then
          known := known ++ [(next, path ++ [next])]
  return known

def decideReach (nodes : List Node) (edge : Node → Node → Bool) (source target : Node) :
    Except String (Decision nodes edge source target) := do
  if source ∉ nodes then throw "The source node is absent from the finite graph."
  if target ∉ nodes then throw "The target node is absent from the finite graph."
  let known := discover nodes edge source
  match known.find? (fun entry => decide (entry.1 = target)) with
  | some (_, trace) =>
    if valid : validPath nodes edge source target trace = true then
      return .reachable trace valid
    else throw "The finite graph search produced an invalid path certificate."
  | none =>
    let region := known.map Prod.fst
    if valid : validCut nodes edge source target region = true then
      return .isolated region valid
    else throw "The finite graph search produced an invalid cut certificate."

def bypassEdge (edge : Node → Node → Bool) (gateways : List Node) (source target : Node) : Bool :=
  edge source target && decide (source ∉ gateways) && decide (target ∉ gateways)

theorem bypass_network_eq (nodes gateways : List Node) (edge : Node → Node → Bool) :
    finiteNetwork nodes (bypassEdge edge gateways) =
      (finiteNetwork nodes edge).without (fun node => node ∈ gateways) := by
  unfold finiteNetwork Network.without Network.restrict
  congr 1
  funext source target
  apply propext
  simp [bypassEdge, and_assoc, and_left_comm, and_comm]

end Netlib.FiniteDecision

namespace Netlib.Certificate

universe u

variable {Node : Type u} [DecidableEq Node]

theorem validPath_walk (nodes : List Node) (edge : Node → Node → Bool)
    (source target : Node) (trace : List Node) (valid : validPath nodes edge source target trace = true) :
    Network.Walk (finiteNetwork nodes edge) source target trace := by
  induction trace generalizing source with
  | nil => simp [validPath] at valid
  | cons head tail ih =>
    cases tail with
    | nil =>
      simp only [validPath, Bool.and_eq_true, decide_eq_true_eq] at valid
      rcases valid with ⟨⟨rfl, rfl⟩, _⟩
      exact .nil head
    | cons next rest =>
      simp only [validPath, Bool.and_eq_true, decide_eq_true_eq] at valid
      rcases valid with ⟨⟨⟨⟨rfl, headNode⟩, nextNode⟩, edge⟩, suffix⟩
      exact .cons ⟨headNode, nextNode, edge⟩ (ih next suffix)

end Netlib.Certificate
