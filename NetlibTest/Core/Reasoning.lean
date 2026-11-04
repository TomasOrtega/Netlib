import Netlib.Core.Reasoning
import Netlib.Policy.Analysis

namespace NetlibTest.Reasoning

open Netlib Netlib.Reasoning

private def p : Formula Nat := .atom 0
private def q : Formula Nat := .atom 1

example : (valuations ([] : List Nat)).length = 1 := by decide
example : (valuations [0, 1, 2]).length = 8 := by decide
example : (support [p, .conj p q, .impl q p]).length = 2 := by decide

example : satisfiable ([] : List (Formula Nat)) = true := by decide
example : satisfiable [p, .impl p q] = true := by decide
example : satisfiable [p, .neg p] = false := by decide
example : model? [(.bot : Formula Nat)] = none := by rfl
example : (model? [p, .neg q]).map (fun v => (v 0, v 1)) = some (true, false) := by
  decide

example : entails [p, .impl p q] q = true := by decide
example : entails [p] q = false := by decide
example : entails ([] : List (Formula Nat)) p = false := by decide
example : entails ([] : List (Formula Nat)) (.impl p p) = true := by decide
example : entails [p, .neg p] q = true := by decide

example : countermodel? [p, .impl p q] q = none := by rfl
example : (countermodel? [p] q).map (fun v => (v 0, v 1)) = some (true, false) := by
  decide
example : (countermodel? [] p).map (fun v => v 0) = some false := by decide

example : minimize [p, p] = [p] := by decide
example : minimize [p, .conj p q, q] = [.conj p q] := by decide
example : minimize [.conj p q, p] = [.conj p q] := by decide
example : minimize [.impl p p] = [] := by decide
example : minimize [p, .neg p, q] = [p, .neg p] := by decide

example (v : Nat → Bool) :
    Models v (minimize [p, .conj p q, q]) ↔ Models v [p, .conj p q, q] :=
  minimize_preserves v _

example : ∀ f ∈ minimize [p, .conj p q, q],
    entails ((minimize [p, .conj p q, q]).erase f) f = false :=
  minimize_irredundant _

example : missingGoals [p] [p, q] = [q] := by decide
example : completion? [p] [q] = some [p, q] := by decide
example : completion? [p] [.neg p] = none := by decide
example : completion? [p, .neg p] [q] = none := by decide
example : completion? ([] : List (Formula Nat)) [] = some [] := by decide

end NetlibTest.Reasoning

namespace NetlibTest.Analysis

open Netlib Netlib.Analysis

private def reach : Observation := .reach (.node "client") (.node "server") "ssh" true
private def someReach : Observation := .reach (.node "client") (.node "server") "ssh" false
private def med : Observation :=
  .mediated (.node "client") (.node "server") (.role "gateway") "ssh"

private def requirement (id : String) (f : Formula Observation) : Requirement :=
  ⟨id, 7, "Preserved source sentence.", f⟩

private def result? (requirements goals : List Requirement) : Option Report :=
  (analyze requirements goals).toOption

example : (result? [] [requirement "G1" (.atom reach), requirement "G2" (.atom med)]).map
    (fun r => r.gaps.map (·.goal.id)) = some ["G1", "G2"] := by decide

example : (result? [requirement "R1" (.atom reach),
    requirement "R2" (.neg (.atom someReach))] []).map (·.consistent) = some false := by decide

example : (result? [requirement "R1" (.atom reach),
    requirement "R2" (.atom someReach)] []).map
    (fun r => (r.retained.map (·.id), r.redundant.map (·.id))) =
      some (["R2"], ["R1"]) := by decide

example : (result? [requirement "R1" (.neg (.atom someReach))]
    [requirement "G1" (.atom med)]).map (fun r => r.gaps.length) = some 0 := by decide

example : (result? [] [requirement "G1" (.atom reach),
    requirement "G2" (.neg (.atom someReach))]).map (fun r => r.additions.isNone) =
      some true := by decide

example : (result? [requirement "R1" (.atom reach)] []).map
    (fun r => (r.retained.map (·.line), r.retained.map (·.text))) =
      some ([7], ["Preserved source sentence."]) := by decide

private def oversized : List Requirement :=
  (List.range 9).map fun i => requirement (toString i)
    (.atom (.reach (.node "client") (.node (toString i)) "ssh" true))

set_option maxRecDepth 4096 in
example : (analyze oversized []).toOption.isNone = true := by decide
set_option maxRecDepth 4096 in
example : (analyze [] oversized).toOption.isNone = true := by decide

end NetlibTest.Analysis
