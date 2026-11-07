import Netlib.Model.FederatedJson
import Netlib.Check.FederatedLocalPlan
import Netlib.Check.FederatedQueries

/-!
# Checked deployments for two independent operators

Native checking runs locally for every revision. Public compatibility and
query checks consume the resulting fixed contracts and declared borders.
-/

namespace Netlib.Federation.Deployment

def workEstimate (input : Input) : Nat :=
  LocalPlan.workEstimate input.left + LocalPlan.workEstimate input.right +
    Queries.workEstimate input.left.contract input.right.contract input.intent

structure Checked (input : Input) where
  within : workEstimate input ≤ input.work
  left : LocalPlan.Checked input.left
  right : LocalPlan.Checked input.right
  compatible : Compatibility.Compatible input.left.contract input.right.contract input.intent
  queries : Queries.Checked input.left.contract input.right.contract input.intent

def certify (input : Input) : Except String (Checked input) := do
  if within : workEstimate input ≤ input.work then
    let limits : Native.Limits := ⟨input.cells, input.work⟩
    let left ← LocalPlan.check input.left limits
    let right ← LocalPlan.check input.right limits
    let compatible ← Compatibility.check input.left.contract input.right.contract input.intent
    let queries ← Queries.check input.left.contract input.right.contract input.intent compatible input.work
    return ⟨within, left, right, compatible, queries⟩
  else throw s!"Complete federation work estimate {workEstimate input} exceeds budget {input.work}."

def certifyJson (text : String) : Except String ((input : Input) × Checked input) := do
  let input ← Json.parse text
  return ⟨input, ← certify input⟩

theorem Checked.covered (value : Checked input) :
    value.queries.results.map Sigma.fst = input.intent.queries := value.queries.covered

theorem Checked.result_for (value : Checked input) (query : Query) (member : query ∈ input.intent.queries) :
    ∃ result : Queries.Result input.left.contract input.right.contract input.intent query,
      ⟨query, result⟩ ∈ value.queries.results := by
  rw [← value.covered] at member
  obtain ⟨⟨actual, result⟩, stored, same⟩ := List.mem_map.mp member
  dsimp only at same
  subst actual
  exact ⟨result, stored⟩

def Checked.resultAt (value : Checked input) (index : Fin value.queries.results.length) :
    (query : Query) × Queries.Result input.left.contract input.right.contract input.intent query :=
  value.queries.results[index.val]

theorem Checked.local_sources (value : Checked input) (left : input.left.Cursor) (right : input.right.Cursor) :
    ⟨input.left.revisionAt left, value.left.nativeAt left⟩ ∈ value.left.revisions ∧
      ⟨input.right.revisionAt right, value.right.nativeAt right⟩ ∈ value.right.revisions :=
  ⟨value.left.nativeAt_stored left, value.right.nativeAt_stored right⟩

end Netlib.Federation.Deployment
