import Netlib.Theory.FiniteSuccessorGraph

namespace NetlibTest.FederatedCohortGraph

namespace S
export Netlib.Theory.FiniteSuccessorGraph (Model Costs Limits Checked check checkLive workEstimate)
end S

private def ensure (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def load : Except String α → IO α
  | .ok value => pure value
  | .error reason => throw (IO.userError reason)

private def reject (result : Except String α) (message : String) : IO Unit :=
  match result with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError message)

private def linear : S.Model Nat String := {
  initial := 0
  successors := fun
    | 0 => [("first", 1)]
    | 1 => [("second", 2)]
    | _ => []
  terminal := fun state => decide (state = 2) }

private def hiddenDeadlock : S.Model Nat String := {
  initial := 0
  successors := fun
    | 0 => [("selected", 1), ("other", 2)]
    | 1 => [("finish", 3)]
    | _ => []
  terminal := fun state => decide (state = 3) }

private def terminalEdge : S.Model Nat String := {
  linear with successors := fun
    | 0 => [("first", 1)]
    | 1 => [("second", 2)]
    | 2 => [("late", 3)]
    | _ => [] }

def run : IO Unit := do
  let costs : S.Costs := ⟨7, 2⟩
  let exact : S.Limits := ⟨3, 2, S.workEstimate costs 3 2⟩
  let checked ← load (S.check linear costs exact)
  ensure (checked.graph.size == 3 && checked.graph.keys.toList == [0, 1, 2])
    "Sparse discovery did not retain exactly the reachable keys."
  ensure (checked.graph.work == exact.work)
    "The sparse work estimate differs from the actual graph dimensions."
  reject (S.check linear costs { exact with states := 2 })
    "An exhausted state budget returned a partial graph."
  reject (S.check linear costs { exact with edges := 1 })
    "An exhausted edge budget omitted a real successor."
  reject (S.check linear costs { exact with work := exact.work - 1 })
    "An incomplete work budget certified the full graph."
  let hiddenLimits : S.Limits := ⟨4, 3, S.workEstimate costs 4 3⟩
  let hidden ← load (Netlib.Theory.FiniteSuccessorGraph.build hiddenDeadlock costs hiddenLimits)
  ensure (hidden.size == 4 && hidden.keys.toList == [0, 1, 2, 3])
    "The sparse graph omitted a reachable alternative."
  reject (S.checkLive hidden)
    "A successful selected path hid another reachable deadlock."
  reject (S.check hiddenDeadlock costs hiddenLimits)
    "The joint live-row check accepted a hidden deadlock."
  reject (S.check terminalEdge costs hiddenLimits)
    "A terminal state retained an unaccounted progress action."

end NetlibTest.FederatedCohortGraph
