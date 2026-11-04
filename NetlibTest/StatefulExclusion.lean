import Netlib.Check.StatefulExclusion

namespace NetlibTest.StatefulExclusion

open Netlib Netlib.Packet Netlib.Import.NftablesStateful Netlib.Check.StatefulExclusion
open StatefulACL (CTState)

private def snapshot (policy : Action) (rules : List SourceRule := []) : Snapshot := {
  version := "1.1.3", releaseName := "late barrier test", table := "filter", chain := "late"
  tableHandle := 1, chainHandle := 2, tableIndex := 1, chainIndex := 2
  hook := "postrouting", priority := 200, policy, rules }

private def rule (test : Match) (states : Option (List CTState)) (action : Action) : SourceRule := {
  source := test.source, destination := test.destination, protocol := test.protocol
  sourcePorts := test.sourcePorts, destinationPorts := test.destinationPorts
  states, action, objectIndex := 3, expressionIndices := [0], verdictIndex := 1
  handle := 3, sourceID := "barrier rule", stateExpressionIndex := none }

private def forbidden : Match := {
  source := some ⟨3405803777, 32⟩, destination := some ⟨3325256706, 32⟩
  protocol := some Protocol.udp, destinationPorts := some (.single 9000) }

private def wire : Header := ⟨3405803777, 3325256706, Protocol.udp, 40000, 9000⟩
private def deny : Snapshot := snapshot .deny
private def permit : Snapshot := snapshot .permit
private def guard : SourceRule := rule forbidden none .deny
private def established : SourceRule := rule {} (some [.established]) .permit
private def guarded : Snapshot := snapshot .permit [guard, established]
private def bypassed : Snapshot := snapshot .permit [established, guard]

example : cellCount deny {} = 5 := by decide
example : check deny {} = true := by decide
example : check permit {} = false := by decide
example : Blocks deny {} := blocks_of_checkBudget deny {} 5 rfl
example : nativeContext { deny with priority := 101 } = true := by decide
example : nativeContext { deny with priority := 100 } = false := by decide
example : nativeContext { deny with priority := 2147483647 } = false := by decide

example (source : Snapshot) (selection : Match) (context : Context)
    (found : counterexample source selection = some context) :
    selection.Holds context.header ∧ source.evaluate context.state context.header = .permit :=
  counterexample_sound _ _ _ found

example (source : Snapshot) (selection : Match) :
    counterexample source selection = none ↔ Blocks source selection := counterexample_none_iff _ _

private def ensure (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def unwrap (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error message => throw (IO.userError message)

private def reject (result : Except String α) (message : String) : IO Unit :=
  match result with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError message)

private def witness (source : Snapshot) (selection : Match) : IO Context := do
  let some context := counterexample source selection
    | throw (IO.userError "A failed barrier must retain a concrete forbidden context.")
  ensure (selection.accepts context.header && source.permits context.state context.header)
    "A counterexample must belong to the forbidden class and be permitted."
  return context

def run : IO Unit := do
  ensure (← unwrap (checkBudget deny forbidden)) "A deny default must block the complete selected class."
  ensure (!(← unwrap (checkBudget permit forbidden)))
    "An accept default must expose the selected class even without a matching permit rule."
  let openContext ← witness permit forbidden
  ensure (openContext.header.source == wire.source && openContext.header.destination == wire.destination &&
      openContext.header.destinationPort == wire.destinationPort && openContext.header.protocol == Protocol.udp)
    "Selection cut points must retain exact public/backend endpoints and ports."
  ensure (← unwrap (checkBudget guarded forbidden))
    "An earlier unconditional forbidden-class guard must also block cached ESTABLISHED traffic."
  ensure (!(← unwrap (checkBudget bypassed forbidden)))
    "A later guard cannot override an earlier ESTABLISHED permit."
  let cached ← witness bypassed forbidden
  ensure (cached.state == .established && bypassed.permits .established wire)
    "The cached-flow bypass must identify the ESTABLISHED state."
  let ssh : Match := { protocol := some Protocol.tcp, destinationPorts := some (.single 22) }
  let irrelevant := snapshot .deny [rule ssh none .permit]
  ensure (← unwrap (checkBudget irrelevant forbidden))
    "An unrelated SSH permit must not invalidate the UDP output barrier."
  let privateGuard := snapshot .permit [rule { source := some ⟨167772160, 24⟩ } none .deny]
  ensure (!(← unwrap (checkBudget privateGuard forbidden)))
    "A pre-translation private source guard does not block the selected public output class."
  let _ ← witness privateGuard forbidden
  for state in states do
    let selected := snapshot .deny [rule forbidden (some [state]) .permit]
    ensure (!(← unwrap (checkBudget selected forbidden)))
      "Every supported state must participate in exclusion checks."
    let context ← witness selected forbidden
    ensure (context.state == state) "The counterexample must retain the only permitted state."
  let emptyStates := snapshot .permit [rule forbidden (some []) .deny]
  ensure (!(← unwrap (checkBudget emptyStates forbidden)))
    "An empty state selector cannot establish a barrier."
  let emptyClass : Match := { destinationPorts := some ⟨9001, 9000⟩ }
  ensure (← unwrap (checkBudget permit emptyClass)) "An empty forbidden class is vacuously excluded."
  ensure ((counterexample permit emptyClass).isNone) "An empty class cannot have a counterexample."
  ensure (← unwrap (checkBudget deny {} 5)) "The exact aggregate five-state budget must complete."
  reject (checkBudget deny {} 4) "Budget exhaustion must not return a partial exclusion answer."
  let cells := cellCount guarded forbidden
  ensure (← unwrap (checkBudget guarded forbidden cells)) "The exact selection-cell budget must complete."
  reject (checkBudget guarded forbidden (cells - 1)) "Selection cuts must count toward the total budget."
  for priority in [-1, 0, 100, 2147483647, 2147483648] do
    reject (checkBudget { guarded with priority } forbidden)
      "A barrier must follow SNAT and precede confirmation with a strict priority bound."
  reject (checkBudget { guarded with hook := "forward" } forbidden)
    "A FORWARD hook cannot certify the late postrouting barrier interface."
  ensure (check { guarded with hook := "forward" } forbidden)
    "The plain semantic check must remain independent of native hook placement."
  IO.println "Stateful exclusion tests passed."

end NetlibTest.StatefulExclusion
