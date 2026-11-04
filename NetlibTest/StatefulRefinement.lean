import Netlib.Check.StatefulRefinement

namespace NetlibTest.StatefulRefinement

open Netlib Netlib.Packet Netlib.Import.NftablesStateful Netlib.Check.StatefulRefinement
open StatefulACL (CTState)

private def snapshot (policy : Action) (rules : List SourceRule := []) : Snapshot := {
  version := "1.1.3", releaseName := "refinement test", table := "filter", chain := "forward"
  tableHandle := 1, chainHandle := 2, tableIndex := 1, chainIndex := 2
  hook := "forward", priority := 0, policy, rules }

private def rule (state : CTState) (test : Match := {}) (action : Action := .permit) : SourceRule := {
  source := test.source, destination := test.destination, protocol := test.protocol
  sourcePorts := test.sourcePorts, destinationPorts := test.destinationPorts
  states := some [state], action, objectIndex := 3, expressionIndices := [0]
  verdictIndex := 1, handle := 3, sourceID := "test rule", stateExpressionIndex := some 0 }

private def deny : Snapshot := snapshot .deny
private def permit : Snapshot := snapshot .permit
private def established : Snapshot := snapshot .deny [rule .established]
private def web : Match := { protocol := some Protocol.tcp, destinationPorts := some (.single 443) }
private def initial : Snapshot := snapshot .deny [rule .established, rule .new web]

example (state : CTState) : state ∈ states := state_mem state

example : check deny permit = true := by decide
example : check permit deny = false := by decide
example : cellCount deny permit = 5 := by decide
example : checkBudget deny permit 4 = .error "Stateful refinement exceeds the total state/header cell budget." := rfl
example : checkBudget deny permit 5 = .ok true := rfl
example : Meaning deny permit := (check_correct _ _).mp (by decide)

example (stronger weaker : Snapshot) (context : Context)
    (found : counterexample stronger weaker = some context) :
    stronger.permits context.state context.header = true ∧ weaker.permits context.state context.header = false :=
  counterexample_sound _ _ _ found

example (stronger weaker : Snapshot) :
    counterexample stronger weaker = none ↔ Meaning stronger weaker := counterexample_none_iff _ _

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

private def witness (stronger weaker : Snapshot) : IO Context := do
  let some context := counterexample stronger weaker
    | throw (IO.userError "A failed refinement must retain a concrete state/header context.")
  ensure (stronger.permits context.state context.header && !weaker.permits context.state context.header)
    "A refinement counterexample must permit only in the proposed stronger snapshot."
  return context

def run : IO Unit := do
  ensure (← unwrap (checkBudget established initial))
    "Removing NEW-flow admission must preserve static permission inclusion."
  ensure (!(← unwrap (checkBudget initial established)))
    "Restoring a NEW-flow exception must fail the reverse refinement."
  let contextExample ← witness initial established
  ensure (contextExample.state == .new && web.accepts contextExample.header)
    "The counterexample must retain the NEW class and matching service port."
  let webPacket : Header := ⟨167772161, 3325256706, Protocol.tcp, 50000, 443⟩
  ensure (established.permits .established webPacket)
    "Static strengthening does not revoke an already ESTABLISHED context."
  let additional := snapshot .deny [rule .established, rule .new web,
    rule .new { protocol := some Protocol.tcp, destinationPorts := some (.single 8443) }]
  ensure (!(← unwrap (checkBudget additional initial)))
    "A hidden alternate port must be checked across the complete header partition."
  let port ← witness additional initial
  ensure (port.state == .new && port.header.destinationPort == 8443)
    "The hidden-port counterexample must identify the exact differing port."
  for state in states do
    let selected := snapshot .deny [rule state]
    ensure (!(← unwrap (checkBudget selected deny)))
      "Every supported conntrack state must participate in the check."
    let context ← witness selected deny
    ensure (context.state == state) "The counterexample lost the differing conntrack state."
  ensure (!(← unwrap (checkBudget permit deny)))
    "An explicit native accept policy cannot silently become a deny default."
  ensure (← unwrap (checkBudget deny permit))
    "The empty deny chain must refine the empty accept chain."
  reject (checkBudget deny permit 4) "The total five-state cell budget must be checked before search."
  ensure (← unwrap (checkBudget deny permit 5)) "The exact five-cell budget must complete."
  reject (checkBudget { deny with hook := "postrouting" } permit)
    "Different hook roles cannot produce a refinement answer."
  reject (checkBudget { deny with priority := 200 } permit)
    "Different processing priorities cannot produce a refinement answer."
  let nativeInitial ← unwrap (Snapshot.parse (← IO.FS.readFile "examples/lifecycle/native/forward-initial.json"))
  let nativeEstablished ← unwrap (Snapshot.parse (← IO.FS.readFile "examples/lifecycle/native/forward-established-only.json"))
  ensure (← unwrap (checkBudget nativeEstablished nativeInitial))
    "The retained native ESTABLISHED-only update must statically refine its original chain."
  ensure (!(← unwrap (checkBudget nativeInitial nativeEstablished)))
    "The retained native reverse update must expose a NEW-flow counterexample."
  let nativeContext ← witness nativeInitial nativeEstablished
  ensure (nativeContext.state == .new && ([9000, 9001] : List Port).contains nativeContext.header.destinationPort &&
      nativeContext.header.protocol == Protocol.udp)
    "The native counterexample must identify an original NEW UDP permit."
  IO.println "Stateful refinement tests passed."

end NetlibTest.StatefulRefinement
