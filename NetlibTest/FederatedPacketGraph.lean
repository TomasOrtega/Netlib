import Netlib.Check.FederatedPacketGraph
import NetlibTest.FederatedPacketFixture

namespace NetlibTest.FederatedPacketGraph

open Netlib Federation InFlight
namespace Rank
export Theory.FiniteProgressRank (Limits Table Edge check)
end Rank

private def loadValue : Except String α → IO α
  | .ok value => pure value
  | .error reason => throw (IO.userError reason)

private def ensure (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

def limits (context : Context input) : Rank.Limits :=
  let states := Graph.universeSize input
  ⟨states, states * ((Control.nodes input).length + 5), context.profile.work⟩

private def replayMoves (context : Context input) (header : Packet.Header) :
    Nat → Key input → List Action → Except Nat (Key input)
  | _, key, [] => .ok key
  | index, key, action :: rest => match action.move? with
    | none => replayMoves context header (index + 1) key rest
    | some move => match Control.step context header key move with
      | none => .error index
      | some after => replayMoves context header (index + 1) after rest

private def expectBlocked (context : Context input) (base : FederatedPacketFixture.Base) (index : Nat) : IO Unit := do
  match replayMoves context base.header 0 (initialKey context) base.actions with
  | .error actual => ensure (actual == index) "The recorded packet actions blocked at the wrong operation."
  | .ok _ => throw (IO.userError "The recorded in-flight update unexpectedly passed its receiver guard.")

private def assertRankFailure (result : Except String α) : IO Unit :=
  match result with
  | .error reason => ensure (reason.contains "dead end") "A semantic rank negative failed before rank validation."
  | .ok _ => throw (IO.userError "A pending dead end or cycle unexpectedly received a rank certificate.")

private def verifyCells (base : FederatedPacketFixture.Base) (context : Context base.input)
    (fails : Packet.Header → Bool) (exactPositive : Bool := false) : IO Unit := do
  let resourceLimits := limits context
  let headers := JointPartition.selectedHeaders base.input context.first
  let mut cost := 0
  for header in headers do
    let graph ← loadValue (Graph.build context header resourceLimits)
    cost := cost + Graph.generationWork context + graph.rankWork
    match graph.analyze resourceLimits with
    | .error reason =>
      ensure (fails header && reason.contains "dead end")
        s!"Unexpected graph rejection at source port {header.sourcePort.val}: {reason}"
    | .ok checked =>
      ensure (!fails header) s!"A bad packet graph certified at source port {header.sourcePort.val}."
      ensure (checked.rank graph.table.initial > 0 && checked.states.length ≤ graph.size)
        "The pending initial state must have positive computed rank."
      if exactPositive then
        ensure (graph.size == 225 && Graph.R.edgeCount graph.table == 518 &&
            checked.states.length == 156 && checked.rank graph.table.initial == 19 &&
            Graph.generationWork context == 67773483 && graph.rankWork == 38000544)
          "The positive graph's actual finite inventory, reachability, or rank changed."
      for member : state in checked.states do
        have reached : state ∈ Theory.FiniteProgressRank.reachable graph.table := by
          rw [← checked.statesComputed]
          exact member
        let _ := checked.zero_iff state reached
        for present : edge in graph.table.row state do
          let _ := graph.edge_step state edge present
          let _ := checked.progress state reached edge present
          pure ()
  ensure (cost ≤ context.profile.work) "The aggregate actual generation and rank work exceeds the original profile budget."
  if exactPositive then ensure (cost == 317322081) "The positive three-cell actual work estimate changed."

private def verifyVariant (json : Lean.Json) (fails : Packet.Header → Bool) (blocked : Nat) : IO Unit := do
  let base ← loadValue (FederatedPacketFixture.fromJson json)
  let deployment ← loadValue (Deployment.certify base.input)
  let selection ← loadValue (Context.select deployment base.profile)
  verifyCells base selection.context fails
  expectBlocked selection.context base blocked

private def doneTable : Rank.Table Nat 1 :=
  ⟨0, Vector.ofFn (fun _ => []), Vector.ofFn (fun _ => true)⟩

private def deadTable : Rank.Table Nat 1 :=
  ⟨0, Vector.ofFn (fun _ => []), Vector.ofFn (fun _ => false)⟩

private def cycleTable : Rank.Table Nat 2 :=
  ⟨0, Vector.ofFn (fun state => if state.val = 0 then [⟨0, 1⟩] else [⟨0, 0⟩]),
    Vector.ofFn (fun _ => false)⟩

private def hiddenBranch : Rank.Table Nat 3 :=
  ⟨0, Vector.ofFn (fun state => if state.val = 0 then [⟨0, 1⟩, ⟨1, 2⟩] else []),
    Vector.ofFn (fun state => decide (state.val = 1))⟩

private def verifyGeneric : IO Unit := do
  let resourceLimits : Rank.Limits := ⟨3, 6, 1000000000⟩
  let checked ← loadValue (Rank.check doneTable resourceLimits)
  ensure (checked.rank doneTable.initial == 0) "An actual completed state must certify with rank zero."
  assertRankFailure (Rank.check deadTable resourceLimits)
  assertRankFailure (Rank.check cycleTable resourceLimits)
  assertRankFailure (Rank.check hiddenBranch resourceLimits)

private def rejects (result : Except String α) (word : String) : IO Unit :=
  match result with
  | .error reason => ensure (reason.contains word) "An exhausted graph budget reported the wrong failure."
  | .ok _ => throw (IO.userError "An exhausted graph budget unexpectedly certified.")

def run : IO Unit := do
  let fixture ← FederatedPacketFixture.build
  let context := fixture.context
  let base := fixture.base
  ensure (((JointPartition.partition base.input context.first).representative base.header).sourcePort.val == 50001)
    "The actual packet at source port 52000 must use the common representative 50001."
  verifyCells base context (fun _ => false) true
  let after ← match replayMoves context base.header 0 (initialKey context) base.actions with
    | .ok after => pure after
    | .error index => throw (IO.userError s!"The positive control replay blocked at operation {index}.")
  ensure (finished after) "The real action sequence must complete the packet and both update plans."
  let graph ← loadValue (Graph.build context base.header (limits context))
  rejects (Graph.build context base.header { limits context with work := 0 }) "generation"
  rejects (Graph.build context base.header { limits context with states := 0 }) "states"
  rejects (graph.analyze { limits context with work := 0 }) "work"
  rejects (graph.analyze { limits context with edges := 0 }) "successors"
  let json ← FederatedPacketFixture.raw
  verifyVariant (← loadValue (FederatedPacketFixture.removedReceiver json)) (fun _ => false) 3
  verifyVariant (← loadValue (FederatedPacketFixture.projectionJump json)) (fun _ => false) 3
  verifyVariant (← loadValue (FederatedPacketFixture.strandedHeader json)) (fun header => header.sourcePort == 52000) 5
  verifyVariant (← loadValue (FederatedPacketFixture.drainingCycle json)) (fun _ => true) 5
  verifyGeneric
  IO.println "Packet graphs: three complete ranks, retained old flights, semantic dead ends/cycles, and strict resource failures."

end NetlibTest.FederatedPacketGraph
