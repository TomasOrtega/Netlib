import Netlib.Protocol.TCP.ReceiveStore

namespace NetlibTest.TCPReceiveStore

open Netlib.Protocol.TCP.ReceiveStore

private def ensure (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def load : Except Stop α → IO α
  | .ok value => pure value
  | .error reason => throw (IO.userError s!"Unexpected receive-store stop: {repr reason}.")

private def payload (start count : Nat) : List UInt8 :=
  (List.range count).map fun offset => UInt8.ofNat ((start + offset) % 251)

private def retainedSuffix : IO Unit := do
  let suffix := payload 31 400
  let firstBytes := payload 17 400
  let held ← load (accept (initial : State Nat) 400 suffix 100 1600 1600)
  ensure (held.receiptID == 0 && held.state.nextID == 1 && held.novel == 400 &&
      held.released.isEmpty && held.state.frontier == 0 && held.state.heldBytes == 400 &&
      held.state.physicalFree 1600 == 1200 && held.state.seenGap)
    "A future suffix must consume physical space without crossing the gap."
  let duplicate ← load (accept held.state 400 suffix 999 1600 1600)
  ensure (duplicate.receiptID == 1 && duplicate.state.nextID == 2 && duplicate.novel == 0 &&
      duplicate.duplicate && duplicate.released.isEmpty && duplicate.state.held == held.state.held)
    "An exact duplicate must retain the first metadata and source identity."
  let released ← load (accept duplicate.state 0 firstBytes 200 1600 1600)
  ensure (released.receiptID == 2 && released.novel == 400 && !released.duplicate &&
      released.state.frontier == 800 && released.state.held.isEmpty &&
      released.released.map (·.receipt) == [2, 0] && released.released.map (·.metadata) == [200, 100] &&
      bytes released.released == firstBytes ++ suffix && decide (released.state.Valid 1600 800))
    "One gap-filling receipt must release both actual source runs in sequence order."

private def severalGaps : IO Unit := do
  let last ← load (accept (initial : State Nat) 4 [5, 6] 30 8 8)
  let middle ← load (accept last.state 2 [3, 4] 20 8 8)
  let first ← load (accept middle.state 0 [1, 2] 10 8 8)
  ensure (first.released.map (·.position) == [0, 2, 4] &&
      first.released.map (·.receipt) == [2, 1, 0] && bytes first.released == [1, 2, 3, 4, 5, 6] &&
      first.state.frontier == 6 && first.state.held.isEmpty && decide (first.state.Valid 8 2))
    "A filled prefix must drain every adjacent held run without losing its source."
  let final ← load (accept first.state 6 [7, 8] 40 8 2)
  ensure (bytes final.released == [7, 8] && final.state.frontier == 8 &&
      decide (final.state.Valid 8 0))
    "An in-order receipt must use the same store interface after gap release."

private def stops : IO Unit := do
  let held ← load (accept (initial : State Nat) 4 [5, 6] 1 8 8)
  ensure ((accept held.state 4 [9, 6] 2 8 8).toOption.isNone)
    "Conflicting bytes at an existing span must stop."
  match accept held.state 4 [9, 6] 2 8 8 with
  | .error .conflict => pure ()
  | _ => throw (IO.userError "The exact conflicting span must report conflict.")
  match accept held.state 3 [4, 5] 2 8 8 with
  | .error .overlap => pure ()
  | _ => throw (IO.userError "A partial overlap must report its selected scope stop.")
  match accept held.state 7 [8, 9] 2 8 8 with
  | .error .right => pure ()
  | _ => throw (IO.userError "A span beyond the offered edge must stop before storage.")
  match accept held.state 0 [] 2 8 8 with
  | .error .empty => pure ()
  | _ => throw (IO.userError "An empty payload must not allocate a receive identity.")
  let first ← load (accept (initial : State Nat) 0 [1, 2] 1 8 8)
  match accept first.state 1 [2, 3] 2 8 6 with
  | .error .left => pure ()
  | _ => throw (IO.userError "An old/new prefix overlap must stop before trimming.")

def run : IO Unit := do
  retainedSuffix
  severalGaps
  stops
  IO.println "Bounded receive-store tests passed."

end NetlibTest.TCPReceiveStore
