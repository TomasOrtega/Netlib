import Netlib.Protocol.TCP.RecoveryReceipt

namespace NetlibTest.TCPRecoveryReceipt

open Netlib.Protocol.TCP

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def load : Except Recovery.Stop α → IO α
  | .error reason => throw (IO.userError s!"The receipt-time operation failed: {repr reason}.")
  | .ok value => pure value

private def delayedProcessing : IO Unit := do
  let first := Recovery.sent (Recovery.initial 800) 400
  let second := Recovery.sent first 400
  let processing ← load (Recovery.advance second 1000)
  let sampled ← load (Recovery.acknowledgeAt processing 400 400)
  ensure (sampled.now == 1000 && sampled.lastSample.map (·.acknowledgedAt) == some 400 &&
      sampled.lastSample.map (·.elapsed) == some 400)
    "A held ACK must retain its receipt clock for the RTT measurement."
  ensure (Recovery.flight sampled == 400 && sampled.deadline == some (1000 + sampled.rto))
    "A remaining range must restart its timer at the current processing clock."
  let complete ← load (Recovery.acknowledgeAt processing 800 400)
  ensure (Recovery.flight complete == 0 && complete.deadline.isNone && complete.now == 1000)
    "A complete ACK must stop its timer without moving the local clock backward."
  ensure (match Recovery.acknowledgeAt processing 400 1001 with | .error .ledger => true | _ => false)
    "A future receipt time must be rejected."
  let later ← load (Recovery.advance (Recovery.initial 800) 500)
  let sentLater := Recovery.sent later 400
  let processingLater ← load (Recovery.advance sentLater 1000)
  ensure (match Recovery.acknowledgeAt processingLater 400 400 with | .error .ledger => true | _ => false)
    "A sampled ACK cannot arrive before its actual original send."
  ensure (match Recovery.acknowledgeAt processingLater 200 400 with | .error .ledger => true | _ => false)
    "A partial ACK cannot arrive before the data that it retires."

private def retryExclusion : IO Unit := do
  let sent := Recovery.sent (Recovery.initial 800) 400
  let due ← load (Recovery.advance sent 1000)
  let (_, retried) ← load (Recovery.timeout due)
  let processing ← load (Recovery.advance retried 1500)
  let after ← load (Recovery.acknowledgeAt processing 400 1200)
  ensure (after.lastSample.isNone && after.estimator.isNone && after.rto == 2000 && after.now == 1500)
    "Deferred processing must retain Karn exclusion for an actual retried range."

def run : IO Unit := do
  delayedProcessing
  retryExclusion
  IO.println "TCP deferred ACK receipt tests passed."

end NetlibTest.TCPRecoveryReceipt
