import Netlib.Check.TCPHandshake

namespace NetlibTest.TCPHandshakeCheck

open Netlib Protocol TCP
open Netlib.Check.TCPHandshake

private def ensure (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def load : Except String α → IO α
  | .ok value => pure value
  | .error reason => throw (IO.userError reason)

def run : IO Unit := do
  let input ← load (Input.parse (← IO.FS.readFile "examples/tcp-handshake/trace.json"))
  let report ← load input.check
  ensure (report.supported && report.final.exchangeComplete && report.steps.length == 4 && report.remaining.isEmpty)
    "The guide must construct an actual ordered startup exchange."
  match report.final with
  | .complete value =>
    let active := value.certificate.activeSeed
    let passive := value.certificate.passiveSeed
    ensure (active.core.sendNext.val == 1001 && active.core.receiveNext.val == 5001 &&
        passive.core.sendNext.val == 5001 && passive.core.receiveNext.val == 1001 &&
        active.sendWindow == 6 && passive.sendWindow == 8 && active.sendWL1.val == 5000 &&
        active.effectiveMSS == 536 && passive.effectiveMSS == 536)
      "Startup must derive cursors, windows, history, and default MSS from the selected source events."
  | _ => throw (IO.userError "The completed history is missing.")
  let lost := { input with events := input.events.take 3 }
  let waiting ← load lost.check
  ensure (waiting.supported && !waiting.final.exchangeComplete && waiting.final.activeSeed.isSome &&
      waiting.final.passiveSeed.isNone)
    "A lost final ACK must leave the active seed available and the passive seed absent."
  let wrongPhase := { input with events := [.synReceivedAck [] .direct, .activeOpen input.passive.socket true] }
  let stopped ← load wrongPhase.check
  ensure (!stopped.supported && stopped.steps.length == 1 && stopped.remaining.length == 1 &&
      stopped.final.activeSeed.isNone && stopped.final.passiveSeed.isNone)
    "A phase limit must stop before transport decoding and the next output event."
  let header := Handshake.outbound input.active input.passive.socket
  for (flags, window) in [(1, 8), (2, 65536)] do
    match ControlOutput.emit header input.active.iss (Seq.ofNat 0) flags window with
    | .error _ => pure ()
    | .ok _ => throw (IO.userError "Invalid control fields must not produce output bytes.")
  match ControlOutput.emit { header with protocol := Packet.Protocol.udp } input.active.iss (Seq.ofNat 0) 2 8 with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "A non-TCP tuple must not produce a TCP control packet.")
  IO.println "TCP startup replay tests passed."

end NetlibTest.TCPHandshakeCheck
