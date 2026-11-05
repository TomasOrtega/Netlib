import Netlib.Protocol.TCP.Endpoint
import Netlib.Protocol.TCP.ControlOutput

namespace NetlibTest.TCPRecoveryEndpoint

open Netlib Packet Protocol TCP

private def ensure (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def acknowledgment (state : Endpoint.State) (ack window : Nat) : IO EstablishedReceive.Input :=
  match ControlOutput.emit state.core.inbound state.core.receiveNext (Seq.ofNat ack) 16 window with
  | .ok input => pure input
  | .error reason => throw (IO.userError reason)

private def lastAckWindow : IO Unit := do
  let initial : Endpoint.State := {
    core := ⟨⟨3325256706, 3221225985, Packet.Protocol.tcp, 8080, 41000⟩,
      Seq.ofNat 200, 65535, [], Seq.ofNat 100, Seq.ofNat 100, []⟩
    pending := [], pendingLimit := 1600, sendWindow := 1000,
    sendWL1 := Seq.ofNat 200, sendWL2 := Seq.ofNat 100, effectiveMSS := 800, ipSendLimit := 1000 }
  let enabled := Endpoint.enableRecovery initial
  ensure (enabled.decision == .accepted .enableRecovery) "Recovery must start from empty outstanding storage."
  let written := Endpoint.write enabled.state [42]
  let sent := Endpoint.send written.state 1 true
  ensure (sent.decision == .accepted (.send 1)) "The regression needs one actual outstanding original send."
  let old ← acknowledgment sent.state 99 400
  let stale := Endpoint.receive sent.state old
  ensure (stale.decision == .accepted (.receive 0 0) && stale.state.sendWindow == 1000 &&
    stale.state.lastAckWindow == some 400)
    "An old ACK must retain SND.WND but update the last incoming ACK window."
  let packet ← acknowledgment stale.state 100 400
  let first := Endpoint.receive stale.state packet
  let second := Endpoint.receive first.state packet
  let third := Endpoint.receive second.state packet
  ensure (first.decision == .accepted (.receive 0 0) && second.decision == .accepted (.receive 0 0) &&
    third.decision == .recoveryUnsupported .fastRecovery)
    "The third qualifying duplicate must stop, even when an earlier ACK did not update SND.WND."

def run : IO Unit := do
  lastAckWindow
  IO.println "Checked TCP recovery endpoint tests passed."

end NetlibTest.TCPRecoveryEndpoint
