import Netlib.Check.CampusTCPTwoProgressReceive
import Netlib.Check.CampusTCPTwoProgressState
import Netlib.Check.CampusTCPTwoProgressSenderWindow

namespace Netlib.Check.CampusTCPTwoProgressReceive

open Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart (TwoWriteInitial)

variable {input : Input} {complete : TCPHandshake.Completed input.active input.passive}
variable {cut current : Cut input complete} {sender : Actor} {gateway : Gateway} {lower upper chunk : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {beforeStage afterStage : CampusTCPTwoProgressReceiver.Stage}
variable {index : Nat} {served : Served input} {emission : WireForwarding.Emission served.ticket.value.source.packet}
variable {emitted : served.evidence.output = some emission}

theorem Received.stream (received : Received initial current beforeStage afterStage chunk index served emission emitted) :
    beforeStage.bytes lower upper ++ chunk = afterStage.bytes lower upper := by
  have actual : received.delivery.localStep.result =
      Endpoint.receive (endpoint current.endpoints sender.other) emission.asInput := by
    simpa only [received.actor] using Delivery.local_result received.delivery
  have effects := (Endpoint.receive_effects (endpoint current.endpoints sender.other) emission.asInput).2.2.1
  rw [← actual, received.delivery.resultState, received.releasedBytes] at effects
  have after : CampusTCPTwoProgressReceiver.Facts initial received.delivery.after afterStage :=
    received.selected ▸ received.receiver
  rw [after.received, received.beforeFacts.received] at effects
  exact effects.symm

private theorem stage_prefix (lower upper : List UInt8) (stage : CampusTCPTwoProgressReceiver.Stage) :
    stage.bytes lower upper <+: lower ++ upper := by
  cases stage with
  | empty | upperHeld => exact List.nil_prefix
  | lowerReleased => exact List.prefix_append _ _
  | allReleased => exact List.prefix_refl _

def Received.joint (received : Received initial current beforeStage afterStage chunk index served emission emitted)
    (live : CampusTCPTwoProgressState.Live initial current sent timeouts beforeStage) :
    CampusTCPTwoProgressState.Live initial received.move.after sent timeouts afterStage := by
  have flight : CampusTCPTwoProgressSender.Flight initial (endpoint received.move.after.endpoints sender) sent timeouts := by
    rw [received.peer]
    exact live.senderFlight
  have stream : beforeStage.bytes lower upper ++ received.delivery.localStep.releasedPayload = afterStage.bytes lower upper := by
    rw [received.localRelease]
    exact received.stream
  have within : beforeStage.bytes lower upper ++ received.delivery.localStep.releasedPayload <+: lower ++ upper := by
    rw [stream]
    exact stage_prefix lower upper afterStage
  have history := live.history.release received.delivery.localStep received.selectedSteps within received.localRead
  exact ⟨⟨CampusTCPTwoProgressState.endpoint_guards flight received.receiver,
    live.anchor.retained.trans received.move.retained, live.anchor.environment.trans received.environment⟩,
    flight, received.receiver, live.gatewayState.reframe (received.gateway gateway), live.gatewayWindow, stream ▸ history⟩

theorem Received.sender_reserved
    (received : Received initial current beforeStage afterStage chunk index served emission emitted)
    (space : CampusTCPTwoProgressSenderWindow.Reserved initial (endpoint current.endpoints sender) sent) :
    CampusTCPTwoProgressSenderWindow.Reserved initial (endpoint received.move.after.endpoints sender) sent := by
  rw [received.peer]
  exact space

end Netlib.Check.CampusTCPTwoProgressReceive
