import Netlib.Check.CampusTCPGapProgressEvidence

/-!
# Held-gap phase evidence across actual clock steps

The monitor and stored packet identities stay fixed.
The current guards supply the ACK time bounds at the new cut.
-/

namespace Netlib.Check.CampusTCPGapProgressEvidence

open Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPRecoveryRoundPhaseBase (At)
open CampusTCPGapProgressPhaseBase (Anchor)
open CampusTCPGapProgressStart (GapInitial NativeEnv)

variable {input : Input} {complete : H.Completed input.active input.passive}
  {cut before current : Cut input complete} {sender : Actor} {lower upper : List UInt8}
  {initial : GapInitial cut sender lower upper}
  {native : NativeEnv cut initial.gateway.seed.entry} {allowance retries : Nat}
  {monitor : CampusTCPGapProgressMonitor.Monitor} {released : Bool} {phase : CampusTCPRoundMonitor.Phase}

private theorem time_ready (placement : At before current) (anchor : Anchor cut current) (actor : Actor) :
    Endpoint.AckTimeReady (endpoint before.endpoints actor) (endpoint current.endpoints actor).now := by
  intro reaction stored
  have runtime : (endpoint current.endpoints actor).ackReaction = some reaction :=
    (placement.frame.endpointFrame actor).ackReaction.trans stored
  have prepared := (anchor.guards actor).prepared.2
  rw [runtime] at prepared
  exact prepared.1

private theorem history_first
    (history : CampusTCPGapProgressHistory.History cut before sender.other (lower ++ upper) released)
    (placement : At before current) : (history.clock placement).streams.first = history.streams.first := rfl

private theorem complete_first
    (history : CampusTCPGapProgressHistory.Complete cut before sender.other (lower ++ upper) reader)
    (placement : At before current) : (history.clock placement).streams.first = history.streams.first := rfl

def Active.clock (record : Active initial allowance before monitor retries released phase)
    (placement : At before current) (anchor : Anchor cut current) :
    Active initial allowance current monitor retries released phase where
  live := record.live.clock placement (time_ready placement anchor sender.other)
  phaseEq := record.phaseEq
  waiting := record.waiting
  retryCount := record.retryCount
  dropCount := record.dropCount
  bound := record.bound
  drops := record.drops.clock placement
  first := record.first.map (fun receipt => receipt.clock placement)
  firstRef := by
    simpa only [Option.map_map, Function.comp_def, FirstReceipt.clock, FirstReceipt.reframe] using record.firstRef
  firstOperation := by
    change (record.live.history.clock placement).streams.first = _
    rw [history_first]
    simpa only [Option.map_map, Function.comp_def, FirstReceipt.clock, FirstReceipt.reframe] using record.firstOperation

def DataOutput.clock (output : DataOutput initial before) (placement : At before current) : DataOutput initial current where
  index := output.index
  produced := output.produced
  stored := by rw [placement.frame.outputs]; exact output.stored
  actor := output.actor
  application := output.application
  fields := output.fields

def AckOutput.clock (output : AckOutput initial before) (placement : At before current) : AckOutput initial current where
  index := output.index
  produced := output.produced
  stored := by rw [placement.frame.outputs]; exact output.stored
  actor := output.actor
  application := output.application
  fields := output.fields

def DataIngress.clock (record : DataIngress initial allowance before monitor retries released)
    (placement : At before current) (anchor : Anchor cut current) :
    DataIngress initial allowance current monitor retries released where
  toActive := record.toActive.clock placement anchor
  output := record.output.clock placement
  packetID := record.packetID
  custody := by rw [placement.frame.custody]; exact record.custody
  outputRef := record.outputRef
  packetRef := record.packetRef

def DataTicket.clock (record : DataTicket initial native allowance before monitor retries released)
    (placement : At before current) (anchor : Anchor cut current) :
    DataTicket initial native allowance current monitor retries released where
  toActive := record.toActive.clock placement anchor
  output := record.output.clock placement
  ticket := record.ticket
  pending := by rw [placement.frame.work]; exact record.pending
  outputIndex := record.outputIndex
  produced := record.produced
  standby := record.standby
  ingress := record.ingress
  outputRef := record.outputRef
  ticketRef := record.ticketRef

def DataLink.clock (record : DataLink initial allowance before monitor retries released)
    (placement : At before current) (anchor : Anchor cut current) :
    DataLink initial allowance current monitor retries released where
  toActive := record.toActive.clock placement anchor
  index := record.index
  served := record.served
  stored := by rw [placement.frame.services]; exact record.stored
  emission := record.emission
  emitted := record.emitted
  actor := record.actor
  application := record.application
  fields := record.fields
  packetID := record.packetID
  custody := by rw [placement.frame.custody]; exact record.custody
  serviceRef := record.serviceRef
  packetRef := record.packetRef

def NeedAck.clock (record : NeedAck initial allowance before monitor retries)
    (placement : At before current) (anchor : Anchor cut current) : NeedAck initial allowance current monitor retries where
  toActive := record.toActive.clock placement anchor
  pending := record.pending

def AckIngress.clock (record : AckIngress initial allowance before monitor retries)
    (placement : At before current) (anchor : Anchor cut current) : AckIngress initial allowance current monitor retries where
  toActive := record.toActive.clock placement anchor
  output := record.output.clock placement
  packetID := record.packetID
  custody := by rw [placement.frame.custody]; exact record.custody
  outputRef := record.outputRef
  packetRef := record.packetRef

def AckTicket.clock (record : AckTicket initial native allowance before monitor retries)
    (placement : At before current) (anchor : Anchor cut current) : AckTicket initial native allowance current monitor retries where
  toActive := record.toActive.clock placement anchor
  output := record.output.clock placement
  ticket := record.ticket
  pending := by rw [placement.frame.work]; exact record.pending
  outputIndex := record.outputIndex
  produced := record.produced
  standby := record.standby
  ingress := record.ingress
  outputRef := record.outputRef
  ticketRef := record.ticketRef

def AckLink.clock (record : AckLink initial allowance before monitor retries)
    (placement : At before current) (anchor : Anchor cut current) : AckLink initial allowance current monitor retries where
  toActive := record.toActive.clock placement anchor
  index := record.index
  served := record.served
  stored := by rw [placement.frame.services]; exact record.stored
  emission := record.emission
  emitted := record.emitted
  actor := record.actor
  application := record.application
  fields := record.fields
  target := record.target
  packetID := record.packetID
  custody := by rw [placement.frame.custody]; exact record.custody
  serviceRef := record.serviceRef
  packetRef := record.packetRef

def Waiting.clock (record : Waiting initial allowance before monitor retries released)
    (placement : At before current) (anchor : Anchor cut current) : Waiting initial allowance current monitor retries released where
  live := record.live.clock placement (time_ready placement anchor sender.other)
  waiting := record.waiting
  retryCount := record.retryCount
  dropCount := record.dropCount
  bound := record.bound
  drops := record.drops.clock placement
  dropStep := record.dropStep
  member := placement.member record.member
  dropPacket := record.dropPacket
  lastDrop := record.lastDrop
  facts := record.facts
  absent := by
    intro item member
    rw [placement.frame.custody] at member
    exact record.absent item member
  first := record.first.map (fun receipt => receipt.clock placement)
  firstRef := by
    simpa only [Option.map_map, Function.comp_def, FirstReceipt.clock, FirstReceipt.reframe] using record.firstRef
  firstOperation := by
    change (record.live.history.clock placement).streams.first = _
    rw [history_first]
    simpa only [Option.map_map, Function.comp_def, FirstReceipt.clock, FirstReceipt.reframe] using record.firstOperation

def NeedRead.clock (record : NeedRead initial allowance before monitor retries)
    (placement : At before current) (anchor : Anchor cut current) : NeedRead initial allowance current monitor retries where
  retired := record.retired.clock placement (time_ready placement anchor sender) (time_ready placement anchor sender.other)
  phaseEq := record.phaseEq
  waiting := record.waiting
  retryCount := record.retryCount
  dropCount := record.dropCount
  bound := record.bound
  drops := record.drops.clock placement
  first := record.first.map (fun receipt => receipt.clock placement)
  firstRef := by
    simpa only [Option.map_map, Function.comp_def, FirstReceipt.clock, FirstReceipt.reframe] using record.firstRef
  firstOperation := by
    change (record.retired.history.clock placement).streams.first = _
    rw [history_first]
    simpa only [Option.map_map, Function.comp_def, FirstReceipt.clock, FirstReceipt.reframe] using record.firstOperation

def Done.clock (record : Done initial allowance before monitor retries)
    (placement : At before current) (anchor : Anchor cut current) : Done initial allowance current monitor retries where
  completed := record.completed.clock placement (time_ready placement anchor sender) (time_ready placement anchor sender.other)
  phaseEq := record.phaseEq
  waiting := record.waiting
  retryCount := record.retryCount
  dropCount := record.dropCount
  bound := record.bound
  drops := record.drops.clock placement
  first := record.first.map (fun receipt => receipt.clock placement)
  firstRef := by
    simpa only [Option.map_map, Function.comp_def, FirstReceipt.clock, FirstReceipt.reframe] using record.firstRef
  firstOperation := by
    change (record.completed.history.clock placement).streams.first = _
    rw [complete_first]
    simpa only [Option.map_map, Function.comp_def, FirstReceipt.clock, FirstReceipt.reframe] using record.firstOperation

def Evidence.clock (evidence : Evidence initial native allowance before monitor)
    (placement : At before current) (anchor : Anchor cut current) : Evidence initial native allowance current monitor :=
  match evidence with
  | .dataIngress record => .dataIngress (record.clock placement anchor)
  | .dataTicket record => .dataTicket (record.clock placement anchor)
  | .dataLink record => .dataLink (record.clock placement anchor)
  | .needAck record => .needAck (record.clock placement anchor)
  | .ackIngress record => .ackIngress (record.clock placement anchor)
  | .ackTicket record => .ackTicket (record.clock placement anchor)
  | .ackLink record => .ackLink (record.clock placement anchor)
  | .waiting record => .waiting (record.clock placement anchor)
  | .needRead record => .needRead (record.clock placement anchor)
  | .done record => .done (record.clock placement anchor)

end Netlib.Check.CampusTCPGapProgressEvidence
