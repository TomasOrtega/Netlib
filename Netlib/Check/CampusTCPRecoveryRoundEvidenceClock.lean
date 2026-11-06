import Netlib.Check.CampusTCPRecoveryRoundEvidence

/-!
# Recovery phase evidence across actual clock slots

The monitor and packet identities stay fixed.
Endpoint state uses the new recovery clocks at the current cut.
-/

namespace Netlib.Check.CampusTCPRecoveryRoundEvidence

noncomputable section

open Protocol.TCP CampusTCPModel CampusTCPEnabled CampusTCPRoundStart
open CampusTCPRound (Cut)
open CampusTCPRecoveryRoundPhaseBase (At Anchor)

variable {input : Input} {events : List Event} {report : Report input events}
  {complete : H.Completed input.active input.passive} {request : Request input}
  {initial : Initial report complete request} {native : NativeEnv initial} {quantum : Nat}
  {before current : Cut input complete} {monitor : CampusTCPRecoveryRoundMonitor.Monitor}
  {sentAt retries : Nat} {released : Bool} {phase : CampusTCPRoundMonitor.Phase}

private theorem streams_cast_first (same : left = right)
    (history : CampusTCPRecoveryRoundHistory.Streams bytes right released) :
    (Eq.mpr (congrArg (fun operations => CampusTCPRecoveryRoundHistory.Streams bytes operations released) same) history).first =
      history.first := by
  cases same
  rfl

private theorem read_streams_cast_first (same : left = right)
    (history : CampusTCPRecoveryRoundHistory.ReadStreams bytes right reader) :
    (Eq.mpr (congrArg (fun operations => CampusTCPRecoveryRoundHistory.ReadStreams bytes operations reader) same) history).first =
      history.first := by
  cases same
  rfl

private theorem history_first (history : CampusTCPRecoveryRoundHistory.History initial before released)
    (placement : At before current) : (history.clock placement).first = history.first := by
  let extra := Classical.choose (CampusTCPRecoveryRoundHistory.At.application_history placement .server)
  have actual := Classical.choose_spec (CampusTCPRecoveryRoundHistory.At.application_history placement .server)
  change (Eq.mpr (congrArg (fun operations => CampusTCPRecoveryRoundHistory.Streams request.bytes operations released) actual.1)
    (history.clocks_append extra actual.2)).first = history.first
  rw [streams_cast_first actual.1]
  rfl

private theorem complete_first (history : CampusTCPRecoveryRoundHistory.Complete initial before reader)
    (placement : At before current) : (history.clock placement).first = history.first := by
  let extra := Classical.choose (CampusTCPRecoveryRoundHistory.At.application_history placement .server)
  have actual := Classical.choose_spec (CampusTCPRecoveryRoundHistory.At.application_history placement .server)
  change (Eq.mpr (congrArg (fun operations => CampusTCPRecoveryRoundHistory.ReadStreams request.bytes operations reader) actual.1)
    (history.clocks_append extra actual.2)).first = history.first
  rw [read_streams_cast_first actual.1]
  rfl

def Active.clock (record : Active initial before monitor sentAt retries released phase)
    (placement : At before current) (anchor : Anchor initial current) :
    Active initial current monitor sentAt retries released phase where
  live := record.live.frame placement anchor
  phaseEq := record.phaseEq
  waiting := record.waiting
  retryCount := record.retryCount
  dropCount := record.dropCount
  drops := record.drops.clock placement
  first := record.first.map (fun receipt => receipt.clock placement)
  firstRef := by
    simpa only [Option.map_map, Function.comp_def, FirstReceipt.clock, FirstReceipt.reframe] using record.firstRef
  firstOperation := by
    change (record.live.history.clock placement).first = _
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

def DataIngress.clock (record : DataIngress initial before monitor sentAt retries released)
    (placement : At before current) (anchor : Anchor initial current) :
    DataIngress initial current monitor sentAt retries released where
  toActive := record.toActive.clock placement anchor
  output := record.output.clock placement
  packetID := record.packetID
  custody := by rw [placement.frame.custody]; exact record.custody
  outputRef := record.outputRef
  packetRef := record.packetRef

def DataTicket.clock (record : DataTicket initial native before monitor sentAt retries released)
    (placement : At before current) (anchor : Anchor initial current) :
    DataTicket initial native current monitor sentAt retries released where
  toActive := record.toActive.clock placement anchor
  output := record.output.clock placement
  ticket := record.ticket
  pending := by rw [placement.frame.work]; exact record.pending
  outputIndex := record.outputIndex
  produced := record.produced
  primary := record.primary
  ingress := record.ingress
  outputRef := record.outputRef
  ticketRef := record.ticketRef

def DataLink.clock (record : DataLink initial before monitor sentAt retries released)
    (placement : At before current) (anchor : Anchor initial current) :
    DataLink initial current monitor sentAt retries released where
  toActive := record.toActive.clock placement anchor
  index := record.index
  served := record.served
  stored := by rw [placement.frame.services]; exact record.stored
  emission := record.emission
  emitted := record.emitted
  application := record.application
  fields := record.fields
  observed := record.observed.frame (congrArg CampusTCPService.Before.admission (placement.frame.beforeService .primary).symm)
  packetID := record.packetID
  custody := by rw [placement.frame.custody]; exact record.custody
  serviceRef := record.serviceRef
  packetRef := record.packetRef

def NeedAck.clock (record : NeedAck initial before monitor sentAt retries)
    (placement : At before current) (anchor : Anchor initial current) : NeedAck initial current monitor sentAt retries where
  toActive := record.toActive.clock placement anchor
  pending := record.pending

def AckIngress.clock (record : AckIngress initial before monitor sentAt retries)
    (placement : At before current) (anchor : Anchor initial current) : AckIngress initial current monitor sentAt retries where
  toActive := record.toActive.clock placement anchor
  output := record.output.clock placement
  packetID := record.packetID
  custody := by rw [placement.frame.custody]; exact record.custody
  outputRef := record.outputRef
  packetRef := record.packetRef

def AckTicket.clock (record : AckTicket initial native before monitor sentAt retries)
    (placement : At before current) (anchor : Anchor initial current) : AckTicket initial native current monitor sentAt retries where
  toActive := record.toActive.clock placement anchor
  output := record.output.clock placement
  ticket := record.ticket
  pending := by rw [placement.frame.work]; exact record.pending
  outputIndex := record.outputIndex
  produced := record.produced
  primary := record.primary
  ingress := record.ingress
  outputRef := record.outputRef
  ticketRef := record.ticketRef

def AckLink.clock (record : AckLink initial before monitor sentAt retries)
    (placement : At before current) (anchor : Anchor initial current) : AckLink initial current monitor sentAt retries where
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

def Waiting.clock (record : Waiting initial before monitor sentAt retries released)
    (placement : At before current) (anchor : Anchor initial current) : Waiting initial current monitor sentAt retries released where
  live := record.live.frame placement anchor
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
    change (record.live.history.clock placement).first = _
    rw [history_first]
    simpa only [Option.map_map, Function.comp_def, FirstReceipt.clock, FirstReceipt.reframe] using record.firstOperation

def NeedRead.clock (record : NeedRead initial before monitor retries)
    (placement : At before current) (anchor : Anchor initial current) : NeedRead initial current monitor retries where
  retired := record.retired.frame placement anchor
  phaseEq := record.phaseEq
  waiting := record.waiting
  retryCount := record.retryCount
  dropCount := record.dropCount
  drops := record.drops.clock placement
  first := record.first.map (fun receipt => receipt.clock placement)
  firstRef := by
    simpa only [Option.map_map, Function.comp_def, FirstReceipt.clock, FirstReceipt.reframe] using record.firstRef
  firstOperation := by
    change (record.retired.history.clock placement).first = _
    rw [history_first]
    simpa only [Option.map_map, Function.comp_def, FirstReceipt.clock, FirstReceipt.reframe] using record.firstOperation

def Done.clock (record : Done initial before monitor retries)
    (placement : At before current) (anchor : Anchor initial current) : Done initial current monitor retries where
  completed := record.completed.frame placement anchor
  phaseEq := record.phaseEq
  waiting := record.waiting
  retryCount := record.retryCount
  dropCount := record.dropCount
  drops := record.drops.clock placement
  first := record.first.map (fun receipt => receipt.clock placement)
  firstRef := by
    simpa only [Option.map_map, Function.comp_def, FirstReceipt.clock, FirstReceipt.reframe] using record.firstRef
  firstOperation := by
    change (record.completed.history.clock placement).first = _
    rw [complete_first]
    simpa only [Option.map_map, Function.comp_def, FirstReceipt.clock, FirstReceipt.reframe] using record.firstOperation

def Evidence.clock (evidence : Evidence initial native quantum before monitor)
    (placement : At before current) (anchor : Anchor initial current) : Evidence initial native quantum current monitor :=
  match evidence with
  | .needSend record => .needSend (record.clock placement anchor)
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

end

end Netlib.Check.CampusTCPRecoveryRoundEvidence
