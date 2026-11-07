import Netlib.Check.CampusTCPTwoTransferLocatedTimeout
import Netlib.Check.CampusTCPTwoTransferLocatedCore
import Netlib.Check.CampusTCPTwoProgressReadWriter

namespace Netlib.Check.CampusTCPTwoTransferTimeoutSources

open Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart
open CampusTCPTwoTransferNative (Checks Routing)
open CampusTCPTwoTransferLocatedCore (Core)
open CampusTCPTwoTransferLocatedTimeout (Retry)
open CampusTCPTwoProgressSourceHistory (Issued)
open CampusTCPTwoProgressWriteOrigins (SelectedWriteOrigin)
open CampusTCPTwoProgressReadWriter (SelectedOutput)

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current : Cut input complete} {sender : Actor} {gateway location : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {checks : Checks cut initial.gatewayState.session.entry} {routing : Routing cut gateway}
variable {quantum allowance : Nat} {reverseLower reverseUpper : List UInt8}
variable {monitor : CampusTCPTwoTransferMonitor.Monitor}
variable {sent : CampusTCPTwoProgressSender.Stage initial} {received : CampusTCPTwoProgressReceiver.Stage}
variable {part : CampusTCPTwoProgressSender.Part}
variable {head : Recovery.Outstanding} {rest : List Recovery.Outstanding} {actual : Step input}

private def extend_output (value : ApplicationTrace.OutputAt before) (retained : before <+: after) :
    ApplicationTrace.OutputAt after where
  prior := value.prior
  step := value.step
  later := value.later ++ after.drop before.length
  same := by
    obtain ⟨extra, history⟩ := retained
    rw [← history, List.drop_left]
    exact (congrArg (fun steps => steps ++ extra) value.same).trans (by simp only [List.append_assoc, List.cons_append])
  output := value.output
  origin := value.origin

private def retry_origin {original : CampusTCPTwoProgressSender.Original initial part}
    (core : Core initial checks routing quantum allowance reverseLower reverseUpper current monitor location sent received)
    (value : Retry core.live part head rest actual) (issued : Issued initial current part original)
    (index : Nat) (byte : UInt8) (selected : (part.bytes lower upper)[index]? = some byte) :
    SelectedWriteOrigin initial value.attempt index byte := by
  let base := issued.byte_origin index byte selected
  have retained := CampusTCPGapProgressOrigins.application_retained value.move.retained sender
  let extended := extend_output base.origin.original retained
  have ordered := CampusTCPGapProgressOrigins.endpoint_order value.move.after sender
  rw [value.selectedSteps] at ordered
  have earlier : issued.sent.attempt.step.stamp < value.facts.localStep.stamp :=
    (List.pairwise_append.mp ordered).2.2 _ issued.sent.attempt.member _ (by simp)
  have sourcePayload : value.facts.packet.packet.segment.payload = issued.sent.attempt.output.packet.segment.payload := by
    rw [value.payload, issued.packet, original.payload]
  have sourceSequence : value.facts.packet.packet.segment.sequence = issued.sent.attempt.output.packet.segment.sequence := by
    rw [issued.packet]
    exact (Endpoint.emitAt_transport _ _ _ _ value.encoded).2.1.trans
      ((value.selection.sequence core.live.senderFlight).trans original.sequence.symm)
  have scope : (applicationSteps current.endpoints sender).flatMap ApplicationTrace.Step.emitted <+:
      (value.attempt.prior ++ [value.attempt.step]).flatMap ApplicationTrace.Step.emitted := by
    change (applicationSteps current.endpoints sender).flatMap ApplicationTrace.Step.emitted <+:
      (applicationSteps current.endpoints sender ++ [value.facts.localStep]).flatMap ApplicationTrace.Step.emitted
    rw [List.flatMap_append]
    exact List.prefix_append _ _
  let provenance : ApplicationTrace.AttemptByteOrigin (CampusTCPGapProgressStart.seed complete sender)
      (applicationSteps value.move.after.endpoints sender) value.attempt index byte := {
    prefixBytes := base.origin.prefixBytes
    rangePrefix := by
      change base.origin.prefixBytes ++ value.facts.packet.packet.segment.payload <+: _
      rw [sourcePayload]
      exact (base.origin.rangePrefix.trans issued.sent.attempt.scope_prefix).trans scope
    sequence := sourceSequence.trans base.origin.sequence
    original := extended
    originalIndex := base.origin.originalIndex
    count := base.origin.count
    policy := base.origin.policy
    originalEvent := base.origin.originalEvent
    originalAccepted := base.origin.originalAccepted
    originalByte := base.origin.originalByte
    originalPosition := base.origin.originalPosition
    noLater := Nat.le_trans base.origin.noLater (Nat.le_of_lt earlier)
    retryEarlier := by intro _ _; exact Nat.lt_of_le_of_lt base.origin.noLater earlier
    writerPrior := base.origin.writerPrior
    writer := base.origin.writer
    writerLater := base.origin.writerLater
    writerSplit := base.origin.writerSplit
    bytes := base.origin.bytes
    writtenCount := base.origin.writtenCount
    writerIndex := base.origin.writerIndex
    writerEvent := base.origin.writerEvent
    writerAccepted := base.origin.writerAccepted
    writerByte := base.origin.writerByte
    writerPosition := base.origin.writerPosition
    writerEarlier := base.origin.writerEarlier }
  exact ⟨provenance, base.writer, base.bytes⟩

def source (core : Core initial checks routing quantum allowance reverseLower reverseUpper current monitor location sent received)
    (value : Retry core.live part head rest actual) : SelectedOutput initial value.move.after value.facts.produced where
  attempt := value.attempt
  production := value.facts.production
  selected := by
    intro index byte selected
    have payload : (part.bytes lower upper)[index]? = some byte := by
      simpa only [CampusTCPTwoTransferLocatedTimeout.Retry.attempt, value.payload] using selected
    cases sent with
    | written | lower _ | retired _ _ =>
      exact False.elim (by have selected := value.selection; cases selected)
    | both first second entry =>
      have partEq : part = .lower := by cases value.selection; rfl
      cases partEq
      exact retry_origin core value core.originals.1 index byte payload
    | tail first second entry =>
      have partEq : part = .upper := by cases value.selection; rfl
      cases partEq
      exact retry_origin core value core.originals.2 index byte payload

end Netlib.Check.CampusTCPTwoTransferTimeoutSources
