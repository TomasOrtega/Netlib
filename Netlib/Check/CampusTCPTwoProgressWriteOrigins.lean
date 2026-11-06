import Netlib.Check.CampusTCPTwoProgressStart
import Netlib.Check.CampusTCPGapProgressOrigins

/-!
# Original byte sources after the selected write

The send and write occur in the same retained endpoint history.
The stream coordinate selects the exact writer byte.
-/

namespace Netlib.Check.CampusTCPTwoProgressWriteOrigins

open Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current : Cut input complete} {sender : Actor} {gateway : Gateway}
variable {lower upper beforeBytes payload : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}

structure SentAfterWrite (initial : TwoWriteInitial cut sender gateway lower upper)
    (current : Cut input complete) (beforeBytes payload : List UInt8) where
  attempt : T.OutputAt (applicationSteps current.endpoints sender)
  extra : List T.Step
  prior : attempt.prior = applicationSteps cut.endpoints sender ++ extra
  writes : extra.flatMap ApplicationTrace.Step.written = []
  emitted : extra.flatMap ApplicationTrace.Step.emitted = beforeBytes
  event : attempt.step.event = .send payload.length true
  payload : attempt.output.packet.segment.payload = payload

theorem prior_balance (initial : TwoWriteInitial cut sender gateway lower upper) :
    initial.write.prior.flatMap ApplicationTrace.Step.written =
      initial.write.prior.flatMap ApplicationTrace.Step.emitted := by
  have balance := initial.write.before_chain.pending
  simpa only [CampusTCPGapProgressOrigins.seed_empty_pending complete sender,
    initial.write.emptyPending, List.nil_append, List.append_nil] using balance

theorem SentAfterWrite.accepted (sent : SentAfterWrite initial current beforeBytes payload) :
    sent.attempt.step.result.decision = .accepted (.send payload.length) := by
  cases sent.attempt.origin with
  | send count policy event accepted actual =>
    have same := ApplicationTrace.Event.send.inj (event.symm.trans sent.event)
    simpa only [same.1] using accepted
  | retry count policy event accepted actual => rw [sent.event] at event; cases event
  | ack policy event accepted actual => rw [sent.event] at event; cases event
  | dispatchAck policy event accepted actual => rw [sent.event] at event; cases event

theorem SentAfterWrite.emitted_payload (sent : SentAfterWrite initial current beforeBytes payload) :
    sent.attempt.step.emitted = payload := by
  have noRetry : ApplicationTrace.NoRetry sent.attempt.step := by
    intro policy event
    rw [sent.event] at event
    cases event
  exact (sent.attempt.origin.fields noRetry).1.symm.trans sent.payload

theorem SentAfterWrite.writer_split (sent : SentAfterWrite initial current beforeBytes payload) :
    sent.attempt.prior = initial.write.prior ++ initial.write.writer :: (initial.write.later ++ sent.extra) := by
  rw [sent.prior, initial.write.history]
  simp only [List.append_assoc, List.cons_append]

theorem SentAfterWrite.coordinate (sent : SentAfterWrite initial current beforeBytes payload) :
    (sent.attempt.prior.flatMap ApplicationTrace.Step.emitted).length =
      (initial.write.prior.flatMap ApplicationTrace.Step.written).length + beforeBytes.length := by
  rw [sent.prior, List.flatMap_append, List.length_append, sent.emitted,
    initial.write.coordinate, prior_balance initial]

structure SelectedWriteOrigin (initial : TwoWriteInitial cut sender gateway lower upper)
    (attempt : T.OutputAt steps) (index : Nat) (byte : UInt8) where
  origin : ApplicationTrace.AttemptByteOrigin (CampusTCPGapProgressStart.seed complete sender) steps attempt index byte
  writer : origin.writer = initial.write.writer
  bytes : origin.bytes = lower ++ upper

def SentAfterWrite.byte_origin (sent : SentAfterWrite initial current beforeBytes payload)
    (index : Nat) (byte : UInt8) (selected : payload[index]? = some byte)
    (writerByte : (lower ++ upper)[beforeBytes.length + index]? = some byte) :
    SelectedWriteOrigin initial sent.attempt index byte := by
  have noRetry : ApplicationTrace.NoRetry sent.attempt.step := by
    intro policy event
    rw [sent.event] at event
    cases event
  let provenance : ApplicationTrace.AttemptByteOrigin (CampusTCPGapProgressStart.seed complete sender)
      (applicationSteps current.endpoints sender) sent.attempt index byte := {
    prefixBytes := sent.attempt.prior.flatMap ApplicationTrace.Step.emitted
    rangePrefix := by
      rw [sent.payload, List.flatMap_append, List.flatMap_cons, sent.emitted_payload,
        List.flatMap_nil, List.append_nil]
      exact List.prefix_refl _
    sequence := sent.attempt.coordinate (CampusTCPGapProgressStart.endpoint_chain current sender) noRetry
    original := sent.attempt
    originalIndex := index
    count := payload.length
    policy := true
    originalEvent := sent.event
    originalAccepted := sent.accepted
    originalByte := by rw [sent.payload]; exact selected
    originalPosition := rfl
    noLater := Nat.le_refl _
    retryEarlier := by intro policy timeout; exact False.elim (noRetry policy timeout)
    writerPrior := initial.write.prior
    writer := initial.write.writer
    writerLater := initial.write.later ++ sent.extra
    writerSplit := sent.writer_split
    bytes := lower ++ upper
    writtenCount := (lower ++ upper).length
    writerIndex := beforeBytes.length + index
    writerEvent := initial.write.event
    writerAccepted := initial.write.accepted
    writerByte := writerByte
    writerPosition := by rw [sent.coordinate]; omega
    writerEarlier := sent.attempt.prior_before (CampusTCPGapProgressOrigins.endpoint_order current sender)
      initial.write.writer (by rw [sent.writer_split]; simp)
  }
  exact ⟨provenance, rfl, rfl⟩

def SentAfterWrite.lower_origin (sent : SentAfterWrite initial current [] lower)
    (index : Nat) (byte : UInt8) (selected : lower[index]? = some byte) :
    SelectedWriteOrigin initial sent.attempt index byte := by
  apply sent.byte_origin index byte selected
  rw [List.length_nil, Nat.zero_add, List.getElem?_append_left (List.getElem?_eq_some_iff.mp selected).1]
  exact selected

def SentAfterWrite.upper_origin (sent : SentAfterWrite initial current lower upper)
    (index : Nat) (byte : UInt8) (selected : upper[index]? = some byte) :
    SelectedWriteOrigin initial sent.attempt index byte := by
  apply sent.byte_origin index byte selected
  rw [List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
  exact selected

end Netlib.Check.CampusTCPTwoProgressWriteOrigins
