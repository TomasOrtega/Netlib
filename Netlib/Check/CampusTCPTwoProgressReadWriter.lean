import Netlib.Check.CampusTCPTwoProgressPhaseBase
import Netlib.Check.CampusTCPTwoProgressRetry
import Netlib.Check.CampusTCPTwoProgressReadOrigins

/-!
# Selected writer evidence for actual packet sources

Originals keep their actual send identity.
Retries inherit byte ancestry from the current head's literal original.
-/

namespace Netlib.Check.CampusTCPTwoProgressReadWriter

open Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart
open CampusTCPTwoProgressPhaseBase (Core)
open CampusTCPTwoProgressSourceHistory (Issued)
open CampusTCPTwoProgressWriteOrigins (SelectedWriteOrigin)

namespace S
export CampusTCPTwoProgressSender (Stage Original Part)
end S
namespace R
export CampusTCPTwoProgressReceiver (Stage)
end R
namespace Retry
export CampusTCPTwoProgressRetry (Retry)
end Retry

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current : Cut input complete} {sender : Actor} {gateway : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {native : NativeEnv cut gateway initial.gatewayState.session.entry} {quantum allowance : Nat}
variable {monitor : CampusTCPTwoProgressMonitor.Monitor} {sent : S.Stage initial} {received : R.Stage}
variable {part : S.Part} {original : S.Original initial part} {head : Recovery.Outstanding} {rest : List Recovery.Outstanding}
variable {actual : Step input}

private theorem output_prior_eq (left right : ApplicationTrace.OutputAt steps)
    (ordered : ApplicationTrace.Chronological steps) (same : left.step = right.step) : left.prior = right.prior := by
  have unique : steps.Nodup := ordered.imp (fun {a b} before equal => by cases equal; exact Nat.lt_irrefl _ before)
  have first : steps[left.prior.length]? = some left.step :=
    (congrArg (fun list => list[left.prior.length]?) left.same).trans (by simp)
  have second : steps[right.prior.length]? = some right.step :=
    (congrArg (fun list => list[right.prior.length]?) right.same).trans (by simp)
  have length : left.prior.length = right.prior.length := unique.eq_of_getElem?_eq
    (List.getElem?_eq_some_iff.mp first).1 (by rw [first, second, same])
  have leftPrefix : left.prior <+: steps := ⟨_, left.same.symm⟩
  have rightPrefix : right.prior <+: steps := ⟨_, right.same.symm⟩
  rw [List.prefix_iff_eq_take.mp leftPrefix, List.prefix_iff_eq_take.mp rightPrefix, length]

private theorem output_eq (left right : ApplicationTrace.OutputAt steps)
    (ordered : ApplicationTrace.Chronological steps) (same : left.step = right.step) (packet : left.output = right.output) :
    left = right := by
  have prior := output_prior_eq left right ordered same
  cases left with
  | mk p s l h o r =>
    cases right with
    | mk q t m k v w =>
      dsimp only at same packet prior
      cases prior
      cases same
      cases packet
      have tail : l = m := by
        have equality := congrArg (fun steps => steps.drop p.length) (h.symm.trans k)
        simpa only [List.drop_left, List.cons.injEq, true_and] using equality
      cases tail
      rfl

def Issued.attempt_origin (issued : Issued initial current part original)
    (attempt : ApplicationTrace.OutputAt (applicationSteps current.endpoints sender))
    (step : attempt.step = original.operation) (packet : attempt.output = original.packet)
    (index : Nat) (byte : UInt8) (selected : attempt.output.packet.segment.payload[index]? = some byte) :
    SelectedWriteOrigin initial attempt index byte := by
  have same := output_eq issued.sent.attempt attempt (CampusTCPGapProgressOrigins.endpoint_order current sender)
    (issued.operation.trans step.symm) (issued.packet.trans packet.symm)
  cases same
  apply issued.packet_byte_origin index byte
  rw [← issued.packet]
  exact selected

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

private def retry_origin (core : Core initial native quantum allowance current monitor sent received)
    (value : Retry.Retry core.live part head rest actual) (issued : Issued initial current part original)
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

def lower_retry_origin {first : S.Original initial .lower} {second : S.Original initial .upper}
    (core : Core initial native quantum allowance current monitor (.both first second head) received)
    (value : Retry.Retry core.live .lower head [second.entry] actual)
    (index : Nat) (byte : UInt8) (selected : lower[index]? = some byte) :
    SelectedWriteOrigin initial value.attempt index byte :=
  retry_origin core value core.originals.1 index byte selected

def upper_retry_origin {first : S.Original initial .lower} {second : S.Original initial .upper}
    (core : Core initial native quantum allowance current monitor (.tail first second head) received)
    (value : Retry.Retry core.live .upper head [] actual)
    (index : Nat) (byte : UInt8) (selected : upper[index]? = some byte) :
    SelectedWriteOrigin initial value.attempt index byte :=
  retry_origin core value core.originals.2 index byte selected

theorem retry_joint (core : Core initial native quantum allowance current monitor sent received)
    (value : Retry.Retry core.live part head rest actual) :
    actual ∈ value.move.after.report.steps ∧ actual.result.output = some value.facts.produced :=
  ⟨value.move.member, value.facts.output⟩

structure SelectedOutput (initial : TwoWriteInitial cut sender gateway lower upper) (current : Cut input complete)
    (produced : Produced input.active input.passive) where
  attempt : ApplicationTrace.OutputAt (applicationSteps current.endpoints sender)
  production : produced = .application sender attempt.step attempt.output attempt.origin
  selected : ∀ index byte, attempt.output.packet.segment.payload[index]? = some byte →
    SelectedWriteOrigin initial attempt index byte

variable {produced other : Produced input.active input.passive} {next : Cut input complete}

private theorem application_eq (actor : Actor) (first second : T.Step) (packet output : EstablishedReceive.Input)
    (origin : ApplicationTrace.OutputOrigin first packet) (other : ApplicationTrace.OutputOrigin second output)
    (step : first = second) (same : packet = output) :
    Produced.application (active := input.active) (passive := input.passive) actor first packet origin =
      .application actor second output other := by cases step; cases same; rfl

def SelectedOutput.ofIssued (issued : Issued initial current part original) :
    SelectedOutput initial current (.application sender original.operation original.packet original.origin) where
  attempt := issued.sent.attempt
  production := application_eq sender original.operation issued.sent.attempt.step original.packet issued.sent.attempt.output
    original.origin issued.sent.attempt.origin issued.operation.symm issued.packet.symm
  selected := by
    intro index byte selected
    apply issued.packet_byte_origin index byte
    rw [← issued.packet]
    exact selected

def SelectedOutput.ofLowerRetry {first : S.Original initial .lower} {second : S.Original initial .upper}
    (core : Core initial native quantum allowance current monitor (.both first second head) received)
    (value : Retry.Retry core.live .lower head [second.entry] actual) :
    SelectedOutput initial value.move.after value.facts.produced where
  attempt := value.attempt
  production := value.facts.production
  selected := by
    intro index byte selected
    apply lower_retry_origin core value index byte
    simpa only [CampusTCPTwoProgressRetry.Retry.attempt, value.payload, CampusTCPTwoProgressSender.Part.bytes] using selected

def SelectedOutput.ofUpperRetry {first : S.Original initial .lower} {second : S.Original initial .upper}
    (core : Core initial native quantum allowance current monitor (.tail first second head) received)
    (value : Retry.Retry core.live .upper head [] actual) :
    SelectedOutput initial value.move.after value.facts.produced where
  attempt := value.attempt
  production := value.facts.production
  selected := by
    intro index byte selected
    apply upper_retry_origin core value index byte
    simpa only [CampusTCPTwoProgressRetry.Retry.attempt, value.payload, CampusTCPTwoProgressSender.Part.bytes] using selected

private def extend_selected {before after : List T.Step} {attempt : ApplicationTrace.OutputAt before} {index : Nat} {byte : UInt8}
    (selected : SelectedWriteOrigin initial attempt index byte)
    (retained : before <+: after) : SelectedWriteOrigin initial (extend_output attempt retained) index byte where
  origin := {
    prefixBytes := selected.origin.prefixBytes
    rangePrefix := selected.origin.rangePrefix
    sequence := selected.origin.sequence
    original := extend_output selected.origin.original retained
    originalIndex := selected.origin.originalIndex
    count := selected.origin.count
    policy := selected.origin.policy
    originalEvent := selected.origin.originalEvent
    originalAccepted := selected.origin.originalAccepted
    originalByte := selected.origin.originalByte
    originalPosition := selected.origin.originalPosition
    noLater := selected.origin.noLater
    retryEarlier := selected.origin.retryEarlier
    writerPrior := selected.origin.writerPrior
    writer := selected.origin.writer
    writerLater := selected.origin.writerLater
    writerSplit := selected.origin.writerSplit
    bytes := selected.origin.bytes
    writtenCount := selected.origin.writtenCount
    writerIndex := selected.origin.writerIndex
    writerEvent := selected.origin.writerEvent
    writerAccepted := selected.origin.writerAccepted
    writerByte := selected.origin.writerByte
    writerPosition := selected.origin.writerPosition
    writerEarlier := selected.origin.writerEarlier }
  writer := selected.writer
  bytes := selected.bytes

def SelectedOutput.retain (source : SelectedOutput initial current produced)
    (retained : applicationSteps current.endpoints sender <+: applicationSteps next.endpoints sender) :
    SelectedOutput initial next produced where
  attempt := extend_output source.attempt retained
  production := source.production
  selected := fun index byte selected => extend_selected (source.selected index byte selected) retained

def SelectedOutput.retain_steps (source : SelectedOutput initial current produced)
    (retained : current.report.steps <+: next.report.steps) : SelectedOutput initial next produced :=
  source.retain (CampusTCPGapProgressOrigins.application_retained retained sender)

def SelectedOutput.clock (source : SelectedOutput initial current produced)
    (placement : CampusTCPRecoveryRoundPhaseBase.At current next) : SelectedOutput initial next produced :=
  source.retain_steps placement.retained

def SelectedOutput.reindex (source : SelectedOutput initial current produced) (same : produced = other) :
    SelectedOutput initial current other := same ▸ source

def SelectedOutput.attempt_origin (source : SelectedOutput initial current produced)
    (attempt : ApplicationTrace.OutputAt (applicationSteps current.endpoints sender))
    (step : attempt.step = source.attempt.step) (packet : attempt.output = source.attempt.output)
    (index : Nat) (byte : UInt8) (selected : attempt.output.packet.segment.payload[index]? = some byte) :
    SelectedWriteOrigin initial attempt index byte := by
  have same := output_eq source.attempt attempt (CampusTCPGapProgressOrigins.endpoint_order current sender) step.symm packet.symm
  cases same
  exact source.selected index byte selected

def read_source_origin {first : S.Original initial .lower} {second : S.Original initial .upper} {timeouts index : Nat} {byte : UInt8}
    {done : CampusTCPTwoProgressRead.Completed initial current first second timeouts}
    (origin : CampusTCPTwoProgressRead.ReadOrigin done index byte)
    (source : SelectedOutput initial current origin.delivery.receive.receipt.served.ticket.value.produced) :
    SelectedWriteOrigin initial origin.attempt origin.localIndex byte := by
  have selected : origin.attempt.step = source.attempt.step ∧ origin.attempt.output = source.attempt.output := by
    obtain ⟨operation, packet, outputOrigin, production, step, output⟩ := origin.application_source
    have same := Produced.application.inj (source.production.symm.trans production)
    exact ⟨step.trans same.2.1.symm, output.trans same.2.2.symm⟩
  apply source.attempt_origin origin.attempt selected.1 selected.2
  exact origin.source_fields.2.2

end Netlib.Check.CampusTCPTwoProgressReadWriter
