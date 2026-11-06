import Netlib.Check.CampusTCPTwoProgressWriteHistory

/-!
# Actual issued originals and their selected writer

Each witness keeps the send's literal operation and packet.
Later operations extend only the witness's retained suffix.
-/

namespace Netlib.Check.CampusTCPTwoProgressSourceHistory

open Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart (TwoWriteInitial)
open CampusTCPTwoProgressState (Live)

namespace S
export CampusTCPTwoProgressSender (Part Original Stage Retires)
end S
namespace H
export CampusTCPTwoProgressWriteHistory (History)
end H
namespace O
export CampusTCPTwoProgressWriteOrigins (SentAfterWrite SelectedWriteOrigin)
end O
namespace Send
export CampusTCPTwoProgressSend (FirstSent SecondSent)
end Send

variable {input : Input} {complete : H.Completed input.active input.passive}
  {cut current next : Cut input complete} {sender : Actor} {gateway : Gateway} {lower upper : List UInt8}
  {initial : TwoWriteInitial cut sender gateway lower upper}

def beforeBytes (lower : List UInt8) : S.Part → List UInt8
  | .lower => []
  | .upper => lower

structure Issued (initial : TwoWriteInitial cut sender gateway lower upper) (current : Cut input complete)
    (part : S.Part) (original : S.Original initial part) where
  sent : O.SentAfterWrite initial current (beforeBytes lower part) (part.bytes lower upper)
  operation : sent.attempt.step = original.operation
  packet : sent.attempt.output = original.packet

variable {part : S.Part} {original : S.Original initial part}

private def extend_attempt (attempt : ApplicationTrace.OutputAt before) (retained : before <+: after) :
    ApplicationTrace.OutputAt after where
  prior := attempt.prior
  step := attempt.step
  later := attempt.later ++ after.drop before.length
  same := by
    obtain ⟨extra, history⟩ := retained
    rw [← history, List.drop_left]
    exact (congrArg (fun steps => steps ++ extra) attempt.same).trans (by
      simp only [List.append_assoc, List.cons_append])
  output := attempt.output
  origin := attempt.origin

def Issued.retain (issued : Issued initial current part original)
    (retained : applicationSteps current.endpoints sender <+: applicationSteps next.endpoints sender) :
    Issued initial next part original where
  sent := {
    attempt := extend_attempt issued.sent.attempt retained
    extra := issued.sent.extra
    prior := issued.sent.prior
    writes := issued.sent.writes
    emitted := issued.sent.emitted
    event := issued.sent.event
    payload := issued.sent.payload }
  operation := issued.operation
  packet := issued.packet

def Issued.retain_steps (issued : Issued initial current part original)
    (retained : current.report.steps <+: next.report.steps) : Issued initial next part original :=
  issued.retain (CampusTCPGapProgressOrigins.application_retained retained sender)

def Issued.clock (issued : Issued initial current part original)
    (placement : CampusTCPRecoveryRoundPhaseBase.At current next) : Issued initial next part original :=
  issued.retain_steps placement.retained

theorem Issued.member (issued : Issued initial current part original) :
    original.operation ∈ applicationSteps current.endpoints sender := by
  rw [← issued.operation]
  exact issued.sent.attempt.member

theorem Issued.joint (issued : Issued initial current part original) :
    ∃ actual ∈ current.report.steps, actual.result.application = some (sender, original.operation) := by
  apply CampusTCPRecoveryRoundOrigins.Report.application_origin current.report sender original.operation
  simpa only [current.connection, CampusTCPRoundPhaseHistory.connectionSteps] using issued.member

variable {timeouts : Nat} {received : CampusTCPTwoProgressReceiver.Stage} {actual : Step input}

def Issued.first {live : Live initial current .written timeouts received}
    (value : Send.FirstSent live actual) (history : H.History initial current []) :
    Issued initial value.facts.move.after .lower value.original := by
  have packet : value.facts.packet = value.original.packet :=
    congrArg Produced.output (value.facts.production.symm.trans value.production)
  have payload : value.facts.packet.packet.segment.payload = lower := packet ▸ value.original.payload
  exact ⟨history.sent value.facts payload, value.sameStep.symm, packet⟩

def Issued.second {first : S.Original initial .lower} {live : Live initial current (.lower first) timeouts received}
    (value : Send.SecondSent live actual) (history : H.History initial current lower) :
    Issued initial value.facts.move.after .upper value.original := by
  have packet : value.facts.packet = value.original.packet :=
    congrArg Produced.output (value.facts.production.symm.trans value.production)
  have payload : value.facts.packet.packet.segment.payload = upper := packet ▸ value.original.payload
  exact ⟨history.sent value.facts payload, value.sameStep.symm, packet⟩

def Issued.byte_origin (issued : Issued initial current part original)
    (index : Nat) (byte : UInt8) (selected : (part.bytes lower upper)[index]? = some byte) :
    O.SelectedWriteOrigin initial issued.sent.attempt index byte := by
  cases part
  · exact issued.sent.lower_origin index byte selected
  · exact issued.sent.upper_origin index byte selected

def Issued.packet_byte_origin (issued : Issued initial current part original)
    (index : Nat) (byte : UInt8) (selected : original.packet.packet.segment.payload[index]? = some byte) :
    O.SelectedWriteOrigin initial issued.sent.attempt index byte := by
  apply issued.byte_origin index byte
  simpa only [original.payload] using selected

def Originals (initial : TwoWriteInitial cut sender gateway lower upper) (current : Cut input complete) : S.Stage initial → Type
  | .written => PUnit
  | .lower first => Issued initial current .lower first
  | .both first second _ => Issued initial current .lower first × Issued initial current .upper second
  | .tail first second _ => Issued initial current .lower first × Issued initial current .upper second
  | .retired first second => Issued initial current .lower first × Issued initial current .upper second

variable {stage : S.Stage initial}

def Originals.ofInitial (value : TwoWriteInitial cut sender gateway lower upper) : Originals value cut .written := PUnit.unit

def Originals.retain (originals : Originals initial current stage)
    (retained : applicationSteps current.endpoints sender <+: applicationSteps next.endpoints sender) :
    Originals initial next stage := by
  cases stage with
  | written => exact PUnit.unit
  | lower first => exact originals.retain retained
  | both first second head => exact ⟨originals.1.retain retained, originals.2.retain retained⟩
  | tail first second head => exact ⟨originals.1.retain retained, originals.2.retain retained⟩
  | retired first second => exact ⟨originals.1.retain retained, originals.2.retain retained⟩

def Originals.retain_steps (originals : Originals initial current stage)
    (retained : current.report.steps <+: next.report.steps) : Originals initial next stage :=
  originals.retain (CampusTCPGapProgressOrigins.application_retained retained sender)

def Originals.clock (originals : Originals initial current stage)
    (placement : CampusTCPRecoveryRoundPhaseBase.At current next) : Originals initial next stage :=
  originals.retain_steps placement.retained

def Originals.first {live : Live initial current .written timeouts received}
    (value : Send.FirstSent live actual) (history : H.History initial current []) :
    Originals initial value.facts.move.after (.lower value.original) := Issued.first value history

def Originals.second {first : S.Original initial .lower} {live : Live initial current (.lower first) timeouts received}
    (originals : Originals initial current (.lower first)) (value : Send.SecondSent live actual)
    (history : H.History initial current lower) :
    Originals initial value.facts.move.after (.both first value.original first.entry) :=
  ⟨originals.retain_steps value.facts.move.retained, Issued.second value history⟩

def Originals.retry (originals : Originals initial current stage) (now : Nat) :
    Originals initial current (stage.retry now) := by cases stage <;> exact originals

private theorem originals_retire_eq (retiring : S.Retires stage count after) :
    Originals initial current stage = Originals initial current after := by cases retiring <;> rfl

def Originals.retire (originals : Originals initial current stage) (retiring : S.Retires stage count after) :
    Originals initial current after := (originals_retire_eq retiring) ▸ originals

end Netlib.Check.CampusTCPTwoProgressSourceHistory
