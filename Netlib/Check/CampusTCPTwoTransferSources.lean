import Netlib.Check.CampusTCPTwoTransferNetwork
import Netlib.Check.CampusTCPTransferSequence
import Netlib.Check.CampusTCPTwoProgressReceiptSources

/-!
# Retained writer sources through transfer

Controls and gateway service keep the selected application history.
The source ledger extends over those same actual report steps.
-/

namespace Netlib.Check.CampusTCPTwoTransferSources

open Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPRoundPhaseBase (Move)
open CampusTCPTwoProgressStart (TwoWriteInitial)

namespace S
export CampusTCPTwoProgressSender (Stage Part Original)
end S
namespace O
export CampusTCPTwoProgressSourceHistory (Originals Issued)
end O
namespace W
export CampusTCPTwoProgressWriteHistory (History)
end W
namespace R
export CampusTCPTwoProgressReceiptSources (History)
end R
namespace P
export CampusTCPTwoProgressReadWriter (SelectedOutput)
end P

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current next later : Cut input complete} {sender : Actor} {gateway : Gateway}
variable {lower upper emittedBytes : List UInt8} {initial : TwoWriteInitial cut sender gateway lower upper}
variable {stage : S.Stage initial} {part : S.Part} {original : S.Original initial part}
variable {produced : Produced input.active input.passive} {actual : Step input}

structure Frame (current next : Cut input complete) : Prop where
  retained : current.report.steps <+: next.report.steps
  endpoints : next.endpoints = current.endpoints
  quiet : ∀ actual ∈ next.report.steps.drop current.report.steps.length, actual.result.receipt = none

def Frame.suffix (_frame : Frame current next) : List (Step input) :=
  next.report.steps.drop current.report.steps.length

theorem Frame.history (frame : Frame current next) :
    next.report.steps = current.report.steps ++ frame.suffix := by
  obtain ⟨extra, history⟩ := frame.retained
  simp only [Frame.suffix, ← history, List.drop_append_length]

theorem Frame.refl (current : Cut input complete) : Frame current current :=
  ⟨List.prefix_refl _, rfl, by simp⟩

theorem Frame.trans (first : Frame current next) (second : Frame next later) : Frame current later := by
  refine ⟨first.retained.trans second.retained, second.endpoints.trans first.endpoints, ?_⟩
  intro actual member
  have history : later.report.steps = current.report.steps ++ (first.suffix ++ second.suffix) := by
    rw [second.history, first.history, List.append_assoc]
  rw [history, List.drop_append_length] at member
  rcases List.mem_append.mp member with earlier | last
  · exact first.quiet actual earlier
  · exact second.quiet actual last

theorem Frame.application_steps (frame : Frame current next) (actor : Actor) :
    applicationSteps next.endpoints actor = applicationSteps current.endpoints actor :=
  congrArg (fun endpoints => applicationSteps endpoints actor) frame.endpoints

def Frame.issued (frame : Frame current next) (value : O.Issued initial current part original) :
    O.Issued initial next part original := value.retain_steps frame.retained

theorem Frame.issued_step (frame : Frame current next) (value : O.Issued initial current part original) :
    (frame.issued value).sent.attempt.step = value.sent.attempt.step := rfl

theorem Frame.issued_packet (frame : Frame current next) (value : O.Issued initial current part original) :
    (frame.issued value).sent.attempt.output = value.sent.attempt.output := rfl

def Frame.originals (frame : Frame current next) (value : O.Originals initial current stage) :
    O.Originals initial next stage := value.retain_steps frame.retained

def Frame.writer (frame : Frame current next) (value : W.History initial current emittedBytes) :
    W.History initial next emittedBytes := value.same (frame.application_steps sender)

theorem Frame.writer_operations (frame : Frame current next) (value : W.History initial current emittedBytes) :
    (frame.writer value).operations = value.operations := rfl

def Frame.selected (frame : Frame current next) (value : P.SelectedOutput initial current produced) :
    P.SelectedOutput initial next produced := value.retain_steps frame.retained

theorem Frame.selected_step (frame : Frame current next) (value : P.SelectedOutput initial current produced) :
    (frame.selected value).attempt.step = value.attempt.step := rfl

theorem Frame.selected_packet (frame : Frame current next) (value : P.SelectedOutput initial current produced) :
    (frame.selected value).attempt.output = value.attempt.output := rfl

def Frame.receipts (frame : Frame current next) (value : R.History initial current) : R.History initial next where
  suffix := value.suffix ++ frame.suffix
  steps := by rw [frame.history, value.steps, List.append_assoc]
  sources := by
    intro chosen member receipt recorded receiver
    rcases List.mem_append.mp member with earlier | last
    · obtain ⟨source⟩ := value.sources chosen earlier receipt recorded receiver
      exact ⟨frame.selected source⟩
    · have absent := frame.quiet chosen last
      rw [absent] at recorded
      cases recorded

theorem Frame.receipts_suffix (frame : Frame current next) (value : R.History initial current) :
    (frame.receipts value).suffix = value.suffix ++ next.report.steps.drop current.report.steps.length := rfl

structure Sources (initial : TwoWriteInitial cut sender gateway lower upper) (current : Cut input complete)
    (stage : S.Stage initial) (emitted : List UInt8) where
  originals : O.Originals initial current stage
  writer : W.History initial current emitted
  receipts : R.History initial current

def Frame.sources (frame : Frame current next) (value : Sources initial current stage emittedBytes) :
    Sources initial next stage emittedBytes :=
  ⟨frame.originals value.originals, frame.writer value.writer, frame.receipts value.receipts⟩

theorem Frame.ofMove (move : Move current actual) (endpoints : move.after.endpoints = current.endpoints)
    (quiet : actual.result.receipt = none) : Frame current move.after := by
  refine ⟨move.retained, endpoints, ?_⟩
  intro selected member
  rw [move.history, List.drop_append_length] at member
  have same := List.mem_singleton.mp member
  subst selected
  exact quiet

theorem Frame.control (value : CampusTCPTransferEnabled.Control current event actual) : Frame current value.move.after :=
  Frame.ofMove value.move value.endpoints value.quiet.receipt

theorem Frame.service
    (value : CampusTCPTwoTransferNetwork.Service current item hit session actual served emission emitted) :
    Frame current value.move.after :=
  Frame.ofMove value.move value.endpoints
    (CampusTCPTwoProgressReceiptFrames.Step.receipt_none actual (by rw [value.facts.event]; trivial))

theorem Frame.assignment
    (value : CampusTCPTwoTransferNetwork.Assignment current index ingress produced actual) : Frame current value.move.after :=
  Frame.ofMove value.move value.endpoints
    (CampusTCPTwoProgressReceiptFrames.Step.receipt_none actual (by rw [value.facts.event]; trivial))

theorem Frame.seven (value : CampusTCPTransferSequence.Seven current) : Frame current value.final :=
  (Frame.control value.paused).trans ((Frame.control value.staged).trans ((Frame.control value.installed).trans
    ((Frame.control value.clientRouted).trans ((Frame.control value.serverRouted).trans
      ((Frame.control value.fenced).trans (Frame.control value.resumed))))))

theorem Frame.six (value : CampusTCPTransferSequence.Six current) : Frame current value.final :=
  (Frame.control value.staged).trans ((Frame.control value.installed).trans
    ((Frame.control value.clientRouted).trans ((Frame.control value.serverRouted).trans
      ((Frame.control value.fenced).trans (Frame.control value.resumed)))))

end Netlib.Check.CampusTCPTwoTransferSources
