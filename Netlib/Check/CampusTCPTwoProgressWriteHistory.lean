import Netlib.Check.CampusTCPTwoProgressWriteOrigins
import Netlib.Check.CampusTCPTwoProgressSend

/-!
# Actual sender history after the selected write

Only original sends extend the emitted stream.
The actual send constructs its writer evidence from this preceding history.
-/

namespace Netlib.Check.CampusTCPTwoProgressWriteHistory

open Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart
open CampusTCPTwoProgressSend (SendFacts)

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current next : Cut input complete} {sender : Actor} {gateway : Gateway} {lower upper beforeBytes bytes : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}

structure History (initial : TwoWriteInitial cut sender gateway lower upper) (current : Cut input complete)
    (emitted : List UInt8) where
  operations : List T.Step
  steps : applicationSteps current.endpoints sender = applicationSteps cut.endpoints sender ++ operations
  writes : operations.flatMap ApplicationTrace.Step.written = []
  stream : operations.flatMap ApplicationTrace.Step.emitted = emitted

def History.ofInitial (initial : TwoWriteInitial cut sender gateway lower upper) : History initial cut [] :=
  ⟨[], by simp, rfl, rfl⟩

def History.same (history : History initial current beforeBytes)
    (same : applicationSteps next.endpoints sender = applicationSteps current.endpoints sender) :
    History initial next beforeBytes :=
  ⟨history.operations, same.trans history.steps, history.writes, history.stream⟩

def History.quiet (history : History initial current beforeBytes) (operation : T.Step)
    (steps : applicationSteps next.endpoints sender = applicationSteps current.endpoints sender ++ [operation])
    (written : operation.written = []) (emitted : operation.emitted = []) : History initial next beforeBytes := by
  refine ⟨history.operations ++ [operation], ?_, ?_, ?_⟩
  · rw [steps, history.steps, List.append_assoc]
  · simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil, written,
      history.writes]
  · simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil, emitted,
      history.stream]

def History.send (history : History initial current beforeBytes)
    (facts : SendFacts current sender bytes.length actual) (payload : facts.packet.packet.segment.payload = bytes) :
    History initial facts.move.after (beforeBytes ++ bytes) := by
  have written : facts.localStep.written = [] := by
    simp only [ApplicationTrace.Step.written, ApplicationTrace.written, facts.localEvent]
  have noRetry : ApplicationTrace.NoRetry facts.localStep := by
    intro policy event
    rw [facts.localEvent] at event
    cases event
  have emitted : facts.localStep.emitted = bytes := (facts.origin.fields noRetry).1.symm.trans payload
  refine ⟨history.operations ++ [facts.localStep], ?_, ?_, ?_⟩
  · rw [facts.selectedSteps, history.steps, List.append_assoc]
  · simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      written, history.writes]
  · simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      emitted, history.stream]

def History.sent (history : History initial current beforeBytes)
    (facts : SendFacts current sender bytes.length actual) (payload : facts.packet.packet.segment.payload = bytes) :
    CampusTCPTwoProgressWriteOrigins.SentAfterWrite initial facts.move.after beforeBytes bytes where
  attempt := facts.attempt
  extra := history.operations
  prior := history.steps
  writes := history.writes
  emitted := history.stream
  event := facts.localEvent
  payload := payload

def History.clock (history : History initial current beforeBytes)
    (placement : CampusTCPRecoveryRoundPhaseBase.At current next) : History initial next beforeBytes := by
  let extra := (applicationSteps next.endpoints sender).drop (applicationSteps current.endpoints sender).length
  have properties := CampusTCPGapProgressHistory.clock_delta placement sender
  have written : extra.flatMap ApplicationTrace.Step.written = [] := by
    apply List.flatMap_eq_nil_iff.mpr
    intro operation member
    obtain ⟨millis, event⟩ := properties.2 operation member
    simp only [ApplicationTrace.Step.written, ApplicationTrace.written, event]
  have emitted : extra.flatMap ApplicationTrace.Step.emitted = [] := by
    apply List.flatMap_eq_nil_iff.mpr
    intro operation member
    obtain ⟨millis, event⟩ := properties.2 operation member
    simp only [ApplicationTrace.Step.emitted, ApplicationTrace.emitted, event]
  refine ⟨history.operations ++ extra, ?_, ?_, ?_⟩
  · exact properties.1.trans ((congrArg (fun steps => steps ++ extra) history.steps).trans (List.append_assoc _ _ _))
  · simp only [List.flatMap_append, history.writes, written, List.append_nil]
  · simp only [List.flatMap_append, history.stream, emitted, List.append_nil]

theorem receive_quiet (operation : T.Step) (event : operation.event = .receive packet) :
    operation.written = [] ∧ operation.emitted = [] := by
  simp [ApplicationTrace.Step.written, ApplicationTrace.written, ApplicationTrace.Step.emitted,
    ApplicationTrace.emitted, event]

theorem timeout_quiet (operation : T.Step) (event : operation.event = .timeout policy) :
    operation.written = [] ∧ operation.emitted = [] := by
  simp [ApplicationTrace.Step.written, ApplicationTrace.written, ApplicationTrace.Step.emitted,
    ApplicationTrace.emitted, event]

end Netlib.Check.CampusTCPTwoProgressWriteHistory
