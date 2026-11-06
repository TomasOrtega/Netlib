import Netlib.Check.CampusTCPGapProgressHistory

/-!
# Ordered release chunks after the selected write

The task retains prior endpoint history.
New release chunks form a prefix of the selected bytes until the final read.
-/

namespace Netlib.Check.CampusTCPTwoProgressHistory

open Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPRoundPhaseHistory (Summary summary_clocks nonemptyRead)
open CampusTCPRecoveryRoundHistory (nonemptyRelease)

structure Streams (bytes released : List UInt8) (operations : List T.Step) where
  isPrefix : released <+: bytes
  releaseStream : operations.flatMap ApplicationTrace.Step.releasedPayload = released
  readStream : operations.flatMap ApplicationTrace.Step.readBytes = []
  reads : operations.filter nonemptyRead = []

structure ReadStreams (bytes : List UInt8) (operations : List T.Step) (reader : T.Step) where
  releaseStream : operations.flatMap ApplicationTrace.Step.releasedPayload = bytes
  readStream : operations.flatMap ApplicationTrace.Step.readBytes = bytes
  reads : operations.filter nonemptyRead = [reader]
  readBytes : reader.readBytes = bytes
  readEvent : reader.event = .read bytes.length

variable {bytes released : List UInt8} {operations : List T.Step} {reader : T.Step}

theorem Streams.silent_append (history : Streams bytes released operations) (extra : List T.Step)
    (release : extra.flatMap ApplicationTrace.Step.releasedPayload = [])
    (read : extra.flatMap ApplicationTrace.Step.readBytes = []) (reads : extra.filter nonemptyRead = []) :
    Streams bytes released (operations ++ extra) := by
  refine ⟨history.isPrefix, ?_, ?_, ?_⟩
  · simp only [List.flatMap_append, release, List.append_nil, history.releaseStream]
  · simp only [List.flatMap_append, read, List.append_nil, history.readStream]
  · simp only [List.filter_append, reads, List.append_nil, history.reads]

theorem Streams.release_append (history : Streams bytes released operations) (operation : T.Step)
    (within : released ++ operation.releasedPayload <+: bytes) (read : operation.readBytes = []) :
    Streams bytes (released ++ operation.releasedPayload) (operations ++ [operation]) := by
  refine ⟨within, ?_, ?_, ?_⟩
  · simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil, history.releaseStream]
  · simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil, read,
      history.readStream]
  · simp only [List.filter_append, history.reads, List.filter_cons, List.filter_nil,
      nonemptyRead, read, List.isEmpty_nil, Bool.not_true, Bool.false_eq_true, ite_false, List.nil_append]

theorem Streams.read_append (history : Streams bytes bytes operations) (operation : T.Step)
    (nonempty : bytes ≠ []) (event : operation.event = .read bytes.length) (read : operation.readBytes = bytes) :
    ReadStreams bytes (operations ++ [operation]) operation := by
  have release : operation.releasedPayload = [] := by
    simp only [ApplicationTrace.Step.releasedPayload, ApplicationTrace.releasedPayload, event]
  have populated : bytes.isEmpty = false := List.isEmpty_eq_false_iff.mpr nonempty
  refine ⟨?_, ?_, ?_, read, event⟩
  · simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      release, history.releaseStream]
  · simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      read, history.readStream, List.nil_append]
  · simp only [List.filter_append, history.reads, List.filter_cons, List.filter_nil, nonemptyRead,
      read, populated, Bool.not_false, ite_true, List.nil_append]

theorem ReadStreams.clocks_append (history : ReadStreams bytes operations reader) (extra : List T.Step)
    (clocks : ∀ operation ∈ extra, ∃ now, operation.event = .advanceClock now) :
    ReadStreams bytes (operations ++ extra) reader := by
  have quiet := summary_clocks extra clocks
  have release : extra.flatMap ApplicationTrace.Step.releasedPayload = [] := congrArg Summary.released quiet
  have read : extra.flatMap ApplicationTrace.Step.readBytes = [] := congrArg Summary.read quiet
  have reads : extra.filter nonemptyRead = [] := congrArg Summary.reads quiet
  refine ⟨?_, ?_, ?_, history.readBytes, history.readEvent⟩
  · simp only [List.flatMap_append, release, List.append_nil, history.releaseStream]
  · simp only [List.flatMap_append, read, List.append_nil, history.readStream]
  · simp only [List.filter_append, reads, List.append_nil, history.reads]

theorem release_chunks (operations : List T.Step) :
    (operations.filter nonemptyRelease).flatMap ApplicationTrace.Step.releasedPayload =
      operations.flatMap ApplicationTrace.Step.releasedPayload := by
  induction operations with
  | nil => rfl
  | cons operation rest ih =>
    by_cases empty : operation.releasedPayload = []
    · simp only [List.filter_cons, nonemptyRelease, empty, List.isEmpty_nil, Bool.not_true,
        Bool.false_eq_true, ite_false, List.flatMap_cons, List.nil_append, ih]
    · have populated : operation.releasedPayload.isEmpty = false := List.isEmpty_eq_false_iff.mpr empty
      simp only [List.filter_cons, nonemptyRelease, populated, Bool.not_false, ite_true,
        List.flatMap_cons, ih]

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {initial before current : Cut input complete} {actor : Actor}

structure History (initial current : Cut input complete) (actor : Actor) (bytes released : List UInt8) where
  operations : List T.Step
  steps : applicationSteps current.endpoints actor = applicationSteps initial.endpoints actor ++ operations
  streams : Streams bytes released operations

structure Complete (initial current : Cut input complete) (actor : Actor) (bytes : List UInt8) (reader : T.Step) where
  operations : List T.Step
  steps : applicationSteps current.endpoints actor = applicationSteps initial.endpoints actor ++ operations
  streams : ReadStreams bytes operations reader

def History.ofCut (cut : Cut input complete) (actor : Actor) (bytes : List UInt8) :
    History cut cut actor bytes [] :=
  ⟨[], by simp, ⟨List.nil_prefix, rfl, rfl, rfl⟩⟩

def History.same (history : History initial before actor bytes released)
    (steps : applicationSteps current.endpoints actor = applicationSteps before.endpoints actor) :
    History initial current actor bytes released :=
  ⟨history.operations, steps.trans history.steps, history.streams⟩

def History.clock (history : History initial before actor bytes released)
    (placement : CampusTCPRecoveryRoundPhaseBase.At before current) :
    History initial current actor bytes released := by
  let extra := (applicationSteps current.endpoints actor).drop (applicationSteps before.endpoints actor).length
  have properties := CampusTCPGapProgressHistory.clock_delta placement actor
  have quiet := summary_clocks extra properties.2
  refine ⟨history.operations ++ extra, ?_, history.streams.silent_append extra
    (congrArg Summary.released quiet) (congrArg Summary.read quiet) (congrArg Summary.reads quiet)⟩
  exact properties.1.trans ((congrArg (fun steps => steps ++ extra) history.steps).trans
    (List.append_assoc _ _ _))

def History.release (history : History initial before actor bytes released) (operation : T.Step)
    (steps : applicationSteps current.endpoints actor = applicationSteps before.endpoints actor ++ [operation])
    (within : released ++ operation.releasedPayload <+: bytes) (read : operation.readBytes = []) :
    History initial current actor bytes (released ++ operation.releasedPayload) := by
  refine ⟨history.operations ++ [operation], ?_, history.streams.release_append operation within read⟩
  rw [steps, history.steps, List.append_assoc]

def History.quiet (history : History initial before actor bytes released) (operation : T.Step)
    (steps : applicationSteps current.endpoints actor = applicationSteps before.endpoints actor ++ [operation])
    (release : operation.releasedPayload = []) (read : operation.readBytes = []) :
    History initial current actor bytes released := by
  refine ⟨history.operations ++ [operation], ?_, history.streams.silent_append [operation] ?_ ?_ ?_⟩
  · rw [steps, history.steps, List.append_assoc]
  · simp only [List.flatMap_cons, List.flatMap_nil, release, List.nil_append]
  · simp only [List.flatMap_cons, List.flatMap_nil, read, List.nil_append]
  · simp only [List.filter_cons, List.filter_nil, nonemptyRead, read, List.isEmpty_nil,
      Bool.not_true, Bool.false_eq_true, ite_false]

def History.read (history : History initial before actor bytes bytes) (operation : T.Step)
    (steps : applicationSteps current.endpoints actor = applicationSteps before.endpoints actor ++ [operation])
    (nonempty : bytes ≠ []) (event : operation.event = .read bytes.length) (read : operation.readBytes = bytes) :
    Complete initial current actor bytes operation := by
  refine ⟨history.operations ++ [operation], ?_, history.streams.read_append operation nonempty event read⟩
  rw [steps, history.steps, List.append_assoc]

def Complete.clock (history : Complete initial before actor bytes reader)
    (placement : CampusTCPRecoveryRoundPhaseBase.At before current) : Complete initial current actor bytes reader := by
  let extra := (applicationSteps current.endpoints actor).drop (applicationSteps before.endpoints actor).length
  have properties := CampusTCPGapProgressHistory.clock_delta placement actor
  refine ⟨history.operations ++ extra, ?_, history.streams.clocks_append extra properties.2⟩
  exact properties.1.trans ((congrArg (fun steps => steps ++ extra) history.steps).trans
    (List.append_assoc _ _ _))

theorem Complete.exact_read (history : Complete initial current actor bytes reader) :
    reader ∈ applicationSteps current.endpoints actor ∧
      history.operations.filter nonemptyRead = [reader] ∧
      reader.event = .read bytes.length ∧ reader.readBytes = bytes := by
  have member : reader ∈ history.operations :=
    (List.mem_filter.mp (by rw [history.streams.reads]; simp)).1
  refine ⟨?_, history.streams.reads, history.streams.readEvent, history.streams.readBytes⟩
  rw [history.steps]
  exact List.mem_append_right _ member

theorem Complete.exact_chunks (history : Complete initial current actor bytes reader) :
    (history.operations.filter nonemptyRelease).flatMap ApplicationTrace.Step.releasedPayload = bytes ∧
      ∀ operation ∈ history.operations.filter nonemptyRelease, operation ∈ applicationSteps current.endpoints actor := by
  refine ⟨(release_chunks history.operations).trans history.streams.releaseStream, ?_⟩
  intro operation member
  rw [history.steps]
  exact List.mem_append_right _ (List.mem_filter.mp member).1

end Netlib.Check.CampusTCPTwoProgressHistory
