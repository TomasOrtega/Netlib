import Netlib.Check.CampusTCPRecoveryRoundHistory
import Netlib.Check.CampusTCPGapProgressPhaseBase

/-!
# Stream changes after an actual held-gap cut

The selected task appends to both existing endpoint histories.
Earlier reads and releases remain outside the selected stream change.
-/

namespace Netlib.Check.CampusTCPGapProgressHistory

open Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
namespace R
export CampusTCPRecoveryRoundHistory (Streams ReadStreams nonemptyRelease)
end R

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {initial before current : Cut input complete} {actor : Actor} {bytes : List UInt8} {released : Bool}

structure History (initial current : Cut input complete) (actor : Actor) (bytes : List UInt8) (released : Bool) where
  operations : List T.Step
  steps : applicationSteps current.endpoints actor = applicationSteps initial.endpoints actor ++ operations
  streams : R.Streams bytes operations released

structure Complete (initial current : Cut input complete) (actor : Actor) (bytes : List UInt8) (reader : T.Step) where
  operations : List T.Step
  steps : applicationSteps current.endpoints actor = applicationSteps initial.endpoints actor ++ operations
  streams : R.ReadStreams bytes operations reader

variable {reader : T.Step}

def History.ofCut (cut : Cut input complete) (actor : Actor) (bytes : List UInt8) :
    History cut cut actor bytes false := by
  refine ⟨[], by simp, none, rfl, rfl, rfl, rfl, rfl, ?_⟩
  intro operation absent
  cases absent

def History.same (history : History initial before actor bytes released)
    (steps : applicationSteps current.endpoints actor = applicationSteps before.endpoints actor) :
    History initial current actor bytes released :=
  ⟨history.operations, steps.trans history.steps, history.streams⟩

theorem clock_delta (placement : CampusTCPRecoveryRoundPhaseBase.At before current) (actor : Actor) :
    let extra := (applicationSteps current.endpoints actor).drop (applicationSteps before.endpoints actor).length
    applicationSteps current.endpoints actor = applicationSteps before.endpoints actor ++ extra ∧
      ∀ operation ∈ extra, ∃ now, operation.event = .advanceClock now := by
  obtain ⟨extra, steps, clocks⟩ := Netlib.Check.CampusTCPRecoveryRoundHistory.At.application_history placement actor
  simp only [steps, List.drop_left]
  exact ⟨True.intro, clocks⟩

def History.clock (history : History initial before actor bytes released)
    (placement : CampusTCPRecoveryRoundPhaseBase.At before current) : History initial current actor bytes released := by
  let extra := (applicationSteps current.endpoints actor).drop (applicationSteps before.endpoints actor).length
  have properties := clock_delta placement actor
  refine ⟨history.operations ++ extra, ?_, history.streams.clocks_append extra properties.2⟩
  exact properties.1.trans ((congrArg (fun operations => operations ++ extra) history.steps).trans
    (List.append_assoc _ _ _))

def History.quiet (history : History initial before actor bytes released) (operation : T.Step)
    (steps : applicationSteps current.endpoints actor = applicationSteps before.endpoints actor ++ [operation])
    (release : operation.releasedPayload = []) (read : operation.readBytes = []) :
    History initial current actor bytes released := by
  refine ⟨history.operations ++ [operation], ?_, history.streams.quiet_append operation release read⟩
  rw [steps, history.steps, List.append_assoc]

def History.first (history : History initial before actor bytes false) (operation : T.Step)
    (steps : applicationSteps current.endpoints actor = applicationSteps before.endpoints actor ++ [operation])
    (nonempty : bytes ≠ []) (release : operation.releasedPayload = bytes) (read : operation.readBytes = []) :
    History initial current actor bytes true := by
  refine ⟨history.operations ++ [operation], ?_, history.streams.first_append operation nonempty release read⟩
  rw [steps, history.steps, List.append_assoc]

def History.read (history : History initial before actor bytes true) (operation : T.Step)
    (steps : applicationSteps current.endpoints actor = applicationSteps before.endpoints actor ++ [operation])
    (nonempty : bytes ≠ []) (event : operation.event = .read bytes.length) (read : operation.readBytes = bytes) :
    Complete initial current actor bytes operation := by
  refine ⟨history.operations ++ [operation], ?_, history.streams.read_append operation nonempty event read⟩
  rw [steps, history.steps, List.append_assoc]

def Complete.clock (history : Complete initial before actor bytes reader)
    (placement : CampusTCPRecoveryRoundPhaseBase.At before current) : Complete initial current actor bytes reader := by
  let extra := (applicationSteps current.endpoints actor).drop (applicationSteps before.endpoints actor).length
  have properties := clock_delta placement actor
  refine ⟨history.operations ++ extra, ?_, history.streams.clocks_append extra properties.2⟩
  exact properties.1.trans ((congrArg (fun operations => operations ++ extra) history.steps).trans
    (List.append_assoc _ _ _))

theorem Complete.exact_release (history : Complete initial current actor bytes reader) :
    ∃ operation ∈ applicationSteps current.endpoints actor,
      history.operations.filter R.nonemptyRelease = [operation] ∧ operation.releasedPayload = bytes := by
  obtain ⟨operation, member, only, payload⟩ := history.streams.exact_release
  refine ⟨operation, ?_, only, payload⟩
  rw [history.steps]
  exact List.mem_append_right _ member

theorem Complete.exact_read (history : Complete initial current actor bytes reader) :
    reader ∈ applicationSteps current.endpoints actor ∧
      history.operations.filter CampusTCPRoundPhaseHistory.nonemptyRead = [reader] ∧
      reader.event = .read bytes.length ∧ reader.readBytes = bytes := by
  obtain ⟨member, only, event, payload⟩ := history.streams.exact_read
  refine ⟨?_, only, event, payload⟩
  rw [history.steps]
  exact List.mem_append_right _ member

end Netlib.Check.CampusTCPGapProgressHistory
