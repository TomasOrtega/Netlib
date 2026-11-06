import Netlib.Check.CampusTCPTwoProgressMonitorFacts
import Netlib.Check.CampusTCPGapProgressClock

/-!
# Actual guarded clock moves for two TCP records

The move extends the current report.
The monitor retains its packet references and service demand.
-/

namespace Netlib.Check.CampusTCPTwoProgressClock

open Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPGapProgressPhaseBase (Anchor Move At)

namespace M
export CampusTCPTwoProgressMonitor (Config Monitor Allowed clockAllowed observe)
end M

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {initial current : Cut input complete} {config : M.Config} {monitor : M.Monitor}
variable {actor : Actor} {millis : Nat} {actual : Step input}

theorem allowed_guard (config : M.Config) (current : Cut input complete) (monitor : M.Monitor)
    (actor : Actor) (millis : Nat)
    (allowed : M.Allowed config current.report.final monitor (.advanceClock actor millis)) :
    M.clockAllowed config current.report.final (.advanceClock actor millis) = true :=
  ((CampusTCPTwoProgressMonitorFacts.allowed_iff config current.report.final monitor _).mp allowed).2.2

structure Clocked (initial current : Cut input complete) (config : M.Config) (monitor : M.Monitor)
    (actor : Actor) (millis : Nat) (actual : Step input) where
  base : CampusTCPGapProgressClock.Clocked initial current config.toConfig {} actor millis actual
  observed : M.observe config monitor actual = monitor

theorem clock_at (anchor : Anchor initial current) (config : M.Config) (monitor : M.Monitor)
    (actor : Actor) (millis : Nat)
    (allowed : M.Allowed config current.report.final monitor (.advanceClock actor millis)) :
    ∃ actual : Step input, Nonempty (Clocked initial current config monitor actor millis actual) := by
  obtain ⟨actual, ⟨base⟩⟩ := CampusTCPGapProgressClock.clock_at anchor config.toConfig {} actor millis
    (allowed_guard config current monitor actor millis allowed)
  refine ⟨actual, ⟨⟨base, ?_⟩⟩⟩
  apply CampusTCPTwoProgressMonitorFacts.observe_clock config monitor actual base.move.supported base.move.passed
  · simpa only [base.move.beforeEq, base.event] using allowed
  · exact base.event

theorem Step.clock (actual : Step input) (anchor : Anchor initial current) (config : M.Config) (monitor : M.Monitor)
    (actor : Actor) (millis : Nat) (before : actual.before = current.report.final)
    (event : actual.event = .advanceClock actor millis)
    (allowed : M.Allowed config current.report.final monitor (.advanceClock actor millis)) :
    Nonempty (Clocked initial current config monitor actor millis actual) := by
  obtain ⟨selected, ⟨clocked⟩⟩ := clock_at anchor config monitor actor millis allowed
  have same := CampusTCPRoundPhaseBase.Step.eq_of_before_event selected actual
    (clocked.base.move.beforeEq.trans before.symm) (clocked.base.event.trans event.symm)
  exact ⟨same ▸ clocked⟩

def Clocked.move (clocked : Clocked initial current config monitor actor millis actual) : Move current actual :=
  clocked.base.move

theorem Clocked.event (clocked : Clocked initial current config monitor actor millis actual) :
    actual.event = .advanceClock actor millis := clocked.base.event

theorem Clocked.placement (clocked : Clocked initial current config monitor actor millis actual) :
    At current clocked.move.after := clocked.base.placement

theorem Clocked.anchor (clocked : Clocked initial current config monitor actor millis actual) :
    Anchor initial clocked.move.after := clocked.base.anchor

theorem Clocked.selected (clocked : Clocked initial current config monitor actor millis actual) :
    endpoint clocked.move.after.endpoints actor = Endpoint.clockState (endpoint current.endpoints actor) millis :=
  clocked.base.selected

theorem Clocked.peer (clocked : Clocked initial current config monitor actor millis actual) :
    endpoint clocked.move.after.endpoints actor.other = endpoint current.endpoints actor.other := clocked.base.peer

end Netlib.Check.CampusTCPTwoProgressClock
