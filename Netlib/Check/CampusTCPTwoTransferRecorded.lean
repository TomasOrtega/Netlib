import Netlib.Check.CampusTCPTwoTransferClockBound
import Netlib.Check.CampusTCPTwoTransferLossHistory

/-!
# One recorded prefix for the transfer task

The same actual moves provide the trace, action checks, and clock bounds.
Appending a step keeps the original cut and observer fold.
-/

namespace Netlib.Check.CampusTCPTwoTransferRecorded

open Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPRoundPhaseBase (Move)
open CampusTCPTwoTransferClockBound (MoveChain)

namespace W
export CampusTCPTwoTransferMonitor (Config Monitor Allowed actions observe)
end W

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current next final : Cut input complete} {actual : Step input}
variable {config : W.Config} {monitor : W.Monitor} {steps : List (Step input)}

theorem MoveChain.append (first : MoveChain cut steps current) (second : MoveChain current later final) :
    MoveChain cut (steps ++ later) final := by
  induction first with
  | nil => exact second
  | cons move tail ih => exact .cons move (ih second)

theorem MoveChain.snoc (chain : MoveChain cut steps current) (move : Move current actual) :
    MoveChain cut (steps ++ [actual]) move.after := MoveChain.append chain (.cons move (.nil _))

theorem actions_snoc (chain : MoveChain cut steps current)
    (actions : W.actions config cut.report.final monitor steps = true)
    (move : Move current actual)
    (allowed : W.Allowed config current.report.final (steps.foldl (W.observe config) monitor) actual.event) :
    W.actions config cut.report.final monitor (steps ++ [actual]) = true := by
  induction chain generalizing monitor with
  | nil =>
    simpa only [List.nil_append, W.actions, List.foldl_nil, Bool.and_true, W.Allowed] using allowed
  | cons first tail ih =>
    have checked := Bool.and_eq_true_iff.mp actions
    change (_ && W.actions config _ _ _) = true
    apply Bool.and_eq_true_iff.mpr
    refine ⟨checked.1, ?_⟩
    rw [← first.final]
    exact ih (by simpa only [first.final] using checked.2) move allowed

structure Recorded (cut : Cut input complete) (config : W.Config)
    (current : Cut input complete) (monitor : W.Monitor) where
  suffix : List (Step input)
  chain : MoveChain cut suffix current
  observed : suffix.foldl (W.observe config) .initial = monitor
  actions : W.actions config cut.report.final .initial suffix = true

def Recorded.empty (cut : Cut input complete) (config : W.Config) : Recorded cut config cut .initial :=
  ⟨[], .nil cut, rfl, rfl⟩

def Recorded.snoc (recorded : Recorded cut config current monitor) (move : Move current actual)
    (allowed : W.Allowed config current.report.final monitor actual.event) :
    Recorded cut config move.after (W.observe config monitor actual) :=
  ⟨recorded.suffix ++ [actual], MoveChain.snoc recorded.chain move,
    by rw [List.foldl_append, recorded.observed]; rfl,
    actions_snoc recorded.chain recorded.actions move (by rw [recorded.observed]; exact allowed)⟩

theorem Recorded.history (recorded : Recorded cut config current monitor) :
    current.report.steps = cut.report.steps ++ recorded.suffix := recorded.chain.history

theorem Recorded.trace (recorded : Recorded cut config current monitor) :
    Trace input cut.report.final (recorded.suffix.map (·.event)) recorded.suffix current.report.final [] :=
  recorded.chain.trace

theorem Recorded.suffix_unique (left : Recorded cut config current monitor)
    (right : Recorded cut config current monitor) : left.suffix = right.suffix := by
  apply List.append_cancel_left
  exact left.history.symm.trans right.history

theorem Recorded.loss_suffix
    {initial : CampusTCPTwoProgressStart.TwoWriteInitial cut sender gateway lower upper} (recorded : Recorded cut config current monitor)
    (history : CampusTCPTwoTransferLossHistory.History initial config current monitor) :
    recorded.suffix = history.suffix := by
  apply List.append_cancel_left
  exact recorded.history.symm.trans history.steps

theorem Recorded.now_le (recorded : Recorded cut config current monitor) (actor : Actor) :
    (endpoint current.endpoints actor).now ≤
      (endpoint cut.endpoints actor).now + recorded.suffix.length * config.exchange.forward.quantum :=
  recorded.chain.now_le recorded.actions actor

theorem Recorded.cut_now (recorded : Recorded cut config current monitor)
    (slot : Nat) (within : slot ≤ recorded.suffix.length) :
    ∃ next : Cut input complete,
      next.report.final = CampusTCPSchedule.stateAt cut.report.final recorded.suffix slot ∧
      next.report.steps = cut.report.steps ++ recorded.suffix.take slot ∧
      MoveChain cut (recorded.suffix.take slot) next ∧
      ∀ actor, (endpoint next.endpoints actor).now ≤
        (endpoint cut.endpoints actor).now + slot * config.exchange.forward.quantum :=
  recorded.chain.cut_now recorded.actions slot within

end Netlib.Check.CampusTCPTwoTransferRecorded
