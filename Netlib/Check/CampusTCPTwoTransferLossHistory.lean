import Netlib.Check.CampusTCPTwoTransferLoss

/-!
# One actual loss history through transfer

The same suffix records controls, drains, drops, and timeout outputs.
Each timeout spends a distinct earlier cause for its actual current head.
-/

namespace Netlib.Check.CampusTCPTwoTransferLossHistory

open Protocol Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPRoundPhaseBase (Move)
open CampusTCPTwoProgressStart
open CampusTCPTwoTransferLoss
open CampusTCPTwoProgressLossHistory (Head isDrop dropID)
open CampusTCPTwoExchangeLoss (isTimeoutOutput)

namespace W
export CampusTCPTwoTransferMonitor (Config Monitor observe)
end W
namespace S
export CampusTCPTwoProgressSender (Part)
end S

local notation "Config" => CampusTCPTwoTransferMonitor.Config

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current next : Cut input complete} {sender : Actor} {gateway : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper} {config : Config}
variable {monitor : W.Monitor} {actual : Step input} {id : Nat}

structure History (initial : TwoWriteInitial cut sender gateway lower upper) (config : Config)
    (current : Cut input complete) (monitor : W.Monitor) where
  suffix : List (Step input)
  steps : current.report.steps = cut.report.steps ++ suffix
  observed : suffix.foldl (W.observe config) .initial = monitor
  book : Book initial config
  valid : book.Valid
  dropSteps : suffix.filter isDrop = book.losses.map (·.actual)
  timeoutSteps : suffix.filter isTimeoutOutput = book.spent.map (·.actual)
  dropIDs : monitor.exchange.forward.drops = book.losses.map (·.id)
  retries : book.spent.length = monitor.exchange.forward.retries
  wholeDropIDs : monitor.exchange.drops = book.losses.map (·.id)
  wholeTimeouts : monitor.exchange.timeouts = book.spent.length
  lossesPast : ∀ loss ∈ book.losses, loss.move.after.report.steps <+: current.report.steps
  timeoutsPast : ∀ entry ∈ book.spent, entry.move.after.report.steps <+: current.report.steps

def History.empty (initial : TwoWriteInitial cut sender gateway lower upper) (config : Config) :
    History initial config cut .initial where
  suffix := []
  steps := (List.append_nil _).symm
  observed := rfl
  book := Book.empty initial config
  valid := Book.empty_valid initial config
  dropSteps := rfl
  timeoutSteps := rfl
  dropIDs := rfl
  retries := rfl
  wholeDropIDs := rfl
  wholeTimeouts := rfl
  lossesPast := by simp [Book.empty]
  timeoutsPast := by simp [Book.empty]

theorem History.count (history : History initial config current monitor) :
    monitor.exchange.forward.retries ≤ monitor.exchange.forward.drops.length := by
  rw [← history.retries, history.dropIDs, List.length_map]
  exact history.valid.spent_le

theorem History.credit (history : History initial config current monitor)
    (chosen : history.book.cause role = some position) :
    monitor.exchange.forward.retries < monitor.exchange.forward.drops.length := by
  rw [← history.retries, history.dropIDs, List.length_map]
  exact history.valid.cause_credit chosen

private theorem filtered_drop_ids (steps : List (Step input)) :
    steps.filterMap dropID = (steps.filter isDrop).filterMap dropID := by
  induction steps with
  | nil => rfl
  | cons actual rest ih => cases event : actual.event <;>
      simp only [List.filterMap_cons, List.filter_cons, dropID, isDrop, event, Bool.false_eq_true,
        ite_false, ite_true, ih]

private theorem loss_drop_ids (losses : List (Loss initial config)) :
    (losses.map (·.actual)).filterMap dropID = losses.map (·.id) := by
  induction losses with
  | nil => rfl
  | cons loss rest ih => simp only [List.map_cons, List.filterMap_cons, dropID, loss.facts.event, ih]

theorem History.actual_ids (history : History initial config current monitor) :
    history.suffix.filterMap dropID = monitor.exchange.drops := by
  rw [filtered_drop_ids, history.dropSteps, loss_drop_ids, history.wholeDropIDs]

theorem History.actual_drop_count (history : History initial config current monitor) :
    (history.suffix.filter isDrop).length = monitor.exchange.drops.length := by
  rw [history.dropSteps, history.wholeDropIDs, List.length_map, List.length_map]

theorem History.actual_timeout_count (history : History initial config current monitor) :
    (history.suffix.filter isTimeoutOutput).length = monitor.exchange.timeouts := by
  rw [history.timeoutSteps, List.length_map, history.wholeTimeouts]

theorem History.actual_budget (history : History initial config current monitor)
    (bound : monitor.exchange.drops.length ≤ allowance) :
    (history.suffix.filter isTimeoutOutput).length ≤ (history.suffix.filter isDrop).length ∧
      (history.suffix.filter isDrop).length ≤ allowance := by
  rw [history.actual_timeout_count, history.actual_drop_count, history.wholeTimeouts,
    history.wholeDropIDs, List.length_map]
  exact ⟨history.valid.spent_le, by simpa only [history.wholeDropIDs, List.length_map] using bound⟩

def History.reframe (history : History initial config current monitor) (same : next.report.steps = current.report.steps) :
    History initial config next monitor :=
  { history with
    steps := same.trans history.steps
    lossesPast := fun loss member => same.symm ▸ history.lossesPast loss member
    timeoutsPast := fun entry member => same.symm ▸ history.timeoutsPast entry member }

def History.append (history : History initial config current monitor) (move : Move current actual)
    (noDrop : isDrop actual = false) (noTimeout : isTimeoutOutput actual = false)
    (dropIDs : (W.observe config monitor actual).exchange.forward.drops = monitor.exchange.forward.drops)
    (retries : (W.observe config monitor actual).exchange.forward.retries = monitor.exchange.forward.retries)
    (wholeDropIDs : (W.observe config monitor actual).exchange.drops = monitor.exchange.drops)
    (wholeTimeouts : (W.observe config monitor actual).exchange.timeouts = monitor.exchange.timeouts) :
    History initial config move.after (W.observe config monitor actual) := by
  refine ⟨history.suffix ++ [actual], ?_, ?_, history.book, history.valid, ?_, ?_,
    dropIDs.trans history.dropIDs, history.retries.trans retries.symm,
    wholeDropIDs.trans history.wholeDropIDs, wholeTimeouts.trans history.wholeTimeouts, ?_, ?_⟩
  · rw [move.history, history.steps, List.append_assoc]
  · rw [List.foldl_append, history.observed]
    rfl
  · simp only [List.filter_append, List.filter_cons, noDrop, Bool.false_eq_true, ite_false,
      List.filter_nil, List.append_nil, history.dropSteps]
  · simp only [List.filter_append, List.filter_cons, noTimeout, Bool.false_eq_true, ite_false,
      List.filter_nil, List.append_nil, history.timeoutSteps]
  · exact fun loss member => (history.lossesPast loss member).trans move.retained
  · exact fun entry member => (history.timeoutsPast entry member).trans move.retained

def History.selectedLoss (history : History initial config current monitor) (move : Move current actual)
    (facts : CampusTCPRecoveryRoundDrop.Facts current.report.final id actual)
    (phase : monitor.exchange.mode = .forward)
    (selected : CampusTCPTwoProgressMonitor.dropTarget (config.at current.report.final).forward
      current.report.final monitor.exchange.forward id = some target)
    (allowed : CampusTCPTwoTransferMonitor.Allowed config current.report.final monitor actual.event) : Loss initial config where
  before := current
  monitor := monitor
  retained := by rw [history.steps]; exact List.prefix_append _ _
  observed := by rw [history.steps, List.drop_append_length]; exact history.observed
  actual := actual
  move := move
  id := id
  facts := facts
  phase := phase
  target := target
  selected := selected
  allowed := allowed

end Netlib.Check.CampusTCPTwoTransferLossHistory
