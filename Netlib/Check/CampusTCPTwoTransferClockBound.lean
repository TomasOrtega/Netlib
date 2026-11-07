import Netlib.Check.CampusTCPTwoTransferSources
import Netlib.Check.CampusTCPTwoTransferMonitor
import Netlib.Check.CampusTCPTwoExchangeClockBound

/-!
# Actual endpoint clock bounds during transfer

Each allowed clock input advances by at most one quantum.
Current moves retain the actual cuts across controls and primary service.
-/

namespace Netlib.Check.CampusTCPTwoTransferClockBound

open Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPRoundPhaseBase (Move)

namespace M
export CampusTCPTwoTransferMonitor (Config Monitor Allowed observe actions)
end M
namespace X
export CampusTCPTwoExchangeMonitor (Allowed)
end X
namespace A
export CampusTCPTwoProgressSuffixAge (nowAt nowAt_cut)
end A
namespace S
export CampusTCPSchedule (stateAt)
end S

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current next : Cut input complete} {actual : Step input}
variable {cfg : M.Config} {monitor : M.Monitor}

theorem allowed_clock (cfg : M.Config) (state : State input) (monitor : M.Monitor)
    (actor : Actor) (millis : Nat) (allowed : M.Allowed cfg state monitor (.advanceClock actor millis)) :
    X.Allowed (cfg.at state) state monitor.exchange (.advanceClock actor millis) := by
  by_cases invalid : monitor.mode = .invalid
  · simp only [M.Allowed, CampusTCPTwoTransferMonitor.allowed, invalid, decide_true, ite_true,
      Bool.false_eq_true] at allowed
  · cases drain : CampusTCPTwoTransferMonitor.drainTicket state monitor with
    | some ticket =>
      simpa only [M.Allowed, CampusTCPTwoTransferMonitor.allowed, invalid, decide_false,
        Bool.false_eq_true, ite_false, drain, X.Allowed] using allowed
    | none =>
      cases selected : CampusTCPTwoTransferMonitor.controlDemand monitor <;>
        simpa only [M.Allowed, CampusTCPTwoTransferMonitor.allowed, invalid, decide_false,
          Bool.false_eq_true, ite_false, drain, selected, X.Allowed] using allowed

theorem Move.local_clock_bound (move : Move current actual)
    (allowed : M.Allowed cfg current.report.final monitor actual.event) (actor : Actor) (operation : T.Step)
    (member : operation ∈ CampusTCPRecoveryRoundOrigins.localSteps actual.result.application actor) :
    CampusTCPTwoProgressClockAge.ClockBound cfg.exchange.forward.quantum operation := by
  have recorded := (CampusTCPRecoveryRoundOrigins.mem_localSteps _ _ _).mp member
  intro millis event
  have selected := CampusTCPTwoProgressSuffixAge.Step.clock_origin actual actor operation recorded millis event
  have ordinary := allowed_clock cfg current.report.final monitor actor millis (by rw [← selected]; exact allowed)
  exact CampusTCPTwoExchangeClockBound.Move.local_clock_bound move (cfg.at current.report.final)
    (by rw [selected]; exact ordinary) actor operation member millis event

theorem Move.actor_now_le (move : Move current actual)
    (allowed : M.Allowed cfg current.report.final monitor actual.event) (actor : Actor) :
    (endpoint move.after.endpoints actor).now ≤
      (endpoint current.endpoints actor).now + cfg.exchange.forward.quantum := by
  have upper := CampusTCPTwoProgressClockAge.Chain.now_le_length
    (CampusTCPTwoProgressSuffixAge.Move.application_chain move actor)
    (fun operation member => Move.local_clock_bound move allowed actor operation member)
  have count := CampusTCPTwoProgressSuffixAge.local_count_le [actual] actor
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.length_cons, List.length_nil] at count
  have bound := Nat.mul_le_mul_right cfg.exchange.forward.quantum count
  simp only [Nat.zero_add, Nat.one_mul] at bound
  exact Nat.le_trans upper (Nat.add_le_add_left bound _)

theorem Move.nowAt_le (move : Move current actual)
    (allowed : M.Allowed cfg current.report.final monitor actual.event) (actor : Actor) :
    A.nowAt move.after.report.final actor ≤ A.nowAt current.report.final actor + cfg.exchange.forward.quantum := by
  rw [A.nowAt_cut, A.nowAt_cut]
  exact Move.actor_now_le move allowed actor

theorem frame_now (frame : CampusTCPTwoTransferSources.Frame current next) (actor : Actor) :
    (endpoint next.endpoints actor).now = (endpoint current.endpoints actor).now := by rw [frame.endpoints]

theorem control_now (value : CampusTCPTransferEnabled.Control current event actual) (actor : Actor) :
    (endpoint value.move.after.endpoints actor).now = (endpoint current.endpoints actor).now :=
  frame_now (CampusTCPTwoTransferSources.Frame.control value) actor

theorem service_now
    (value : CampusTCPTwoTransferNetwork.Service current item hit session actual served emission emitted) (actor : Actor) :
    (endpoint value.move.after.endpoints actor).now = (endpoint current.endpoints actor).now :=
  frame_now (CampusTCPTwoTransferSources.Frame.service value) actor

inductive MoveChain : Cut input complete → List (Step input) → Cut input complete → Prop where
  | nil (current : Cut input complete) : MoveChain current [] current
  | cons {current final : Cut input complete} {actual : Step input} {rest : List (Step input)}
      (move : Move current actual) (tail : MoveChain move.after rest final) : MoveChain current (actual :: rest) final

variable {steps : List (Step input)} {last : Cut input complete}

theorem MoveChain.history (chain : MoveChain cut steps last) : last.report.steps = cut.report.steps ++ steps := by
  induction chain with
  | nil => simp
  | cons move _ ih => rw [ih, move.history]; simp only [List.append_assoc, List.singleton_append]

theorem MoveChain.trace (chain : MoveChain cut steps last) :
    Trace input cut.report.final (steps.map (·.event)) steps last.report.final [] := by
  induction chain with
  | nil => exact .done _
  | cons move _ ih =>
    rw [← move.beforeEq]
    exact .next _ move.supported (by rw [← move.final]; exact ih)

theorem MoveChain.now_le (chain : MoveChain cut steps last)
    (actions : M.actions cfg cut.report.final monitor steps = true) (actor : Actor) :
    (endpoint last.endpoints actor).now ≤
      (endpoint cut.endpoints actor).now + steps.length * cfg.exchange.forward.quantum := by
  induction chain generalizing monitor with
  | nil => simp
  | cons move _ ih =>
    have parts := Bool.and_eq_true_iff.mp actions
    have upper := Move.actor_now_le move parts.1 actor
    have later := ih (by simpa only [move.final] using parts.2)
    simp only [List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

theorem MoveChain.take (chain : MoveChain cut steps last) (slot : Nat) (within : slot ≤ steps.length) :
    ∃ current : Cut input complete, current.report.final = S.stateAt cut.report.final steps slot ∧
      MoveChain cut (steps.take slot) current := by
  induction chain generalizing slot with
  | nil current =>
    have zero : slot = 0 := by simpa only [List.length_nil, Nat.le_zero] using within
    subst slot
    exact ⟨current, rfl, .nil _⟩
  | cons move tail ih =>
    cases slot with
    | zero => exact ⟨_, rfl, .nil _⟩
    | succ slot =>
      obtain ⟨current, same, earlier⟩ := ih slot (by simpa only [List.length_cons, Nat.add_le_add_iff_right] using within)
      refine ⟨current, ?_, ?_⟩
      · simpa only [S.stateAt, move.final] using same
      · exact .cons move earlier

theorem actions_take (cfg : M.Config) (state : State input) (monitor : M.Monitor) (steps : List (Step input))
    (actions : M.actions cfg state monitor steps = true) (slot : Nat) :
    M.actions cfg state monitor (steps.take slot) = true := by
  induction steps generalizing state monitor slot with
  | nil => simp only [List.take_nil, M.actions]
  | cons actual rest ih =>
    cases slot with
    | zero => rfl
    | succ slot =>
      have parts := Bool.and_eq_true_iff.mp actions
      simp only [List.take_succ_cons, M.actions, Bool.and_eq_true]
      exact ⟨parts.1, ih _ _ parts.2 slot⟩

theorem MoveChain.prefix_now_le (chain : MoveChain cut steps last)
    (actions : M.actions cfg cut.report.final monitor steps = true)
    (slot : Nat) (within : slot ≤ steps.length) (actor : Actor) :
    A.nowAt (S.stateAt cut.report.final steps slot) actor ≤
      (endpoint cut.endpoints actor).now + slot * cfg.exchange.forward.quantum := by
  obtain ⟨current, same, earlier⟩ := chain.take slot within
  have upper := earlier.now_le (actions_take cfg cut.report.final monitor steps actions slot) actor
  rw [List.length_take, Nat.min_eq_left within] at upper
  rw [← same, A.nowAt_cut]
  exact upper

theorem MoveChain.cut_now (chain : MoveChain cut steps last)
    (actions : M.actions cfg cut.report.final monitor steps = true) (slot : Nat) (within : slot ≤ steps.length) :
    ∃ current : Cut input complete, current.report.final = S.stateAt cut.report.final steps slot ∧
      current.report.steps = cut.report.steps ++ steps.take slot ∧ MoveChain cut (steps.take slot) current ∧
      ∀ actor, (endpoint current.endpoints actor).now ≤
        (endpoint cut.endpoints actor).now + slot * cfg.exchange.forward.quantum := by
  obtain ⟨current, same, earlier⟩ := chain.take slot within
  refine ⟨current, same, earlier.history, earlier, ?_⟩
  intro actor
  have upper := chain.prefix_now_le actions slot within actor
  rw [← same, A.nowAt_cut] at upper
  exact upper

theorem MoveChain.original_ages (chain : MoveChain cut steps last)
    (actions : M.actions cfg cut.report.final monitor steps = true) (slot : Nat) (within : slot ≤ steps.length)
    (same : current.report.final = S.stateAt cut.report.final steps slot)
    (initial : CampusTCPTwoProgressStart.TwoWriteInitial cut sender gateway lower upper)
    (sent : CampusTCPTwoProgressSender.Stage initial) (times : CampusTCPTwoProgressPhaseBase.OriginalTimes initial sent) :
    CampusTCPTwoProgressSuffixAge.OriginalAges initial (endpoint current.endpoints sender).now
      (slot * cfg.exchange.forward.quantum) sent := by
  have upper := chain.prefix_now_le actions slot within sender
  rw [← same, A.nowAt_cut] at upper
  cases sent <;> simp only [CampusTCPTwoProgressSuffixAge.OriginalAges,
    CampusTCPTwoProgressPhaseBase.OriginalTimes] at * <;> omega

end Netlib.Check.CampusTCPTwoTransferClockBound
