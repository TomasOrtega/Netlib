import Netlib.Check.CampusTCPTwoExchangeRecorded
import Netlib.Check.CampusTCPTwoProgressSuffixAge

/-!
# Clock bounds for the stored exchange suffix

Each actual clock input advances by at most one quantum.
-/

namespace Netlib.Check.CampusTCPTwoExchangeClockBound

open Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPRoundPhaseBase (Move)
open CampusTCPTwoProgressStart
open CampusTCPTwoExchangeSetup (config)

namespace M
export CampusTCPTwoExchangeMonitor (Config Monitor Allowed monitorAt)
end M

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current : Cut input complete} {sender : Actor} {gateway : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {native : NativeEnv cut gateway initial.gatewayState.session.entry} {quantum allowance : Nat}
variable {reverseLower reverseUpper : List UInt8} {monitor : M.Monitor}

theorem allowed_not_enableStartupRecovery (cfg : M.Config) (state : State input) (monitor : M.Monitor) (actor : Actor) :
    ¬M.Allowed cfg state monitor (.enableStartupRecovery actor) := by
  intro allowed
  cases mode : monitor.mode with
  | forward =>
    exact CampusTCPTwoProgressSuffixAge.allowed_not_enableStartupRecovery cfg.forward state monitor.forward actor
      (by simpa only [M.Allowed, CampusTCPTwoExchangeMonitor.allowed, mode,
        CampusTCPTwoProgressMonitor.Allowed] using allowed)
  | reverse =>
    exact CampusTCPTwoProgressSuffixAge.allowed_not_enableStartupRecovery
      (cfg.reverse monitor.forward.drops.length) state monitor.reverse actor
      (by simpa only [M.Allowed, CampusTCPTwoExchangeMonitor.allowed, mode,
        CampusTCPTwoProgressMonitor.Allowed] using allowed)
  | needWrite | done | invalid =>
    simp only [M.Allowed, CampusTCPTwoExchangeMonitor.allowed, mode, Bool.false_eq_true] at allowed

private theorem clock_local_allowed (cfg : M.Config) (current : Cut input complete) (monitor : M.Monitor)
    (actor : Actor) (millis : Nat) (allowed : M.Allowed cfg current.report.final monitor (.advanceClock actor millis)) :
    CampusTCPTwoProgressMonitor.Allowed cfg.forward current.report.final monitor.forward (.advanceClock actor millis) ∨
      CampusTCPTwoProgressMonitor.Allowed (cfg.reverse monitor.forward.drops.length) current.report.final
        monitor.reverse (.advanceClock actor millis) := by
  cases mode : monitor.mode with
  | forward | needWrite =>
    left
    simpa only [M.Allowed, CampusTCPTwoExchangeMonitor.allowed, mode, CampusTCPTwoProgressMonitor.Allowed] using allowed
  | reverse | done =>
    right
    simpa only [M.Allowed, CampusTCPTwoExchangeMonitor.allowed, mode, CampusTCPTwoProgressMonitor.Allowed] using allowed
  | invalid => simp only [M.Allowed, CampusTCPTwoExchangeMonitor.allowed, mode, Bool.false_eq_true] at allowed

theorem Move.local_clock_bound (move : Move current actual) (cfg : M.Config)
    (allowed : M.Allowed cfg current.report.final monitor actual.event) (actor : Actor) (operation : T.Step)
    (member : operation ∈ CampusTCPRecoveryRoundOrigins.localSteps actual.result.application actor) :
    CampusTCPTwoProgressClockAge.ClockBound cfg.forward.quantum operation := by
  have recorded := (CampusTCPRecoveryRoundOrigins.mem_localSteps _ _ _).mp member
  constructor
  · intro millis event
    have selected := CampusTCPTwoProgressSuffixAge.Step.clock_origin actual actor operation recorded millis event
    rcases clock_local_allowed cfg current monitor actor millis (by rw [← selected]; exact allowed) with old | reverse
    · exact (CampusTCPTwoProgressSuffixAge.Move.local_clock_bound move cfg.forward
        (by rw [selected]; exact old) actor operation member).1 millis event
    · exact (CampusTCPTwoProgressSuffixAge.Move.local_clock_bound move (cfg.reverse monitor.forward.drops.length)
        (by rw [selected]; exact reverse) actor operation member).1 millis event
  · intro data event
    have selected := CampusTCPTwoProgressSuffixAge.Step.startupRecovery_origin actual actor operation recorded data event
    exact False.elim (allowed_not_enableStartupRecovery cfg current.report.final monitor actor (selected ▸ allowed))

theorem Move.actor_now_le (move : Move current actual) (cfg : M.Config)
    (allowed : M.Allowed cfg current.report.final monitor actual.event) (actor : Actor) :
    (endpoint move.after.endpoints actor).now ≤ (endpoint current.endpoints actor).now + cfg.forward.quantum := by
  have upper := CampusTCPTwoProgressClockAge.Chain.now_le_length
    (CampusTCPTwoProgressSuffixAge.Move.application_chain move actor)
    (fun operation member => Move.local_clock_bound move cfg allowed actor operation member)
  have count := CampusTCPTwoProgressSuffixAge.local_count_le [actual] actor
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.length_cons, List.length_nil] at count
  have bound := Nat.mul_le_mul_right cfg.forward.quantum count
  simp only [Nat.zero_add, Nat.one_mul] at bound
  exact Nat.le_trans upper (Nat.add_le_add_left bound _)

theorem Move.nowAt_le (move : Move current actual) (cfg : M.Config)
    (allowed : M.Allowed cfg current.report.final monitor actual.event) (actor : Actor) :
    CampusTCPTwoProgressSuffixAge.nowAt move.after.report.final actor ≤
      CampusTCPTwoProgressSuffixAge.nowAt current.report.final actor + cfg.forward.quantum := by
  rw [CampusTCPTwoProgressSuffixAge.nowAt_cut, CampusTCPTwoProgressSuffixAge.nowAt_cut]
  exact Move.actor_now_le move cfg allowed actor

variable {suffix remaining : List Event} {steps : List (Step input)} {final : State input}

theorem trace_now_le (trace : Trace input cut.report.final suffix steps final remaining)
    (actions : CampusTCPTwoExchangeRecorded.Actions initial native quantum allowance reverseLower reverseUpper steps)
    (budget : allowance ≤ 2) (endpointReserve : CampusTCPTwoReverseReserves.Initial initial reverseLower reverseUpper)
    (gatewayReserve : CampusTCPTwoReverseGeometry.Initial initial reverseLower reverseUpper)
    (lowerNonempty : reverseLower ≠ []) (upperNonempty : reverseUpper ≠ [])
    (slot : Nat) (within : slot ≤ steps.length) (actor : Actor) :
    CampusTCPTwoProgressSuffixAge.nowAt (CampusTCPSchedule.stateAt cut.report.final steps slot) actor ≤
      (endpoint cut.endpoints actor).now + slot * quantum := by
  induction slot with
  | zero =>
    simp only [CampusTCPSchedule.stateAt_zero, CampusTCPTwoProgressSuffixAge.nowAt_cut,
      Nat.zero_mul, Nat.add_zero, Nat.le_refl]
  | succ slot ih =>
    obtain ⟨current, same, _, ⟨evidence⟩⟩ := CampusTCPTwoExchangeRecorded.trace_at budget endpointReserve
      gatewayReserve lowerNonempty upperNonempty trace actions slot (by omega)
    obtain ⟨actual, _, before, event, after⟩ := CampusTCPSchedule.Trace.at trace slot (by omega)
    have allowed : M.Allowed (config initial native quantum allowance reverseLower reverseUpper) current.report.final
        (M.monitorAt (config initial native quantum allowance reverseLower reverseUpper) .initial steps slot) actual.event := by
      rw [same, event]
      exact actions slot (by omega)
    obtain ⟨move, _⟩ := evidence.step budget endpointReserve gatewayReserve lowerNonempty upperNonempty
      actual (before.trans same.symm) allowed
    have tick := Move.nowAt_le move (config initial native quantum allowance reverseLower reverseUpper) allowed actor
    rw [move.final, after, same] at tick
    change CampusTCPTwoProgressSuffixAge.nowAt (CampusTCPSchedule.stateAt cut.report.final steps (slot + 1)) actor ≤
      CampusTCPTwoProgressSuffixAge.nowAt (CampusTCPSchedule.stateAt cut.report.final steps slot) actor + quantum at tick
    have prior := ih (by omega)
    simp only [Nat.add_mul, Nat.one_mul]
    omega

end Netlib.Check.CampusTCPTwoExchangeClockBound
