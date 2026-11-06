import Netlib.Check.CampusTCPTwoExchangeEvidenceStep

/-!
# Exact stored exchange prefixes

Each cut extends the initial report with the supplied steps.
Its phase evidence refers to that same cut.
-/

namespace Netlib.Check.CampusTCPTwoExchangeRecorded

open Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart
open CampusTCPTwoExchangeSetup (config)
open CampusTCPTwoExchangeEvidence (Evidence)

namespace M
export CampusTCPTwoExchangeMonitor (Monitor monitorAt observe Allowed)
end M
namespace S
export CampusTCPSchedule (stateAt eventAt)
end S
namespace L
export CampusTCPTwoProgressEvidence (Evidence Complete)
end L

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut : Cut input complete} {sender : Actor} {gateway : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {native : NativeEnv cut gateway initial.gatewayState.session.entry} {quantum allowance : Nat}
variable {reverseLower reverseUpper : List UInt8}
variable {suffix remaining : List Event} {steps : List (Step input)} {final : State input}

def Actions (initial : TwoWriteInitial cut sender gateway lower upper)
    (native : NativeEnv cut gateway initial.gatewayState.session.entry) (quantum allowance : Nat)
    (reverseLower reverseUpper : List UInt8) (steps : List (Step input)) : Prop :=
  ∀ slot, slot < steps.length → M.Allowed (config initial native quantum allowance reverseLower reverseUpper)
    (S.stateAt cut.report.final steps slot)
    (M.monitorAt (config initial native quantum allowance reverseLower reverseUpper) .initial steps slot)
    (S.eventAt steps slot)

private theorem take_next {values : List α} {index : Nat} {value : α} (found : values[index]? = some value) :
    values.take (index + 1) = values.take index ++ [value] := by
  induction values generalizing index with
  | nil => simp only [List.getElem?_nil] at found; cases found
  | cons head rest ih =>
    cases index with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at found
      subst value
      rfl
    | succ index => exact congrArg (List.cons head) (ih found)

theorem trace_at (budget : allowance ≤ 2)
    (endpointReserve : CampusTCPTwoReverseReserves.Initial initial reverseLower reverseUpper)
    (gatewayReserve : CampusTCPTwoReverseGeometry.Initial initial reverseLower reverseUpper)
    (lowerNonempty : reverseLower ≠ []) (upperNonempty : reverseUpper ≠ [])
    (trace : Trace input cut.report.final suffix steps final remaining)
    (actions : Actions initial native quantum allowance reverseLower reverseUpper steps)
    (slot : Nat) (within : slot ≤ steps.length) :
    ∃ current : Cut input complete, current.report.final = S.stateAt cut.report.final steps slot ∧
      current.report.steps = cut.report.steps ++ steps.take slot ∧
      Nonempty (Evidence initial native quantum allowance reverseLower reverseUpper current
        (M.monitorAt (config initial native quantum allowance reverseLower reverseUpper) .initial steps slot)) := by
  induction slot with
  | zero =>
    exact ⟨cut, (CampusTCPSchedule.stateAt_zero _ _).symm, (List.append_nil _).symm,
      by simpa only [CampusTCPTwoExchangeMonitor.monitorAt_zero] using
        Nonempty.intro (CampusTCPTwoExchangeEvidence.Evidence.ofInitial initial native quantum allowance reverseLower reverseUpper)⟩
  | succ slot ih =>
    obtain ⟨current, same, history, ⟨evidence⟩⟩ := ih (by omega)
    obtain ⟨actual, found, before, event, after⟩ := CampusTCPSchedule.Trace.at trace slot (by omega)
    have allowed : M.Allowed (config initial native quantum allowance reverseLower reverseUpper) current.report.final
        (M.monitorAt (config initial native quantum allowance reverseLower reverseUpper) .initial steps slot) actual.event := by
      rw [same, event]
      exact actions slot (by omega)
    obtain ⟨move, next⟩ := evidence.step budget endpointReserve gatewayReserve lowerNonempty upperNonempty
      actual (before.trans same.symm) allowed
    refine ⟨move.after, move.final.trans after, ?_, ?_⟩
    · rw [move.history, history, List.append_assoc, ← take_next found]
    · rw [CampusTCPTwoExchangeMonitor.monitorAt_next _ _ _ found]
      exact next

theorem trace_at_checked (budget : allowance ≤ 2)
    (endpointReserve : CampusTCPTwoReverseReserves.Initial initial reverseLower reverseUpper)
    (gatewayReserve : CampusTCPTwoReverseGeometry.Initial initial reverseLower reverseUpper)
    (lowerNonempty : reverseLower ≠ []) (upperNonempty : reverseUpper ≠ [])
    (trace : Trace input cut.report.final suffix steps final remaining)
    (actions : CampusTCPTwoExchangeMonitor.actions (config initial native quantum allowance reverseLower reverseUpper)
      cut.report.final .initial steps = true)
    (slot : Nat) (within : slot ≤ steps.length) :
    ∃ current : Cut input complete, current.report.final = S.stateAt cut.report.final steps slot ∧
      current.report.steps = cut.report.steps ++ steps.take slot ∧
      Nonempty (Evidence initial native quantum allowance reverseLower reverseUpper current
        (M.monitorAt (config initial native quantum allowance reverseLower reverseUpper) .initial steps slot)) :=
  trace_at budget endpointReserve gatewayReserve lowerNonempty upperNonempty trace
    ((CampusTCPTwoExchangeMonitor.actions_correct _ _ _ _).mp actions) slot within

theorem trace_healthy (budget : allowance ≤ 2)
    (endpointReserve : CampusTCPTwoReverseReserves.Initial initial reverseLower reverseUpper)
    (gatewayReserve : CampusTCPTwoReverseGeometry.Initial initial reverseLower reverseUpper)
    (lowerNonempty : reverseLower ≠ []) (upperNonempty : reverseUpper ≠ [])
    (trace : Trace input cut.report.final suffix steps final remaining)
    (actions : Actions initial native quantum allowance reverseLower reverseUpper steps)
    (slot : Nat) (within : slot ≤ steps.length) :
    (M.monitorAt (config initial native quantum allowance reverseLower reverseUpper) .initial steps slot).mode ≠ .invalid := by
  obtain ⟨_, _, _, ⟨evidence⟩⟩ :=
    trace_at budget endpointReserve gatewayReserve lowerNonempty upperNonempty trace actions slot within
  exact evidence.healthy

variable {current : Cut input complete} {monitor : M.Monitor}

theorem needWrite_value (value : Evidence initial native quantum allowance reverseLower reverseUpper current monitor)
    (mode : monitor.mode = .needWrite) : Nonempty (L.Complete initial native quantum allowance current monitor.forward) := by
  cases value with
  | needWrite forward _ => exact ⟨forward⟩
  | forward _ selected _ | reverse _ _ _ selected _ | done _ _ _ selected => rw [selected] at mode; cases mode

theorem reverse_value (value : Evidence initial native quantum allowance reverseLower reverseUpper current monitor)
    (mode : monitor.mode = .reverse) :
    ∃ before : Cut input complete, ∃ forward : L.Complete initial native quantum allowance before monitor.forward,
      ∃ written : Step input, ∃ start : CampusTCPTwoReverseGeometry.Started forward reverseLower reverseUpper written,
        Nonempty (L.Evidence start.reverseInitial start.reverseNative quantum
          (allowance - monitor.forward.drops.length) current monitor.reverse) := by
  cases value with
  | reverse forward start next _ _ => exact ⟨_, forward, _, start, ⟨next⟩⟩
  | forward _ selected _ | needWrite _ selected | done _ _ _ selected => rw [selected] at mode; cases mode

theorem done_value (value : Evidence initial native quantum allowance reverseLower reverseUpper current monitor)
    (mode : monitor.mode = .done) :
    ∃ before : Cut input complete, ∃ forward : L.Complete initial native quantum allowance before monitor.forward,
      ∃ written : Step input, ∃ start : CampusTCPTwoReverseGeometry.Started forward reverseLower reverseUpper written,
        Nonempty (L.Complete start.reverseInitial start.reverseNative quantum
          (allowance - monitor.forward.drops.length) current monitor.reverse) := by
  cases value with
  | done forward start next _ => exact ⟨_, forward, _, start, ⟨next⟩⟩
  | forward _ selected _ | needWrite _ selected | reverse _ _ _ selected _ => rw [selected] at mode; cases mode

end Netlib.Check.CampusTCPTwoExchangeRecorded
