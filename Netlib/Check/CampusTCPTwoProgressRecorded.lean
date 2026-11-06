import Netlib.Check.CampusTCPTwoProgressProgress

/-!
# Exact recorded prefixes

Each selected cut extends the initial report with the supplied stored steps.
The completed reader belongs to that new suffix.
-/

namespace Netlib.Check.CampusTCPTwoProgressRecorded

open Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart
open CampusTCPTwoProgressSetup (config)
open CampusTCPTwoProgressEvidence (Evidence Complete)

namespace M
export CampusTCPTwoProgressMonitor (Monitor monitorAt observe)
end M
namespace S
export CampusTCPSchedule (stateAt eventAt)
end S

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut : Cut input complete} {sender : Actor} {gateway : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {native : NativeEnv cut gateway initial.gatewayState.session.entry} {quantum allowance : Nat}
variable {suffix remaining : List Event} {steps : List (Step input)} {final : State input}

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
    | succ index =>
      exact congrArg (List.cons head) (ih found)

theorem trace_at (budget : allowance ≤ 2) (trace : Trace input cut.report.final suffix steps final remaining)
    (actions : CampusTCPTwoProgressProgress.Actions initial native quantum allowance steps)
    (slot : Nat) (within : slot ≤ steps.length) :
    ∃ current : Cut input complete, current.report.final = S.stateAt cut.report.final steps slot ∧
      current.report.steps = cut.report.steps ++ steps.take slot ∧
      Nonempty (Evidence initial native quantum allowance current
        (M.monitorAt (config initial native quantum allowance) .initial steps slot)) := by
  induction slot with
  | zero =>
    exact ⟨cut, (CampusTCPSchedule.stateAt_zero _ _).symm, (List.append_nil _).symm,
      by simpa only [CampusTCPTwoProgressMonitor.monitorAt_zero] using
        Nonempty.intro (Evidence.ofInitial initial native quantum allowance)⟩
  | succ slot ih =>
    obtain ⟨current, final, history, ⟨evidence⟩⟩ := ih (by omega)
    obtain ⟨actual, found, before, event, after⟩ := CampusTCPSchedule.Trace.at trace slot (by omega)
    have allowed : CampusTCPTwoProgressMonitor.Allowed (config initial native quantum allowance) current.report.final
        (M.monitorAt (config initial native quantum allowance) .initial steps slot) actual.event := by
      rw [final, event]
      exact actions slot (by omega)
    obtain ⟨move, next⟩ := evidence.step budget actual (before.trans final.symm) allowed
    refine ⟨move.after, move.final.trans after, ?_, ?_⟩
    · rw [move.history, history, List.append_assoc, ← take_next found]
    · rw [CampusTCPTwoProgressMonitor.monitorAt_next _ _ _ found]
      exact next

variable {current : Cut input complete} {monitor : M.Monitor}

theorem Complete.reader_not_initial (value : Complete initial native quantum allowance current monitor) :
    value.completed.reader ∉ cut.report.steps := by
  intro past
  have old := CampusTCPRecoveryRoundOrigins.Report.application_member cut.report value.completed.reader past
    sender.other value.completed.operation value.completed.recorded
  have oldMember : value.completed.operation ∈ applicationSteps cut.endpoints sender.other := by
    simpa only [cut.connection, CampusTCPRoundPhaseHistory.connectionSteps] using old
  have ordered := CampusTCPGapProgressOrigins.endpoint_order current sender.other
  rw [value.completed.history.steps] at ordered
  have newMember := CampusTCPTwoProgressReadSuffix.Completed.reader_suffix value.completed
  exact Nat.lt_irrefl _ ((List.pairwise_append.mp ordered).2.2
    value.completed.operation oldMember value.completed.operation newMember)

theorem reader_recorded (value : Complete initial native quantum allowance current monitor)
    (history : current.report.steps = cut.report.steps ++ recorded) : value.completed.reader ∈ recorded := by
  have member : value.completed.reader ∈ cut.report.steps ++ recorded := by
    rw [← history]
    exact value.completed.member
  rcases List.mem_append.mp member with old | fresh
  · exact False.elim (Complete.reader_not_initial value old)
  · exact fresh

end Netlib.Check.CampusTCPTwoProgressRecorded
