import Netlib.Check.CampusTCPTwoProgressRecoveryBounded
import Netlib.Check.CampusTCPTwoProgressRecorded

/-!
# Complete two-record reads within the actual trace bound

The result retains the exact recorded prefix and its actual reader.
Byte origins and service permissions use that same completed report.
-/

namespace Netlib.Check.CampusTCPTwoProgressBounded

open Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart
open CampusTCPTwoProgressSetup (config)
open CampusTCPTwoProgressEvidence (Complete)

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut : Cut input complete} {sender : Actor} {gateway : Gateway} {lower upper : List UInt8}

abbrev boundSlots (initial : TwoWriteInitial cut sender gateway lower upper) (quantum allowance bound : Nat) : Nat :=
  CampusTCPTwoProgressRecoveryBounded.boundSlots initial quantum allowance bound

structure Result (initial : TwoWriteInitial cut sender gateway lower upper)
    (native : NativeEnv cut gateway initial.gatewayState.session.entry) (quantum allowance bound : Nat)
    (steps : List (Step input)) where
  current : Cut input complete
  final : current.report.final = CampusTCPSchedule.stateAt cut.report.final steps (boundSlots initial quantum allowance bound)
  history : current.report.steps = cut.report.steps ++ steps.take (boundSlots initial quantum allowance bound)
  value : Complete initial native quantum allowance current
    (CampusTCPTwoProgressMonitor.monitorAt (config initial native quantum allowance) .initial steps (boundSlots initial quantum allowance bound))
  readerRecorded : value.completed.reader ∈ steps.take (boundSlots initial quantum allowance bound)

variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {native : NativeEnv cut gateway initial.gatewayState.session.entry} {quantum allowance bound : Nat}
variable {steps : List (Step input)}

theorem Result.reader_slot (result : Result initial native quantum allowance bound steps) :
    ∃ slot, slot < boundSlots initial quantum allowance bound ∧ steps[slot]? = some result.value.completed.reader := by
  obtain ⟨slot, selected⟩ := List.mem_iff_getElem?.mp result.readerRecorded
  rw [List.getElem?_take] at selected
  by_cases inside : slot < boundSlots initial quantum allowance bound
  · exact ⟨slot, inside, by simpa only [inside, ite_true] using selected⟩
  · rw [ite_eq_right inside] at selected
    cases selected

theorem Result.read_event (result : Result initial native quantum allowance bound steps) :
    result.value.completed.reader.event = .read sender.other (lower ++ upper).length := result.value.completed.event

theorem Result.read_bytes (result : Result initial native quantum allowance bound steps) :
    result.value.completed.reader.result.read = lower ++ upper := result.value.completed.returned

theorem Result.retry_bound (result : Result initial native quantum allowance bound steps) : result.value.timeouts ≤ allowance :=
  result.value.retry_bound

theorem Result.read_permissions (result : Result initial native quantum allowance bound steps)
    (prior : cut.report.compliant = true) (index : Nat) (byte : UInt8) (selected : (lower ++ upper)[index]? = some byte) :
    ∃ origin : CampusTCPTwoProgressReadSuffix.SuffixReadOrigin result.value.completed index byte,
      Nonempty (CampusTCPTwoProgressWriteOrigins.SelectedWriteOrigin initial origin.attempt origin.read.origin.localIndex byte) ∧
        CampusTCPRoundOrigins.ServicePermissions origin.delivery.service.joint.step origin.delivery.receive.receipt.served :=
  result.value.read_permissions prior index byte selected

variable {suffix remaining : List Event} {final : State input}

theorem Result.now_le (result : Result initial native quantum allowance bound steps) (budget : allowance ≤ 2)
    (trace : Trace input cut.report.final suffix steps final remaining)
    (actions : CampusTCPTwoProgressProgress.Actions initial native quantum allowance steps)
    (within : boundSlots initial quantum allowance bound ≤ steps.length) (actor : Actor) :
    (endpoint result.current.endpoints actor).now ≤ (endpoint cut.endpoints actor).now +
      boundSlots initial quantum allowance bound * quantum := by
  have bound := CampusTCPTwoProgressSuffixAge.trace_now_le trace actions budget
    (boundSlots initial quantum allowance bound) within actor
  rw [← result.final, CampusTCPTwoProgressSuffixAge.nowAt_cut] at bound
  exact bound

theorem complete_by (budget : allowance ≤ 2) (positive : 0 < quantum)
    (trace : Trace input cut.report.final suffix steps final remaining)
    (actions : CampusTCPTwoProgressProgress.Actions initial native quantum allowance steps)
    (service : CampusTCPTwoProgressMonitor.Serviced (config initial native quantum allowance) cut.report.final .initial steps bound)
    (enough : boundSlots initial quantum allowance bound ≤ steps.length) :
    Nonempty (Result initial native quantum allowance bound steps) := by
  have done : (CampusTCPTwoProgressMonitor.monitorAt (config initial native quantum allowance) .initial steps
      (boundSlots initial quantum allowance bound)).mode = .done := by
    obtain ⟨_, _, ⟨value⟩⟩ := CampusTCPTwoProgressRecoveryBounded.completes_by budget positive trace actions service enough
    exact value.mode
  obtain ⟨current, same, history, ⟨evidence⟩⟩ :=
    CampusTCPTwoProgressRecorded.trace_at budget trace actions (boundSlots initial quantum allowance bound) enough
  obtain ⟨value⟩ := CampusTCPTwoProgressInvariant.done_evidence evidence done
  exact ⟨⟨current, same, history, value, CampusTCPTwoProgressRecorded.reader_recorded value history⟩⟩

theorem complete_by_checked (budget : allowance ≤ 2) (positive : 0 < quantum)
    (trace : Trace input cut.report.final suffix steps final remaining)
    (actions : CampusTCPTwoProgressMonitor.actions (config initial native quantum allowance) cut.report.final .initial steps = true)
    (service : CampusTCPTwoProgressMonitor.check (config initial native quantum allowance) cut.report.final .initial steps bound = true)
    (enough : boundSlots initial quantum allowance bound ≤ steps.length) :
    Nonempty (Result initial native quantum allowance bound steps) :=
  complete_by budget positive trace ((CampusTCPTwoProgressMonitor.actions_correct _ _ _ _).mp actions)
    ((CampusTCPTwoProgressMonitor.check_correct _ _ _ _ _).mp service) enough

theorem complete_by_permissions (budget : allowance ≤ 2) (positive : 0 < quantum)
    (trace : Trace input cut.report.final suffix steps final remaining)
    (actions : CampusTCPTwoProgressProgress.Actions initial native quantum allowance steps)
    (service : CampusTCPTwoProgressMonitor.Serviced (config initial native quantum allowance) cut.report.final .initial steps bound)
    (enough : boundSlots initial quantum allowance bound ≤ steps.length) (prior : cut.report.compliant = true) :
    ∃ result : Result initial native quantum allowance bound steps, ∀ index byte, (lower ++ upper)[index]? = some byte →
      ∃ origin : CampusTCPTwoProgressReadSuffix.SuffixReadOrigin result.value.completed index byte,
        Nonempty (CampusTCPTwoProgressWriteOrigins.SelectedWriteOrigin initial origin.attempt origin.read.origin.localIndex byte) ∧
          CampusTCPRoundOrigins.ServicePermissions origin.delivery.service.joint.step origin.delivery.receive.receipt.served := by
  obtain ⟨result⟩ := complete_by budget positive trace actions service enough
  exact ⟨result, result.read_permissions prior⟩

theorem complete_by_checked_permissions (budget : allowance ≤ 2) (positive : 0 < quantum)
    (trace : Trace input cut.report.final suffix steps final remaining)
    (actions : CampusTCPTwoProgressMonitor.actions (config initial native quantum allowance) cut.report.final .initial steps = true)
    (service : CampusTCPTwoProgressMonitor.check (config initial native quantum allowance) cut.report.final .initial steps bound = true)
    (enough : boundSlots initial quantum allowance bound ≤ steps.length) (prior : cut.report.compliant = true) :
    ∃ result : Result initial native quantum allowance bound steps, ∀ index byte, (lower ++ upper)[index]? = some byte →
      ∃ origin : CampusTCPTwoProgressReadSuffix.SuffixReadOrigin result.value.completed index byte,
        Nonempty (CampusTCPTwoProgressWriteOrigins.SelectedWriteOrigin initial origin.attempt origin.read.origin.localIndex byte) ∧
          CampusTCPRoundOrigins.ServicePermissions origin.delivery.service.joint.step origin.delivery.receive.receipt.served :=
  complete_by_permissions budget positive trace ((CampusTCPTwoProgressMonitor.actions_correct _ _ _ _).mp actions)
    ((CampusTCPTwoProgressMonitor.check_correct _ _ _ _ _).mp service) enough prior

end Netlib.Check.CampusTCPTwoProgressBounded
