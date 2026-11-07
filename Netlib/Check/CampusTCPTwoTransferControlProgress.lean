import Netlib.Check.CampusTCPTwoTransferControlState
import Netlib.Check.CampusTCPTwoTransferPhaseControl

namespace Netlib.Check.CampusTCPTwoTransferControlProgress

open Protocol Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart
open CampusTCPTwoTransferNative (Checks Routing)
open CampusTCPTwoTransferLocatedCore (Core config)

namespace C
export CampusTCPTwoTransferControlState (Phase Advanced afterLocation)
end C
namespace W
export CampusTCPTwoTransferMonitor (Monitor Control controlDemand drainTicket observe)
end W
namespace P
export CampusTCPTwoTransferPreparationState (Written PendingUpper)
end P
namespace A
export CampusTCPTwoTransferPhaseState (Active)
end A

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current : Cut input complete} {sender : Actor} {gateway location : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {checks : Checks cut initial.gatewayState.session.entry} {routing : Routing cut gateway}
variable {quantum allowance : Nat} {reverseLower reverseUpper : List UInt8}
variable {monitor : W.Monitor} {kind : W.Control} {actual : Step input}
variable {sent : CampusTCPTwoProgressSender.Stage initial} {received : CampusTCPTwoProgressReceiver.Stage}
variable {first : CampusTCPTwoProgressSender.Original initial .lower}

local notation "cfg" => config initial checks routing quantum allowance reverseLower reverseUpper

theorem location_at (phase : C.Phase current.report.final monitor.mode location)
    (selected : W.controlDemand monitor = some kind) :
    location = if kind = .install then .primary else C.afterLocation kind := by
  generalize modeEq : monitor.mode = mode at phase
  cases phase <;> cases kind <;>
    simp_all [W.controlDemand, C.afterLocation]
  all_goals split at selected <;> simp_all

theorem install_location (phase : C.Phase current.report.final monitor.mode location)
    (selected : W.controlDemand monitor = some .install) : location = .primary := by
  simpa only [ite_true] using location_at phase selected

theorem ordinary_location (phase : C.Phase current.report.final monitor.mode location)
    (selected : W.controlDemand monitor = some kind) (ordinary : kind ≠ .install) : location = C.afterLocation kind := by
  simpa only [ordinary, ite_false] using location_at phase selected

private theorem noninstall (ordinary : kind ≠ .install) : ∀ ns, kind.event cfg ≠ .installCheckpoint ns := by
  cases kind <;> simp_all [CampusTCPTwoTransferMonitor.Control.event]

structure WrittenAdvanced
    (state : P.Written initial checks routing quantum allowance reverseLower reverseUpper current monitor location)
    (kind : W.Control) (actual : Step input) where
  advance : C.Advanced current cfg monitor kind actual
  next : P.Written initial checks routing quantum allowance reverseLower reverseUpper advance.value.move.after
    (W.observe cfg monitor actual) (C.afterLocation kind)
  book : next.core.losses.book = state.core.losses.book

structure PendingUpperAdvanced
    (state : P.PendingUpper initial checks routing quantum allowance reverseLower reverseUpper current monitor location first)
    (kind : W.Control) (actual : Step input) where
  advance : C.Advanced current cfg monitor kind actual
  next : P.PendingUpper initial checks routing quantum allowance reverseLower reverseUpper advance.value.move.after
    (W.observe cfg monitor actual) (C.afterLocation kind) first
  book : next.core.losses.book = state.core.losses.book

structure ActiveAdvanced
    {core : Core initial checks routing quantum allowance reverseLower reverseUpper current monitor location sent received}
    (state : A.Active core) (kind : W.Control) (actual : Step input) where
  advance : C.Advanced current cfg monitor kind actual
  next : Core initial checks routing quantum allowance reverseLower reverseUpper advance.value.move.after
    (W.observe cfg monitor actual) (C.afterLocation kind) sent received
  active : A.Active next
  book : next.losses.book = core.losses.book

theorem WrittenAdvanced.ofAdvance
    (state : P.Written initial checks routing quantum allowance reverseLower reverseUpper current monitor location)
    (phase : C.Phase current.report.final monitor.mode location)
    (selected : W.controlDemand monitor = some kind) (drainless : W.drainTicket current.report.final monitor = none)
    (advance : C.Advanced current cfg monitor kind actual) : Nonempty (WrittenAdvanced state kind actual) := by
  by_cases installing : kind = .install
  · subst kind
    have primary := install_location phase selected
    subst location
    obtain ⟨installation, present⟩ := advance.stored
    exact ⟨⟨advance, state.install advance.value selected drainless installation present,
      state.core.install_book advance.value selected drainless installation present⟩⟩
  · have located := ordinary_location phase selected installing
    subst location
    exact ⟨⟨advance, state.control advance.value selected drainless (noninstall installing),
      state.core.control_book advance.value selected drainless (noninstall installing)⟩⟩

theorem PendingUpperAdvanced.ofAdvance
    (state : P.PendingUpper initial checks routing quantum allowance reverseLower reverseUpper current monitor location first)
    (phase : C.Phase current.report.final monitor.mode location)
    (selected : W.controlDemand monitor = some kind) (drainless : W.drainTicket current.report.final monitor = none)
    (advance : C.Advanced current cfg monitor kind actual) : Nonempty (PendingUpperAdvanced state kind actual) := by
  by_cases installing : kind = .install
  · subst kind
    have primary := install_location phase selected
    subst location
    obtain ⟨installation, present⟩ := advance.stored
    exact ⟨⟨advance, state.install advance.value selected drainless installation present,
      state.core.install_book advance.value selected drainless installation present⟩⟩
  · have located := ordinary_location phase selected installing
    subst location
    exact ⟨⟨advance, state.control advance.value selected drainless (noninstall installing),
      state.core.control_book advance.value selected drainless (noninstall installing)⟩⟩

theorem ActiveAdvanced.ofAdvance
    {core : Core initial checks routing quantum allowance reverseLower reverseUpper current monitor location sent received}
    (state : A.Active core) (phase : C.Phase current.report.final monitor.mode location)
    (selected : W.controlDemand monitor = some kind) (drainless : W.drainTicket current.report.final monitor = none)
    (advance : C.Advanced current cfg monitor kind actual) : Nonempty (ActiveAdvanced state kind actual) := by
  by_cases installing : kind = .install
  · subst kind
    have primary := install_location phase selected
    subst location
    obtain ⟨installation, present⟩ := advance.stored
    exact ⟨⟨advance, core.install advance.value selected drainless installation present,
      state.install advance.value selected drainless installation present,
      core.install_book advance.value selected drainless installation present⟩⟩
  · have located := ordinary_location phase selected installing
    subst location
    exact ⟨⟨advance, core.control advance.value selected drainless (noninstall installing),
      state.control advance.value selected drainless (noninstall installing),
      core.control_book advance.value selected drainless (noninstall installing)⟩⟩

theorem WrittenAdvanced.next_phase
    {state : P.Written initial checks routing quantum allowance reverseLower reverseUpper current monitor location}
    (value : WrittenAdvanced state kind actual) :
    C.Phase value.advance.value.move.after.report.final (W.observe cfg monitor actual).mode (C.afterLocation kind) :=
  value.advance.next_observed

theorem PendingUpperAdvanced.next_phase
    {state : P.PendingUpper initial checks routing quantum allowance reverseLower reverseUpper current monitor location first}
    (value : PendingUpperAdvanced state kind actual) :
    C.Phase value.advance.value.move.after.report.final (W.observe cfg monitor actual).mode (C.afterLocation kind) :=
  value.advance.next_observed

theorem ActiveAdvanced.next_phase
    {core : Core initial checks routing quantum allowance reverseLower reverseUpper current monitor location sent received}
    {state : A.Active core} (value : ActiveAdvanced state kind actual) :
    C.Phase value.advance.value.move.after.report.final (W.observe cfg monitor actual).mode (C.afterLocation kind) :=
  value.advance.next_observed

end Netlib.Check.CampusTCPTwoTransferControlProgress

namespace Netlib.Check.CampusTCPTwoTransferPreparationState

open Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart
open CampusTCPTwoTransferNative (Checks Routing)
open CampusTCPTwoTransferLocatedCore (config)
open CampusTCPTwoTransferControlProgress

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current : Cut input complete} {sender : Actor} {gateway location : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {checks : Checks cut initial.gatewayState.session.entry} {routing : Routing cut gateway}
variable {quantum allowance : Nat} {reverseLower reverseUpper : List UInt8}
variable {monitor : CampusTCPTwoTransferMonitor.Monitor} {kind : CampusTCPTwoTransferMonitor.Control}
variable {first : CampusTCPTwoProgressSender.Original initial .lower}

local notation "cfg" => config initial checks routing quantum allowance reverseLower reverseUpper

theorem Written.control_at
    (state : Written initial checks routing quantum allowance reverseLower reverseUpper current monitor location)
    (phase : C.Phase current.report.final monitor.mode location)
    (selected : W.controlDemand monitor = some kind) (drainless : W.drainTicket current.report.final monitor = none) :
    ∃ actual, Nonempty (WrittenAdvanced state kind actual) := by
  obtain ⟨actual, ⟨advance⟩⟩ := CampusTCPTwoTransferControlState.control_at state.core phase selected drainless
  exact ⟨actual, WrittenAdvanced.ofAdvance state phase selected drainless advance⟩

theorem PendingUpper.control_at
    (state : PendingUpper initial checks routing quantum allowance reverseLower reverseUpper current monitor location first)
    (phase : C.Phase current.report.final monitor.mode location)
    (selected : W.controlDemand monitor = some kind) (drainless : W.drainTicket current.report.final monitor = none) :
    ∃ actual, Nonempty (PendingUpperAdvanced state kind actual) := by
  obtain ⟨actual, ⟨advance⟩⟩ := CampusTCPTwoTransferControlState.control_at state.core phase selected drainless
  exact ⟨actual, PendingUpperAdvanced.ofAdvance state phase selected drainless advance⟩

theorem Written.control_step
    (state : Written initial checks routing quantum allowance reverseLower reverseUpper current monitor location)
    (phase : C.Phase current.report.final monitor.mode location)
    (selected : W.controlDemand monitor = some kind) (drainless : W.drainTicket current.report.final monitor = none)
    (actual : Step input) (before : actual.before = current.report.final) (event : actual.event = kind.event cfg) :
    Nonempty (WrittenAdvanced state kind actual) := by
  obtain ⟨advance⟩ := CampusTCPTwoTransferControlState.Step.control state.core phase selected drainless actual before event
  exact WrittenAdvanced.ofAdvance state phase selected drainless advance

theorem PendingUpper.control_step
    (state : PendingUpper initial checks routing quantum allowance reverseLower reverseUpper current monitor location first)
    (phase : C.Phase current.report.final monitor.mode location)
    (selected : W.controlDemand monitor = some kind) (drainless : W.drainTicket current.report.final monitor = none)
    (actual : Step input) (before : actual.before = current.report.final) (event : actual.event = kind.event cfg) :
    Nonempty (PendingUpperAdvanced state kind actual) := by
  obtain ⟨advance⟩ := CampusTCPTwoTransferControlState.Step.control state.core phase selected drainless actual before event
  exact PendingUpperAdvanced.ofAdvance state phase selected drainless advance

end Netlib.Check.CampusTCPTwoTransferPreparationState

namespace Netlib.Check.CampusTCPTwoTransferPhaseState

open Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart
open CampusTCPTwoTransferNative (Checks Routing)
open CampusTCPTwoTransferLocatedCore (Core config)
open CampusTCPTwoTransferControlProgress

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current : Cut input complete} {sender : Actor} {gateway location : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {checks : Checks cut initial.gatewayState.session.entry} {routing : Routing cut gateway}
variable {quantum allowance : Nat} {reverseLower reverseUpper : List UInt8}
variable {monitor : CampusTCPTwoTransferMonitor.Monitor} {kind : CampusTCPTwoTransferMonitor.Control}
variable {sent : CampusTCPTwoProgressSender.Stage initial} {received : CampusTCPTwoProgressReceiver.Stage}
variable {core : Core initial checks routing quantum allowance reverseLower reverseUpper current monitor location sent received}

local notation "cfg" => config initial checks routing quantum allowance reverseLower reverseUpper

theorem Active.control_at (state : Active core) (phase : C.Phase current.report.final monitor.mode location)
    (selected : W.controlDemand monitor = some kind) (drainless : W.drainTicket current.report.final monitor = none) :
    ∃ actual, Nonempty (ActiveAdvanced state kind actual) := by
  obtain ⟨actual, ⟨advance⟩⟩ := CampusTCPTwoTransferControlState.control_at core phase selected drainless
  exact ⟨actual, ActiveAdvanced.ofAdvance state phase selected drainless advance⟩

theorem Active.control_step (state : Active core) (phase : C.Phase current.report.final monitor.mode location)
    (selected : W.controlDemand monitor = some kind) (drainless : W.drainTicket current.report.final monitor = none)
    (actual : Step input) (before : actual.before = current.report.final) (event : actual.event = kind.event cfg) :
    Nonempty (ActiveAdvanced state kind actual) := by
  obtain ⟨advance⟩ := CampusTCPTwoTransferControlState.Step.control core phase selected drainless actual before event
  exact ActiveAdvanced.ofAdvance state phase selected drainless advance

end Netlib.Check.CampusTCPTwoTransferPhaseState
