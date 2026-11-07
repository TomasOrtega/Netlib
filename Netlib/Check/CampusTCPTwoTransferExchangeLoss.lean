import Netlib.Check.CampusTCPTwoTransferForwardWriteBounded
import Netlib.Check.CampusTCPTwoExchangeLoss
import Netlib.Check.CampusTCPDropIDs

namespace Netlib.Check.CampusTCPTwoTransferExchangeLoss

open Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart
open CampusTCPTwoTransferNative (Checks Routing)
open CampusTCPTwoTransferLocatedCore (config)
open CampusTCPTwoTransferForwardWriteBounded (ReadWrite)
open CampusTCPTwoProgressLossHistory (isDrop dropID)
open CampusTCPTwoExchangeLoss (isTimeoutOutput)

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut final : Cut input complete} {sender : Actor} {gateway : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {checks : Checks cut initial.gatewayState.session.entry} {routing : Routing cut gateway}
variable {quantum allowance : Nat} {reverseLower reverseUpper : List UInt8} {steps : List (Step input)}

local notation "cfg" => config initial checks routing quantum allowance reverseLower reverseUpper

def forward (value : ReadWrite initial checks routing quantum allowance reverseLower reverseUpper steps) :
    CampusTCPTwoTransferLossHistory.History initial cfg value.written.point.current
      (CampusTCPTwoTransferMonitor.monitorAt cfg .initial steps value.writeSlot) := value.written.point.value.losses

def remaining (value : ReadWrite initial checks routing quantum allowance reverseLower reverseUpper steps) : Nat :=
  allowance - (forward value).book.losses.length

abbrev reverseConfig (value : ReadWrite initial checks routing quantum allowance reverseLower reverseUpper steps) :
    CampusTCPTwoProgressMonitor.Config :=
  CampusTCPTwoProgressSetup.config value.written.start.reverseInitial value.written.start.reverseNative quantum (remaining value)

abbrev Reverse (value : ReadWrite initial checks routing quantum allowance reverseLower reverseUpper steps)
    (final : Cut input complete) (monitor : CampusTCPTwoProgressMonitor.Monitor) :=
  CampusTCPTwoProgressEvidence.Complete value.written.start.reverseInitial value.written.start.reverseNative
    quantum (remaining value) final monitor

abbrev MixedLoss (value : ReadWrite initial checks routing quantum allowance reverseLower reverseUpper steps) :=
  CampusTCPTwoTransferLoss.Loss initial cfg ⊕
    CampusTCPTwoProgressLossHistory.Loss value.written.start.reverseInitial (reverseConfig value)

def lossStep {value : ReadWrite initial checks routing quantum allowance reverseLower reverseUpper steps} :
    MixedLoss value → Step input
  | .inl loss => loss.actual
  | .inr loss => loss.actual

def lossID {value : ReadWrite initial checks routing quantum allowance reverseLower reverseUpper steps} : MixedLoss value → Nat
  | .inl loss => loss.id
  | .inr loss => loss.id

variable (value : ReadWrite initial checks routing quantum allowance reverseLower reverseUpper steps)
variable {monitor : CampusTCPTwoProgressMonitor.Monitor} (reverse : Reverse value final monitor)

def losses : List (MixedLoss value) :=
  (forward value).book.losses.map Sum.inl ++ reverse.losses.book.losses.map Sum.inr

def reverseIndex (position : Nat) : Nat := (forward value).book.losses.length + position

def spentPositions : List Nat :=
  (forward value).book.positions ++ reverse.losses.book.positions.map (reverseIndex value)

def recorded : List (Step input) := (forward value).suffix ++ [value.written.actual] ++ reverse.losses.suffix

theorem joined : CampusTCPTwoExchangeLoss.Joined value.written.point.current
    value.written.start.boundary.write.move.after [value.written.actual] :=
  CampusTCPTwoExchangeLoss.Joined.of_write value.written.start.boundary.write.move sender.other (reverseLower ++ reverseUpper)
    value.written.start.boundary.write.event

theorem forward_book : (forward value).book = value.read.advance.value.losses.book := value.written.point.value.book

theorem remaining_at_write : remaining value = allowance -
    (CampusTCPTwoTransferMonitor.monitorAt cfg .initial steps value.writeSlot).exchange.forward.drops.length := by
  rw [(forward value).dropIDs, List.length_map]
  rfl

theorem forward_drop_bound : (forward value).book.losses.length ≤ allowance := by
  rw [forward_book]
  have bound := value.read.advance.value.lossBound
  rw [value.read.advance.value.losses.dropIDs, List.length_map] at bound
  exact bound

theorem reverse_drop_bound : reverse.losses.book.losses.length ≤ remaining value := by
  have bound := reverse.lossBound
  rw [reverse.losses.dropIDs, List.length_map] at bound
  exact bound

theorem report_steps : final.report.steps = cut.report.steps ++ recorded value reverse := by
  rw [reverse.losses.steps, (joined value).history, (forward value).steps]
  simp only [recorded, List.append_assoc]

theorem recorded_eq {supplied : List (Step input)} (history : final.report.steps = cut.report.steps ++ supplied) :
    supplied = recorded value reverse := List.append_cancel_left (history.symm.trans (report_steps value reverse))

theorem forward_suffix : (forward value).suffix = steps.take value.writeSlot :=
  List.append_cancel_left ((forward value).steps.symm.trans value.written.point.history)

theorem forward_suffix_length : (forward value).suffix.length = value.writeSlot := by
  rw [forward_suffix, List.length_take, Nat.min_eq_left (Nat.le_of_lt (List.getElem?_eq_some_iff.mp value.written.found).1)]

theorem forward_suffix_clocks :
    (forward value).suffix = value.read.advance.value.losses.suffix ++ value.written.point.value.clocks := by
  apply List.append_cancel_left (as := cut.report.steps)
  rw [← (forward value).steps, value.written.point.value.history]
  change value.read.advance.value.value.move.after.report.steps ++ value.written.point.value.clocks = _
  rw [value.read.advance.value.losses.steps, List.append_assoc]

theorem recorded_expanded : recorded value reverse = value.read.advance.value.losses.suffix ++
    value.written.point.value.clocks ++ [value.written.actual] ++ reverse.losses.suffix := by
  rw [recorded, forward_suffix_clocks]

theorem recorded_length : (recorded value reverse).length = value.writeSlot + 1 + reverse.losses.suffix.length := by
  simp only [recorded, List.length_append, List.length_cons, List.length_nil, Nat.zero_add, forward_suffix_length]

private theorem filtered_ids (stored : List (Step input)) :
    stored.filterMap dropID = (stored.filter isDrop).filterMap dropID := by
  induction stored with
  | nil => rfl
  | cons actual rest ih => cases event : actual.event <;>
      simp only [List.filterMap_cons, List.filter_cons, dropID, isDrop, event, Bool.false_eq_true, ite_false, ite_true, ih]

theorem actual_drop_steps : (recorded value reverse).filter isDrop = (losses value reverse).map lossStep := by
  unfold losses
  rw [List.map_append, List.map_map, List.map_map]
  simp only [recorded, List.filter_append, (joined value).noDrop, List.append_nil, (forward value).dropSteps,
    reverse.losses.dropSteps, Function.comp_def, lossStep]

theorem losses_ids : (losses value reverse).map lossID =
    (CampusTCPTwoTransferMonitor.monitorAt cfg .initial steps value.writeSlot).exchange.drops ++ monitor.drops := by
  unfold losses
  rw [List.map_append, List.map_map, List.map_map]
  simp only [Function.comp_def, lossID,
    (forward value).wholeDropIDs, reverse.losses.dropIDs]

theorem actual_drop_ids : (recorded value reverse).filterMap dropID =
    (CampusTCPTwoTransferMonitor.monitorAt cfg .initial steps value.writeSlot).exchange.drops ++ monitor.drops := by
  have quiet : [value.written.actual].filterMap dropID = [] := by rw [filtered_ids, (joined value).noDrop]; rfl
  simp only [recorded, List.filterMap_append, quiet, List.append_nil, (forward value).actual_ids, reverse.losses.actual_ids]

theorem actual_global_ids : (recorded value reverse).filterMap dropID = (losses value reverse).map lossID :=
  (actual_drop_ids value reverse).trans (losses_ids value reverse).symm

theorem actual_drop_count : ((recorded value reverse).filter isDrop).length =
    (forward value).book.losses.length + reverse.losses.book.losses.length := by
  rw [actual_drop_steps]
  unfold losses
  rw [List.length_map, List.length_append, List.length_map, List.length_map]

theorem reverse_owned : CampusTCPTwoExchangeLoss.OwnedTimeouts sender.other reverse.losses.suffix := by
  apply CampusTCPTwoExchangeLoss.owned_of_healthy_fold (reverseConfig value) .initial reverse.losses.suffix
  unfold reverseConfig
  rw [reverse.losses.observed, reverse.mode]
  decide

theorem actual_timeout_steps : (recorded value reverse).filter isTimeoutOutput =
    (forward value).book.spent.map (·.actual) ++ reverse.losses.book.spent.map (·.actual) := by
  have owned := List.filter_congr (reverse_owned value reverse)
  simp only [recorded, List.filter_append, (joined value).noTimeout, List.append_nil,
    (forward value).timeoutSteps, owned, reverse.losses.timeoutSteps]

theorem actual_timeout_count : ((recorded value reverse).filter isTimeoutOutput).length =
    (forward value).book.spent.length + reverse.losses.book.spent.length := by
  rw [actual_timeout_steps]
  simp only [List.length_append, List.length_map]

theorem timeout_le_drops : ((recorded value reverse).filter isTimeoutOutput).length ≤
    ((recorded value reverse).filter isDrop).length := by
  rw [actual_timeout_count, actual_drop_count]
  exact Nat.add_le_add (forward value).valid.spent_le reverse.losses.valid.spent_le

theorem drop_budget : ((recorded value reverse).filter isDrop).length ≤ allowance := by
  rw [actual_drop_count]
  have first := forward_drop_bound value
  have second := reverse_drop_bound value reverse
  change reverse.losses.book.losses.length ≤ allowance - (forward value).book.losses.length at second
  omega

theorem timeout_budget : ((recorded value reverse).filter isTimeoutOutput).length ≤ allowance :=
  Nat.le_trans (timeout_le_drops value reverse) (drop_budget value reverse)

theorem packet_ids_nodup : ((recorded value reverse).filterMap dropID).Nodup :=
  CampusTCPDropIDs.Report.suffix_ids_nodup final.report (report_steps value reverse)

theorem packet_ids_disjoint : ∀ id ∈ (forward value).book.losses.map (·.id),
    ∀ next ∈ reverse.losses.book.losses.map (·.id), id ≠ next := by
  have distinct := packet_ids_nodup value reverse
  rw [actual_drop_ids, (forward value).wholeDropIDs, reverse.losses.dropIDs] at distinct
  exact (List.nodup_append.mp distinct).2.2

theorem prior_ids_disjoint : ∀ id ∈ cut.report.final.custody.droppedIDs,
    ∀ selected ∈ (recorded value reverse).filterMap dropID, id ≠ selected := by
  have distinct := CampusTCPDropIDs.Report.ids_nodup final.report
  rw [report_steps, List.filterMap_append] at distinct
  have earlier := (List.nodup_append.mp distinct).2.2
  rw [CampusTCPDropIDs.Report.droppedIDs cut.report]
  exact earlier

end Netlib.Check.CampusTCPTwoTransferExchangeLoss
