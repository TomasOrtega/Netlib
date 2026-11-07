import Netlib.Check.CampusTCPTwoTransferExchangeLoss

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

variable (value : ReadWrite initial checks routing quantum allowance reverseLower reverseUpper steps)
variable {monitor : CampusTCPTwoProgressMonitor.Monitor} (reverse : Reverse value final monitor)

abbrev MixedSpent := CampusTCPTwoTransferLoss.Spent initial cfg ⊕
  CampusTCPTwoProgressLossHistory.Spent value.written.start.reverseInitial (reverseConfig value)

def spent : List (MixedSpent value) :=
  (forward value).book.spent.map Sum.inl ++ reverse.losses.book.spent.map Sum.inr

def spentStep : MixedSpent value → Step input
  | .inl entry => entry.actual
  | .inr entry => entry.actual

def spentPosition : MixedSpent value → Nat
  | .inl entry => entry.position
  | .inr entry => reverseIndex value entry.position

def spentLoss : MixedSpent value → MixedLoss value
  | .inl entry => .inl entry.loss
  | .inr entry => .inr entry.loss

def spentActor : MixedSpent value → Actor
  | .inl _ => sender
  | .inr _ => sender.other

def lossBeforeSteps : MixedLoss value → List (Step input)
  | .inl loss => loss.before.report.steps
  | .inr loss => loss.before.report.steps

def lossAfterSteps : MixedLoss value → List (Step input)
  | .inl loss => loss.move.after.report.steps
  | .inr loss => loss.move.after.report.steps

def spentBeforeSteps : MixedSpent value → List (Step input)
  | .inl entry => entry.before.report.steps
  | .inr entry => entry.before.report.steps

def spentAfterSteps : MixedSpent value → List (Step input)
  | .inl entry => entry.move.after.report.steps
  | .inr entry => entry.move.after.report.steps

theorem reverseIndex_injective (same : reverseIndex value first = reverseIndex value second) : first = second :=
  Nat.add_left_cancel same

theorem reverse_after_forward (old : position < (forward value).book.losses.length) (next : Nat) :
    position < reverseIndex value next := by unfold reverseIndex; omega

theorem forward_lookup {position : Nat} {loss : CampusTCPTwoTransferLoss.Loss initial cfg}
    (found : (forward value).book.losses[position]? = some loss) :
    (losses value reverse)[position]? = some (.inl loss) := by
  rw [losses, List.getElem?_append_left (by simp only [List.length_map]; exact (List.getElem?_eq_some_iff.mp found).1),
    List.getElem?_map, found]
  rfl

theorem reverse_lookup {position : Nat}
    {loss : CampusTCPTwoProgressLossHistory.Loss value.written.start.reverseInitial (reverseConfig value)}
    (found : reverse.losses.book.losses[position]? = some loss) :
    (losses value reverse)[reverseIndex value position]? = some (.inr loss) := by
  rw [losses, List.getElem?_append_right (by simp only [List.length_map, reverseIndex]; omega), List.length_map,
    reverseIndex, Nat.add_sub_cancel_left, List.getElem?_map, found]
  rfl

theorem spent_distinct : (spentPositions value reverse).Nodup := by
  apply List.nodup_append.mpr
  refine ⟨(forward value).valid.distinct, ?_, ?_⟩
  · exact List.Pairwise.map (reverseIndex value)
      (by intro first second different same; exact different (reverseIndex_injective value same)) reverse.losses.valid.distinct
  · intro old member next mapped same
    obtain ⟨position, _, equality⟩ := List.mem_map.mp mapped
    have bound := (forward value).valid.position_bound member
    have after := reverse_after_forward value bound position
    omega

theorem spent_bound (member : position ∈ spentPositions value reverse) : position < (losses value reverse).length := by
  simp only [spentPositions, List.mem_append] at member
  simp only [losses, List.length_append, List.length_map]
  rcases member with first | second
  · have bound := (forward value).valid.position_bound first
    omega
  · obtain ⟨localPosition, localMember, same⟩ := List.mem_map.mp second
    have bound := reverse.losses.valid.position_bound localMember
    unfold reverseIndex at same
    omega

theorem spent_count : (spentPositions value reverse).length = (forward value).book.spent.length + reverse.losses.book.spent.length := by
  simp only [spentPositions, List.length_append, List.length_map, CampusTCPTwoTransferLoss.Book.positions,
    CampusTCPTwoProgressLossHistory.Book.positions]

theorem actual_spent_count : ((recorded value reverse).filter isTimeoutOutput).length = (spentPositions value reverse).length :=
  (actual_timeout_count value reverse).trans (spent_count value reverse).symm

theorem spent_le_losses : (spentPositions value reverse).length ≤ (losses value reverse).length := by
  have subset : spentPositions value reverse ⊆ List.range (losses value reverse).length := by
    intro position member
    exact List.mem_range.mpr (spent_bound value reverse member)
  simpa only [List.length_range] using (spent_distinct value reverse).length_le_of_subset subset

theorem forward_spent {entry : CampusTCPTwoTransferLoss.Spent initial cfg}
    (member : entry ∈ (forward value).book.spent) :
    (losses value reverse)[entry.position]? = some (.inl entry.loss) :=
  forward_lookup value reverse ((forward value).valid.spent entry member)

theorem reverse_spent {entry : CampusTCPTwoProgressLossHistory.Spent value.written.start.reverseInitial (reverseConfig value)}
    (member : entry ∈ reverse.losses.book.spent) :
    (losses value reverse)[reverseIndex value entry.position]? = some (.inr entry.loss) :=
  reverse_lookup value reverse (reverse.losses.valid.spent entry member)

theorem reverse_cause {role : CampusTCPTwoProgressSender.Part} {position : Nat}
    (chosen : reverse.losses.book.cause role = some position) :
    ∃ loss, (losses value reverse)[reverseIndex value position]? = some (.inr loss) ∧
      CampusTCPTwoProgressLossHistory.Supports loss role ∧ reverseIndex value position ∉ spentPositions value reverse := by
  obtain ⟨loss, found, support, unused⟩ := reverse.losses.valid.cause position chosen
  refine ⟨loss, reverse_lookup value reverse found, support, ?_⟩
  intro member
  rcases List.mem_append.mp member with first | second
  · have bound := (forward value).valid.position_bound first
    have after := reverse_after_forward value bound position
    omega
  · obtain ⟨old, member, same⟩ := List.mem_map.mp second
    exact unused ((reverseIndex_injective value same) ▸ member)

theorem spent_positions : (spent value reverse).map (spentPosition value) = spentPositions value reverse := by
  simp only [spent, spentPositions, List.map_append, List.map_map, Function.comp_def, spentPosition,
    CampusTCPTwoTransferLoss.Book.positions, CampusTCPTwoProgressLossHistory.Book.positions]

theorem actual_spent_steps : (recorded value reverse).filter isTimeoutOutput = (spent value reverse).map (spentStep value) := by
  rw [actual_timeout_steps]
  simp only [spent, List.map_append, List.map_map, Function.comp_def, spentStep]

theorem spent_lookup (member : entry ∈ spent value reverse) :
    (losses value reverse)[spentPosition value entry]? = some (spentLoss value entry) := by
  rcases List.mem_append.mp member with first | second
  · obtain ⟨entry, localMember, same⟩ := List.mem_map.mp first
    subst_vars
    exact forward_spent value reverse localMember
  · obtain ⟨entry, localMember, same⟩ := List.mem_map.mp second
    subst_vars
    exact reverse_spent value reverse localMember

theorem loss_recorded (member : entry ∈ losses value reverse) : lossStep entry ∈ recorded value reverse := by
  have selected : lossStep entry ∈ (losses value reverse).map lossStep := List.mem_map.mpr ⟨entry, member, rfl⟩
  rw [← actual_drop_steps] at selected
  exact (List.mem_filter.mp selected).1

theorem loss_event (member : entry ∈ losses value reverse) : (lossStep entry).event = .dropPacket (lossID entry) := by
  rcases List.mem_append.mp member with first | second
  · obtain ⟨loss, _, same⟩ := List.mem_map.mp first
    subst_vars
    exact loss.facts.event
  · obtain ⟨loss, _, same⟩ := List.mem_map.mp second
    subst_vars
    exact loss.facts.event

theorem spent_recorded (member : entry ∈ spent value reverse) : spentStep value entry ∈ recorded value reverse := by
  have selected : spentStep value entry ∈ (spent value reverse).map (spentStep value) := List.mem_map.mpr ⟨entry, member, rfl⟩
  rw [← actual_spent_steps] at selected
  exact (List.mem_filter.mp selected).1

theorem spent_event (entry : MixedSpent value) : (spentStep value entry).event = .timeout (spentActor value entry) true := by
  cases entry with
  | inl entry => exact entry.event
  | inr entry => exact entry.event

include reverse in
private theorem forward_final_prefix : value.written.point.current.report.steps <+: final.report.steps := by
  have first : value.written.point.current.report.steps <+: value.written.start.boundary.write.move.after.report.steps :=
    ⟨[value.written.actual], (joined value).history.symm⟩
  exact first.trans ⟨reverse.losses.suffix, reverse.losses.steps.symm⟩

theorem loss_retained (member : entry ∈ losses value reverse) : lossAfterSteps value entry <+: final.report.steps := by
  rcases List.mem_append.mp member with first | second
  · obtain ⟨loss, localMember, same⟩ := List.mem_map.mp first
    subst_vars
    exact ((forward value).lossesPast loss localMember).trans (forward_final_prefix value reverse)
  · obtain ⟨loss, localMember, same⟩ := List.mem_map.mp second
    subst_vars
    exact reverse.losses.lossesPast loss localMember

theorem spent_retained (member : entry ∈ spent value reverse) : spentAfterSteps value entry <+: final.report.steps := by
  rcases List.mem_append.mp member with first | second
  · obtain ⟨entry, localMember, same⟩ := List.mem_map.mp first
    subst_vars
    exact ((forward value).timeoutsPast entry localMember).trans (forward_final_prefix value reverse)
  · obtain ⟨entry, localMember, same⟩ := List.mem_map.mp second
    subst_vars
    exact reverse.losses.timeoutsPast entry localMember

theorem spent_earlier (entry : MixedSpent value) : lossAfterSteps value (spentLoss value entry) <+: spentBeforeSteps value entry := by
  cases entry with
  | inl entry => exact entry.earlier
  | inr entry => exact entry.earlier

theorem spent_order (entry : MixedSpent value) :
    (lossBeforeSteps value (spentLoss value entry)).length < (spentBeforeSteps value entry).length := by
  cases entry with
  | inl entry =>
    have earlier := entry.earlier.length_le
    rw [entry.loss.move.history, List.length_append, List.length_cons, List.length_nil] at earlier
    exact earlier
  | inr entry =>
    have earlier := entry.earlier.length_le
    rw [entry.loss.move.history, List.length_append, List.length_cons, List.length_nil] at earlier
    exact earlier

theorem forward_ack0_unspent {loss : CampusTCPTwoTransferLoss.Loss initial cfg}
    (target : loss.target = .ack) (fields : CampusTCPTwoProgressWire.AckFields initial 0 loss.source) :
    ∀ entry ∈ spent value reverse, spentLoss value entry ≠ .inl loss := by
  intro entry member same
  cases entry with
  | inl entry =>
    have equality : entry.loss = loss := Sum.inl.inj same
    exact (CampusTCPTwoTransferLoss.Supports.no_gap_ack target fields) (equality ▸ entry.support)
  | inr entry => cases same

theorem reverse_ack0_unspent
    {loss : CampusTCPTwoProgressLossHistory.Loss value.written.start.reverseInitial (reverseConfig value)}
    (target : loss.target = .ack)
    (fields : CampusTCPTwoProgressWire.AckFields value.written.start.reverseInitial 0 loss.source) :
    ∀ entry ∈ spent value reverse, spentLoss value entry ≠ .inr loss := by
  intro entry member same
  cases entry with
  | inl entry => cases same
  | inr entry =>
    have equality : entry.loss = loss := Sum.inr.inj same
    exact (CampusTCPTwoProgressLossHistory.Supports.no_gap_ack target fields) (equality ▸ entry.support)

end Netlib.Check.CampusTCPTwoTransferExchangeLoss
