import Netlib.Check.CampusTCPTwoProgressLossHistory
import Netlib.Check.CampusTCPTwoProgressTimer
import Netlib.Check.CampusTCPTwoProgressEvidenceTrace

/-!
# Shared loss positions across an actual direction change

Each leg keeps its own typed loss and cause evidence.
Reverse positions follow every forward loss, including unused losses.
-/

namespace Netlib.Check.CampusTCPTwoExchangeLoss

open Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart
open CampusTCPTwoProgressLossHistory (History Loss isDrop dropID isTimeout)

def isTimeoutOutput (actual : Step input) : Bool :=
  match actual.event with | .timeout _ true => true | _ => false

def OwnedTimeouts (actor : Actor) (steps : List (Step input)) : Prop :=
  ∀ actual ∈ steps, isTimeoutOutput actual = isTimeout actor actual

namespace M
export CampusTCPTwoProgressMonitor (Config Monitor Demand Allowed nextDemand laneDemand serves observe)
end M
namespace G
export CampusTCPGapProgressMonitor (Demand serves)
end G

private theorem lane_timeout_false (cfg : M.Config) (state : State input) (monitor : M.Monitor)
    (lane : CampusTCPTwoProgressMonitor.Lane) (selected : M.laneDemand cfg state monitor lane = some demand)
    (actor : Actor) (policy : Bool) : G.serves demand (.timeout actor policy) = false := by
  obtain ⟨_, _, ordinary | ⟨_, resolution⟩⟩ := CampusTCPTwoProgressMonitorFacts.laneDemand_action _ _ _ _ selected
  · rw [ordinary]; rfl
  · rw [resolution]; rfl

private theorem selected_timeout_actor (cfg : M.Config) (state : State input) (monitor : M.Monitor)
    (next : M.nextDemand cfg state monitor = some demand) (actor : Actor) (policy : Bool)
    (served : M.serves demand (.timeout actor policy) = true) : actor = cfg.sender ∧ policy = true := by
  have laneImpossible (lane : CampusTCPTwoProgressMonitor.Lane) (raw : G.Demand)
      (pending : M.laneDemand cfg state monitor lane = some raw)
      (served : G.serves raw (.timeout actor policy) = true) : False := by
    rw [lane_timeout_false cfg state monitor lane pending actor policy] at served
    cases served
  cases mode : monitor.mode <;> simp only [M.nextDemand, mode] at next
  case originals =>
    split at next
    · cases next
      cases served
    · split at next
      · cases next
        cases served
      · cases ack : monitor.ack with
        | some lane =>
          simp only [ack] at next
          cases pending : M.laneDemand cfg state monitor lane with
          | none => simp only [pending, Option.map_none] at next; cases next
          | some raw =>
            have same : (.single raw : M.Demand) = demand := by simpa only [pending, Option.map_some, Option.some.injEq] using next
            subst demand
            exact False.elim (laneImpossible lane raw pending served)
        | none =>
          simp only [ack] at next
          split at next
          · cases next
            rcases CampusTCPTwoProgressMonitorFacts.originalChoice_branch _ _ _ served with
              ⟨raw, pending, served⟩ | ⟨raw, pending, served⟩
            · exact False.elim (laneImpossible _ raw pending served)
            · exact False.elim (laneImpossible _ raw pending served)
          · cases next
  case recovery =>
    cases ack : monitor.ack with
    | some lane =>
      simp only [ack] at next
      cases pending : M.laneDemand cfg state monitor lane with
      | none => simp only [pending, Option.map_none] at next; cases next
      | some raw =>
        have same : (.single raw : M.Demand) = demand := by simpa only [pending, Option.map_some, Option.some.injEq] using next
        subst demand
        exact False.elim (laneImpossible lane raw pending served)
    | none =>
      simp only [ack] at next
      split at next
      · cases pending : CampusTCPTwoProgressMonitor.timerDemand cfg state with
        | none => simp only [pending, Option.map_none] at next; cases next
        | some raw =>
          have same : (.single raw : M.Demand) = demand := by simpa only [pending, Option.map_some, Option.some.injEq] using next
          subst demand
          obtain ⟨recovery, _, _, _, target, _, _, _, _, chosen⟩ := CampusTCPTwoProgressTimer.timerDemand_some pending
          by_cases early : recovery.now < target
          · rw [ite_eq_left early] at chosen
            have impossible := (CampusTCPTwoProgressMonitorFacts.serves_tick cfg.sender (min (recovery.now + cfg.quantum) target) (.timeout actor policy)).mp (chosen ▸ served)
            cases impossible
          · rw [ite_eq_right early] at chosen
            have same := (CampusTCPTwoProgressMonitorFacts.serves_timeout cfg.sender (.timeout actor policy)).mp (chosen ▸ served)
            exact Event.timeout.inj same
      · cases pending : M.laneDemand cfg state monitor monitor.retry with
        | none => simp only [pending, Option.map_none] at next; cases next
        | some raw =>
          have same : (.single raw : M.Demand) = demand := by simpa only [pending, Option.map_some, Option.some.injEq] using next
          subst demand
          exact False.elim (laneImpossible _ raw pending served)
  case needRead => cases next; cases served
  case done => cases next
  case invalid => cases next

theorem allowed_timeout_actor (cfg : M.Config) (state : State input) (monitor : M.Monitor) (actor : Actor) (policy : Bool)
    (allowed : M.Allowed cfg state monitor (.timeout actor policy)) : actor = cfg.sender ∧ policy = true := by
  obtain ⟨_, selected | dropped | clocked, _⟩ := (CampusTCPTwoProgressMonitorFacts.allowed_iff _ _ _ _).mp allowed
  · obtain ⟨demand, next, served⟩ := selected
    exact selected_timeout_actor cfg state monitor next actor policy served
  · obtain ⟨_, _, impossible, _⟩ := dropped
    cases impossible
  · obtain ⟨_, _, impossible, _⟩ := CampusTCPTwoProgressMonitorFacts.freeClock_event _ _ _ _ clocked
    cases impossible

theorem owned_of_healthy_fold (cfg : M.Config) (monitor : M.Monitor) (steps : List (Step input))
    (healthy : (steps.foldl (M.observe cfg) monitor).mode ≠ .invalid) : OwnedTimeouts cfg.sender steps := by
  induction steps generalizing monitor with
  | nil => intro actual member; cases member
  | cons actual rest ih =>
    have nextHealthy := (CampusTCPTwoProgressEvidenceTrace.fold_passed cfg (M.observe cfg monitor actual) rest healthy).1
    have allowed := (CampusTCPTwoProgressEvidenceTrace.observe_checked cfg monitor actual nextHealthy).2.2.2
    have first : isTimeoutOutput actual = isTimeout cfg.sender actual := by
      cases event : actual.event <;> simp only [isTimeoutOutput, isTimeout, event]
      case timeout actor policy =>
        cases policy
        · rfl
        · have same := (allowed_timeout_actor cfg actual.before monitor actor true (by rw [← event]; exact allowed)).1
          simp only [same, decide_true]
    intro chosen member
    rcases List.mem_cons.mp member with same | later
    · exact same ▸ first
    · exact ih (M.observe cfg monitor actual) healthy chosen later

private theorem filtered_ids (steps : List (Step input)) :
    steps.filterMap dropID = (steps.filter isDrop).filterMap dropID := by
  induction steps with
  | nil => rfl
  | cons actual rest ih => cases event : actual.event <;>
    simp only [List.filterMap_cons, List.filter_cons, dropID, isDrop, event, Bool.false_eq_true,
      ite_false, ite_true, ih]

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {forwardCut forwardEnd reverseCut reverseEnd : Cut input complete}
variable {sender : Actor} {forwardGateway reverseGateway : Gateway}
variable {forwardLower forwardUpper reverseLower reverseUpper : List UInt8}
variable {forwardInitial : TwoWriteInitial forwardCut sender forwardGateway forwardLower forwardUpper}
variable {reverseInitial : TwoWriteInitial reverseCut sender.other reverseGateway reverseLower reverseUpper}
variable {forwardConfig reverseConfig : CampusTCPTwoProgressMonitor.Config}
variable {forwardMonitor reverseMonitor : CampusTCPTwoProgressMonitor.Monitor}

abbrev ForwardLoss := Loss forwardInitial forwardConfig
abbrev ReverseLoss := Loss reverseInitial reverseConfig

def lossStep : ForwardLoss (forwardInitial := forwardInitial) (forwardConfig := forwardConfig) ⊕
    ReverseLoss (reverseInitial := reverseInitial) (reverseConfig := reverseConfig) → Step input
  | .inl loss => loss.actual
  | .inr loss => loss.actual

def lossID : ForwardLoss (forwardInitial := forwardInitial) (forwardConfig := forwardConfig) ⊕
    ReverseLoss (reverseInitial := reverseInitial) (reverseConfig := reverseConfig) → Nat
  | .inl loss => loss.id
  | .inr loss => loss.id

variable (forward : History forwardInitial forwardConfig forwardEnd forwardMonitor)
variable (reverse : History reverseInitial reverseConfig reverseEnd reverseMonitor)

def losses : List (ForwardLoss (forwardInitial := forwardInitial) (forwardConfig := forwardConfig) ⊕
    ReverseLoss (reverseInitial := reverseInitial) (reverseConfig := reverseConfig)) :=
  forward.book.losses.map Sum.inl ++ reverse.book.losses.map Sum.inr

def reverseIndex (position : Nat) : Nat := forward.book.losses.length + position

def spentPositions : List Nat := forward.book.positions ++ reverse.book.positions.map (reverseIndex forward)

def recorded (bridge : List (Step input)) : List (Step input) := forward.suffix ++ bridge ++ reverse.suffix

structure Joined (forwardEnd reverseCut : Cut input complete) (bridge : List (Step input)) : Prop where
  history : reverseCut.report.steps = forwardEnd.report.steps ++ bridge
  noDrop : bridge.filter isDrop = []
  noTimeout : bridge.filter isTimeoutOutput = []

theorem Joined.of_write (move : CampusTCPRoundPhaseBase.Move forwardEnd actual) (actor : Actor) (bytes : List UInt8)
    (event : actual.event = .write actor bytes) : Joined forwardEnd move.after [actual] := by
  exact ⟨move.history, by simp only [List.filter_cons, List.filter_nil, isDrop, event, Bool.false_eq_true, ite_false],
    by simp only [List.filter_cons, List.filter_nil, isTimeoutOutput, event, Bool.false_eq_true, ite_false]⟩

variable {forward reverse} {bridge : List (Step input)}

theorem report_steps (joined : Joined forwardEnd reverseCut bridge) :
    reverseEnd.report.steps = forwardCut.report.steps ++ recorded forward reverse bridge := by
  rw [reverse.steps, joined.history, forward.steps]
  simp only [recorded, List.append_assoc]

theorem actual_drop_steps (joined : Joined forwardEnd reverseCut bridge) :
    (recorded forward reverse bridge).filter isDrop = (losses forward reverse).map lossStep := by
  simp only [recorded, List.filter_append, joined.noDrop, List.append_nil, forward.dropSteps, reverse.dropSteps,
    losses, List.map_append, List.map_map, Function.comp_def, lossStep]

theorem actual_drop_ids (joined : Joined forwardEnd reverseCut bridge) :
    (recorded forward reverse bridge).filterMap dropID = forwardMonitor.drops ++ reverseMonitor.drops := by
  have quiet : bridge.filterMap dropID = [] := by rw [filtered_ids, joined.noDrop]; rfl
  simp only [recorded, List.filterMap_append, quiet, List.append_nil, forward.actual_ids, reverse.actual_ids]

theorem actual_drop_count (joined : Joined forwardEnd reverseCut bridge) :
    ((recorded forward reverse bridge).filter isDrop).length = forwardMonitor.drops.length + reverseMonitor.drops.length := by
  simp only [recorded, List.filter_append, joined.noDrop, List.append_nil, List.length_append,
    forward.actual_drop_count, reverse.actual_drop_count]

theorem losses_count : (losses forward reverse).length = forwardMonitor.drops.length + reverseMonitor.drops.length := by
  simp only [losses, List.length_append, List.length_map, forward.dropIDs, reverse.dropIDs]

theorem losses_ids : (losses forward reverse).map lossID = forwardMonitor.drops ++ reverseMonitor.drops := by
  simp only [losses, List.map_append, List.map_map, Function.comp_def, lossID, forward.dropIDs, reverse.dropIDs]

theorem actual_global_ids (joined : Joined forwardEnd reverseCut bridge) :
    (recorded forward reverse bridge).filterMap dropID = (losses forward reverse).map lossID :=
  (actual_drop_ids joined).trans (losses_ids (forward := forward) (reverse := reverse)).symm

theorem loss_recorded (joined : Joined forwardEnd reverseCut bridge) (member : entry ∈ losses forward reverse) :
    lossStep entry ∈ recorded forward reverse bridge := by
  have selected : lossStep entry ∈ (losses forward reverse).map lossStep := List.mem_map.mpr ⟨entry, member, rfl⟩
  rw [← actual_drop_steps joined] at selected
  exact (List.mem_filter.mp selected).1

theorem loss_event (member : entry ∈ losses forward reverse) : (lossStep entry).event = .dropPacket (lossID entry) := by
  rcases List.mem_append.mp member with first | second
  · obtain ⟨loss, _, same⟩ := List.mem_map.mp first
    subst entry
    exact loss.facts.event
  · obtain ⟨loss, _, same⟩ := List.mem_map.mp second
    subst entry
    exact loss.facts.event

theorem reverseIndex_injective (same : reverseIndex forward first = reverseIndex forward second) : first = second :=
  Nat.add_left_cancel same

theorem reverse_after_forward (old : position < forward.book.losses.length) (next : Nat) :
    position < reverseIndex forward next := by unfold reverseIndex; omega

theorem forward_lookup {position : Nat} {loss : Loss forwardInitial forwardConfig}
    (found : forward.book.losses[position]? = some loss) : (losses forward reverse)[position]? = some (.inl loss) := by
  rw [losses, List.getElem?_append_left (by
    simp only [List.length_map]
    exact (List.getElem?_eq_some_iff.mp found).1), List.getElem?_map, found]
  rfl

theorem reverse_lookup {position : Nat} {loss : Loss reverseInitial reverseConfig}
    (found : reverse.book.losses[position]? = some loss) :
    (losses forward reverse)[reverseIndex forward position]? = some (.inr loss) := by
  rw [losses, List.getElem?_append_right (by simp only [List.length_map, reverseIndex]; omega),
    List.length_map, reverseIndex, Nat.add_sub_cancel_left, List.getElem?_map, found]
  rfl

theorem spent_distinct : (spentPositions forward reverse).Nodup := by
  apply List.nodup_append.mpr
  refine ⟨forward.valid.distinct, ?_, ?_⟩
  · exact List.Pairwise.map (reverseIndex forward)
      (by intro first second different same; exact different (reverseIndex_injective same)) reverse.valid.distinct
  · intro old member next mapped same
    obtain ⟨position, _, equality⟩ := List.mem_map.mp mapped
    have bound := forward.valid.position_bound member
    have after := reverse_after_forward bound position
    omega

theorem spent_bound (member : position ∈ spentPositions forward reverse) : position < (losses forward reverse).length := by
  simp only [spentPositions, List.mem_append] at member
  simp only [losses, List.length_append, List.length_map]
  rcases member with first | second
  · have bound := forward.valid.position_bound first
    omega
  · obtain ⟨localPosition, localMember, same⟩ := List.mem_map.mp second
    have bound := reverse.valid.position_bound localMember
    unfold reverseIndex at same
    omega

theorem spent_count : (spentPositions forward reverse).length = forwardMonitor.retries + reverseMonitor.retries := by
  simp only [spentPositions, List.length_append, List.length_map, CampusTCPTwoProgressLossHistory.Book.positions,
    forward.retries, reverse.retries]

theorem spent_le_losses : (spentPositions forward reverse).length ≤ (losses forward reverse).length := by
  have subset : spentPositions forward reverse ⊆ List.range (losses forward reverse).length := by
    intro position member
    exact List.mem_range.mpr (spent_bound member)
  simpa only [List.length_range] using (spent_distinct (forward := forward) (reverse := reverse)).length_le_of_subset subset

theorem forward_spent {entry : CampusTCPTwoProgressLossHistory.Spent forwardInitial forwardConfig}
    (member : entry ∈ forward.book.spent) : (losses forward reverse)[entry.position]? = some (.inl entry.loss) :=
  forward_lookup (reverse := reverse) (forward.valid.spent entry member)

theorem reverse_spent {entry : CampusTCPTwoProgressLossHistory.Spent reverseInitial reverseConfig}
    (member : entry ∈ reverse.book.spent) :
    (losses forward reverse)[reverseIndex forward entry.position]? = some (.inr entry.loss) :=
  reverse_lookup (forward := forward) (reverse.valid.spent entry member)

theorem reverse_cause {role : CampusTCPTwoProgressSender.Part} {position : Nat}
    (chosen : reverse.book.cause role = some position) :
    ∃ loss, (losses forward reverse)[reverseIndex forward position]? = some (.inr loss) ∧
      CampusTCPTwoProgressLossHistory.Supports loss role ∧ reverseIndex forward position ∉ spentPositions forward reverse := by
  obtain ⟨loss, found, support, unused⟩ := reverse.valid.cause position chosen
  refine ⟨loss, reverse_lookup found, support, ?_⟩
  intro member
  rcases List.mem_append.mp member with first | second
  · have bound := forward.valid.position_bound first
    have after := reverse_after_forward bound position
    omega
  · obtain ⟨old, member, same⟩ := List.mem_map.mp second
    exact unused ((reverseIndex_injective same) ▸ member)

theorem actual_timeout_count (joined : Joined forwardEnd reverseCut bridge)
    (first : OwnedTimeouts sender forward.suffix) (second : OwnedTimeouts sender.other reverse.suffix) :
    ((recorded forward reverse bridge).filter isTimeoutOutput).length = forwardMonitor.retries + reverseMonitor.retries := by
  have left := List.filter_congr first
  have right := List.filter_congr second
  simp only [recorded, List.filter_append, joined.noTimeout, List.append_nil, List.length_append,
    left, right, forward.actual_timeout_count, reverse.actual_timeout_count]

theorem timeout_le_actual_drops (joined : Joined forwardEnd reverseCut bridge)
    (first : OwnedTimeouts sender forward.suffix) (second : OwnedTimeouts sender.other reverse.suffix) :
    ((recorded forward reverse bridge).filter isTimeoutOutput).length ≤ ((recorded forward reverse bridge).filter isDrop).length := by
  rw [actual_timeout_count joined first second, actual_drop_count joined, ← spent_count, ← losses_count]
  exact spent_le_losses (forward := forward) (reverse := reverse)

theorem remaining_budget (allowance : Nat) (first : forwardMonitor.drops.length ≤ allowance)
    (second : reverseMonitor.drops.length ≤ allowance - forwardMonitor.drops.length) :
    forwardMonitor.drops.length + reverseMonitor.drops.length ≤ allowance := by omega

theorem actual_drop_budget (joined : Joined forwardEnd reverseCut bridge) (allowance : Nat)
    (first : forwardMonitor.drops.length ≤ allowance)
    (second : reverseMonitor.drops.length ≤ allowance - forwardMonitor.drops.length) :
    ((recorded forward reverse bridge).filter isDrop).length ≤ allowance := by
  rw [actual_drop_count joined]
  exact remaining_budget allowance first second

theorem actual_timeout_budget (joined : Joined forwardEnd reverseCut bridge) (allowance : Nat)
    (first : forwardMonitor.drops.length ≤ allowance)
    (second : reverseMonitor.drops.length ≤ allowance - forwardMonitor.drops.length)
    (firstOwned : OwnedTimeouts sender forward.suffix) (secondOwned : OwnedTimeouts sender.other reverse.suffix) :
    ((recorded forward reverse bridge).filter isTimeoutOutput).length ≤ allowance :=
  Nat.le_trans (timeout_le_actual_drops joined firstOwned secondOwned) (actual_drop_budget joined allowance first second)

theorem forward_owned (healthy : forwardMonitor.mode ≠ .invalid) (senderEq : forwardConfig.sender = sender) :
    OwnedTimeouts sender forward.suffix := by
  have own := owned_of_healthy_fold forwardConfig .initial forward.suffix (by rw [forward.observed]; exact healthy)
  rw [senderEq] at own
  exact own

theorem reverse_owned (healthy : reverseMonitor.mode ≠ .invalid) (senderEq : reverseConfig.sender = sender.other) :
    OwnedTimeouts sender.other reverse.suffix := by
  have own := owned_of_healthy_fold reverseConfig .initial reverse.suffix (by rw [reverse.observed]; exact healthy)
  rw [senderEq] at own
  exact own

theorem actual_timeout_count_of_healthy (joined : Joined forwardEnd reverseCut bridge)
    (firstHealthy : forwardMonitor.mode ≠ .invalid) (secondHealthy : reverseMonitor.mode ≠ .invalid)
    (firstSender : forwardConfig.sender = sender) (secondSender : reverseConfig.sender = sender.other) :
    ((recorded forward reverse bridge).filter isTimeoutOutput).length = forwardMonitor.retries + reverseMonitor.retries :=
  actual_timeout_count joined (forward_owned firstHealthy firstSender) (reverse_owned secondHealthy secondSender)

theorem timeout_le_actual_drops_of_healthy (joined : Joined forwardEnd reverseCut bridge)
    (firstHealthy : forwardMonitor.mode ≠ .invalid) (secondHealthy : reverseMonitor.mode ≠ .invalid)
    (firstSender : forwardConfig.sender = sender) (secondSender : reverseConfig.sender = sender.other) :
    ((recorded forward reverse bridge).filter isTimeoutOutput).length ≤ ((recorded forward reverse bridge).filter isDrop).length :=
  timeout_le_actual_drops joined (forward_owned firstHealthy firstSender) (reverse_owned secondHealthy secondSender)

theorem actual_timeout_budget_of_healthy (joined : Joined forwardEnd reverseCut bridge) (allowance : Nat)
    (first : forwardMonitor.drops.length ≤ allowance)
    (second : reverseMonitor.drops.length ≤ allowance - forwardMonitor.drops.length)
    (firstHealthy : forwardMonitor.mode ≠ .invalid) (secondHealthy : reverseMonitor.mode ≠ .invalid)
    (firstSender : forwardConfig.sender = sender) (secondSender : reverseConfig.sender = sender.other) :
    ((recorded forward reverse bridge).filter isTimeoutOutput).length ≤ allowance :=
  actual_timeout_budget joined allowance first second (forward_owned firstHealthy firstSender) (reverse_owned secondHealthy secondSender)

end Netlib.Check.CampusTCPTwoExchangeLoss
