import Netlib.Check.CampusTCPTwoTransferMonitor
import Netlib.Check.CampusTCPTwoProgressLossHistory
import Netlib.Check.CampusTCPTwoExchangeLoss

/-!
# Loss causes on the actual transfer trace

Each drop retains its current owner, monitor, and actual source.
Controls and drain slots remain in the same observed suffix.
-/

namespace Netlib.Check.CampusTCPTwoTransferLoss

open Protocol Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPRoundPhaseBase (Move)
open CampusTCPTwoProgressStart CampusTCPTwoProgressWire
open CampusTCPTwoProgressLossHistory (Head)

namespace M
export CampusTCPTwoProgressMonitor (DropTarget dropTarget)
end M
namespace W
export CampusTCPTwoTransferMonitor (Config Monitor Allowed observe)
end W
namespace D
export CampusTCPRecoveryRoundDrop (Facts)
end D
namespace S
export CampusTCPTwoProgressSender (Part)
end S
local notation "Config" => CampusTCPTwoTransferMonitor.Config

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current next : Cut input complete} {sender : Actor} {gateway : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper} {config : Config}
variable {monitor : W.Monitor} {actual : Step input} {id : Nat} {target : M.DropTarget}

structure Loss (initial : TwoWriteInitial cut sender gateway lower upper) (config : Config) where
  before : Cut input complete
  monitor : W.Monitor
  retained : cut.report.steps <+: before.report.steps
  observed : (before.report.steps.drop cut.report.steps.length).foldl (W.observe config) .initial = monitor
  actual : Step input
  move : Move before actual
  id : Nat
  facts : D.Facts before.report.final id actual
  target : M.DropTarget
  phase : monitor.exchange.mode = .forward
  selected : M.dropTarget (config.at before.report.final).forward before.report.final monitor.exchange.forward id = some target
  allowed : W.Allowed config before.report.final monitor actual.event

def transitSource : Transit input → Produced input.active input.passive
  | .ingress _ produced => produced
  | .link _ served _ _ => served.ticket.value.produced

def Loss.source (loss : Loss initial config) : Produced input.active input.passive :=
  transitSource loss.facts.resolved.item.value.payload

inductive Supports (loss : Loss initial config) : S.Part → Prop
  | lower (target : loss.target = .lower) (actor : loss.source.actor = sender)
      (fields : DataFields initial 0 lower loss.source) : Supports loss .lower
  | upper (target : loss.target = .upper) (actor : loss.source.actor = sender)
      (fields : DataFields initial lower.length upper loss.source) : Supports loss .upper
  | retry (role : S.Part) (target : loss.target = .retry) (head : Head initial loss.before role)
      (actor : loss.source.actor = sender)
      (fields : DataFields initial (role.offset lower) (role.bytes lower upper) loss.source) : Supports loss role
  | ack (role : S.Part) (target : loss.target = .ack) (head : Head initial loss.before role)
      (count : Nat) (actor : loss.source.actor = sender.other) (fields : AckFields initial count loss.source)
      (within : count ≤ lower.length + upper.length)
      (covered : role.offset lower + (role.bytes lower upper).length ≤ count) : Supports loss role

variable {loss : Loss initial config} {role : S.Part}

theorem Supports.ack_positive (_head : Head initial current role)
    (covered : role.offset lower + (role.bytes lower upper).length ≤ count) : 0 < count := by
  have first := List.length_pos_iff.mpr initial.lowerNonempty
  have second := List.length_pos_iff.mpr initial.upperNonempty
  cases role <;> simp only [CampusTCPTwoProgressSender.Part.offset, CampusTCPTwoProgressSender.Part.bytes] at covered <;> omega

theorem ack_count_unique (first : AckFields initial firstCount produced) (second : AckFields initial secondCount produced)
    (firstBound : firstCount ≤ lower.length + upper.length) (secondBound : secondCount ≤ lower.length + upper.length) :
    firstCount = secondCount := by
  have bound : lower.length + upper.length < Seq.modulus := by
    have epoch := initial.geometry.epoch
    unfold Seq.halfSpace Seq.modulus at *
    omega
  have firstSmall := Nat.lt_of_le_of_lt firstBound bound
  have secondSmall := Nat.lt_of_le_of_lt secondBound bound
  have same := congrArg (Seq.distance (endpoint cut.endpoints sender).core.sendNext)
    (first.acknowledgment.symm.trans second.acknowledgment)
  simpa only [Seq.distance_add, Nat.mod_eq_of_lt firstSmall, Nat.mod_eq_of_lt secondSmall] using same

theorem Supports.no_gap_ack (target : loss.target = .ack) (fields : AckFields initial 0 loss.source) :
    ¬Supports loss role := by
  intro support
  cases support with
  | lower different actor data => rw [target] at different; cases different
  | upper different actor data => rw [target] at different; cases different
  | retry role different head actor data => rw [target] at different; cases different
  | ack role selected head count actor bounded within covered =>
    have zero := ack_count_unique bounded fields within (Nat.zero_le _)
    have positive := Supports.ack_positive head covered
    omega

structure Spent (initial : TwoWriteInitial cut sender gateway lower upper) (config : Config) where
  position : Nat
  loss : Loss initial config
  role : S.Part
  support : Supports loss role
  before : Cut input complete
  monitor : W.Monitor
  observed : (before.report.steps.drop cut.report.steps.length).foldl (W.observe config) .initial = monitor
  phase : monitor.exchange.mode = .forward
  head : Head initial before role
  earlier : loss.move.after.report.steps <+: before.report.steps
  actual : Step input
  move : Move before actual
  event : actual.event = .timeout sender true
  allowed : W.Allowed config before.report.final monitor actual.event

structure Book (initial : TwoWriteInitial cut sender gateway lower upper) (config : Config) where
  losses : List (Loss initial config) := []
  spent : List (Spent initial config) := []
  lower : Option Nat := none
  upper : Option Nat := none

def Book.positions (book : Book initial config) : List Nat := book.spent.map (·.position)

def Book.cause (book : Book initial config) : S.Part → Option Nat
  | .lower => book.lower
  | .upper => book.upper

def CauseValid (book : Book initial config) (role : S.Part) : Prop :=
  ∀ position, book.cause role = some position → ∃ loss,
    book.losses[position]? = some loss ∧ Supports loss role ∧ position ∉ book.positions

structure Book.Valid (book : Book initial config) : Prop where
  spent : ∀ entry ∈ book.spent, book.losses[entry.position]? = some entry.loss
  distinct : book.positions.Nodup
  lower : CauseValid book .lower
  upper : CauseValid book .upper
  apart : ∀ position, book.lower = some position → book.upper ≠ some position

variable {book : Book initial config} {position : Nat}

def Book.empty (initial : TwoWriteInitial cut sender gateway lower upper) (config : Config) : Book initial config := {}

theorem Book.empty_valid (initial : TwoWriteInitial cut sender gateway lower upper) (config : Config) :
    (Book.empty initial config).Valid := by
  refine ⟨by simp [Book.empty], List.nodup_nil, ?_, ?_, ?_⟩
  all_goals simp [CauseValid, Book.cause, Book.empty]

theorem Book.Valid.cause (valid : book.Valid) : CauseValid book role := by
  cases role
  · exact valid.lower
  · exact valid.upper

theorem Book.Valid.position_bound (valid : book.Valid) (member : position ∈ book.positions) : position < book.losses.length := by
  obtain ⟨entry, present, same⟩ := List.mem_map.mp member
  rw [← same]
  exact ((List.getElem?_eq_some_iff).mp (valid.spent entry present)).1

theorem Book.Valid.spent_le (valid : book.Valid) : book.spent.length ≤ book.losses.length := by
  have subset : book.positions ⊆ List.range book.losses.length := by
    intro position member
    exact List.mem_range.mpr (valid.position_bound member)
  have bound := valid.distinct.length_le_of_subset subset
  simpa only [Book.positions, List.length_map, List.length_range] using bound

theorem Book.Valid.cause_credit (valid : book.Valid) (chosen : book.cause role = some position) :
    book.spent.length < book.losses.length := by
  obtain ⟨loss, found, _, unused⟩ := valid.cause position chosen
  have unique : (book.positions ++ [position]).Nodup := by
    apply List.nodup_append.mpr
    refine ⟨valid.distinct, by simp, ?_⟩
    intro prior member fresh singleton
    have same := List.mem_singleton.mp singleton
    subst fresh
    exact fun equal => unused (equal ▸ member)
  have subset : book.positions ++ [position] ⊆ List.range book.losses.length := by
    intro selected member
    apply List.mem_range.mpr
    rcases List.mem_append.mp member with old | fresh
    · exact valid.position_bound old
    · have same := List.mem_singleton.mp fresh
      subst selected
      exact (List.getElem?_eq_some_iff.mp found).1
  have bound := unique.length_le_of_subset subset
  simp only [List.length_append, Book.positions, List.length_map, List.length_cons, List.length_nil,
    Nat.zero_add, List.length_range] at bound
  omega

private theorem lookup_append {losses : List α} {position : Nat} {loss fresh : α}
    (found : losses[position]? = some loss) :
    (losses ++ [fresh])[position]? = some loss := by
  rw [List.getElem?_append_left ((List.getElem?_eq_some_iff.mp found).1)]
  exact found

def Book.appendLoss (book : Book initial config) (loss : Loss initial config) : Book initial config :=
  { book with losses := book.losses ++ [loss] }

theorem Book.Valid.appendLoss (valid : book.Valid) (loss : Loss initial config) : (book.appendLoss loss).Valid := by
  refine ⟨fun entry member => lookup_append (valid.spent entry member), valid.distinct, ?_, ?_, valid.apart⟩
  · intro position selected
    change book.cause .lower = some position at selected
    obtain ⟨prior, found, support, unused⟩ := valid.lower position selected
    exact ⟨prior, lookup_append found, support, unused⟩
  · intro position selected
    change book.cause .upper = some position at selected
    obtain ⟨prior, found, support, unused⟩ := valid.upper position selected
    exact ⟨prior, lookup_append found, support, unused⟩

def Book.clearLower (book : Book initial config) : Book initial config := { book with lower := none }
def Book.clearAll (book : Book initial config) : Book initial config := { book with lower := none, upper := none }

theorem Book.Valid.clearLower (valid : book.Valid) : book.clearLower.Valid := by
  exact ⟨valid.spent, valid.distinct, by simp [CauseValid, Book.cause, Book.clearLower], valid.upper,
    by simp [Book.clearLower]⟩

theorem Book.Valid.clearAll (valid : book.Valid) : book.clearAll.Valid := by
  refine ⟨valid.spent, valid.distinct, ?_, ?_, ?_⟩
  all_goals simp [CauseValid, Book.cause, Book.clearAll]

private def remember (book : Book initial config) (role : S.Part) (position : Nat) : Book initial config :=
  match role with
  | .lower => { book with lower := some position }
  | .upper => { book with upper := some position }

private theorem remember_valid (valid : book.Valid) (found : book.losses[position]? = some loss)
    (support : Supports loss role) (unused : position ∉ book.positions)
    (apart : book.cause (match role with | .lower => .upper | .upper => .lower) ≠ some position) :
    (remember book role position).Valid := by
  cases role
  · refine ⟨valid.spent, valid.distinct, ?_, valid.upper, ?_⟩
    · intro chosen selected
      have same : position = chosen := Option.some.inj selected
      subst chosen
      exact ⟨loss, found, support, unused⟩
    · intro chosen selected
      have same : position = chosen := Option.some.inj selected
      subst chosen
      exact apart
  · refine ⟨valid.spent, valid.distinct, valid.lower, ?_, ?_⟩
    · intro chosen selected
      have same : position = chosen := Option.some.inj selected
      subst chosen
      exact ⟨loss, found, support, unused⟩
    · intro chosen selected conflict
      have same : position = chosen := Option.some.inj conflict
      subst chosen
      exact apart selected

private def spend (book : Book initial config) (entry : Spent initial config) : Book initial config :=
  match entry.role with
  | .lower => { book with spent := book.spent ++ [entry], lower := none }
  | .upper => { book with spent := book.spent ++ [entry], upper := none }

private theorem spend_valid (valid : book.Valid) (entry : Spent initial config)
    (chosen : book.cause entry.role = some entry.position)
    (found : book.losses[entry.position]? = some entry.loss) : (spend book entry).Valid := by
  obtain ⟨_, _, _, unused⟩ := valid.cause entry.position chosen
  have positions : (spend book entry).positions = book.positions ++ [entry.position] := by
    cases role : entry.role <;> simp only [spend, role, Book.positions, List.map_append, List.map_cons, List.map_nil]
  have entries : (spend book entry).spent = book.spent ++ [entry] := by cases role : entry.role <;> simp only [spend, role]
  have losses : (spend book entry).losses = book.losses := by cases role : entry.role <;> simp only [spend, role]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [entries, losses]
    intro selected member
    rcases List.mem_append.mp member with old | fresh
    · exact valid.spent selected old
    · have same := List.mem_singleton.mp fresh
      subst selected
      exact found
  · rw [positions]
    apply List.nodup_append.mpr
    refine ⟨valid.distinct, by simp, ?_⟩
    intro old member fresh singleton
    have same := List.mem_singleton.mp singleton
    subst fresh
    exact fun equal => unused (equal ▸ member)
  · intro position selected
    cases role : entry.role with
    | lower => simp only [spend, role, Book.cause] at selected; cases selected
    | upper =>
      simp only [spend, role, Book.cause] at selected
      obtain ⟨loss, stored, support, prior⟩ := valid.lower position selected
      refine ⟨loss, by rw [losses]; exact stored, support, ?_⟩
      rw [positions, List.mem_append, List.mem_singleton]
      intro conflict
      rcases conflict with old | same
      · exact prior old
      · exact valid.apart position selected (by simpa only [Book.cause, role, same] using chosen)
  · intro position selected
    cases role : entry.role with
    | upper => simp only [spend, role, Book.cause] at selected; cases selected
    | lower =>
      simp only [spend, role, Book.cause] at selected
      obtain ⟨loss, stored, support, prior⟩ := valid.upper position selected
      refine ⟨loss, by rw [losses]; exact stored, support, ?_⟩
      rw [positions, List.mem_append, List.mem_singleton]
      intro conflict
      rcases conflict with old | same
      · exact prior old
      · have lower : book.lower = some position := by simpa only [Book.cause, role, same] using chosen
        exact valid.apart position lower selected
  · intro position selected
    cases role : entry.role with
    | lower => simp only [spend, role] at selected; cases selected
    | upper => simp only [spend, role, ne_eq, reduceCtorEq, not_false_eq_true]

def Book.rememberCause (book : Book initial config) (role : S.Part) (position : Nat) : Book initial config :=
  remember book role position

theorem Book.Valid.rememberCause (valid : book.Valid) (found : book.losses[position]? = some loss)
    (support : Supports loss role) (unused : position ∉ book.positions)
    (apart : book.cause (match role with | .lower => .upper | .upper => .lower) ≠ some position) :
    (book.rememberCause role position).Valid := remember_valid valid found support unused apart

def Book.spendCause (book : Book initial config) (entry : Spent initial config) : Book initial config :=
  spend book entry

theorem Book.Valid.spendCause (valid : book.Valid) (entry : Spent initial config)
    (chosen : book.cause entry.role = some entry.position)
    (found : book.losses[entry.position]? = some entry.loss) : (book.spendCause entry).Valid :=
  spend_valid valid entry chosen found

theorem Book.spendCause_losses (book : Book initial config) (entry : Spent initial config) :
    (book.spendCause entry).losses = book.losses := by cases role : entry.role <;> simp only [Book.spendCause, spend, role]

theorem Book.spendCause_spent (book : Book initial config) (entry : Spent initial config) :
    (book.spendCause entry).spent = book.spent ++ [entry] := by cases role : entry.role <;> simp only [Book.spendCause, spend, role]

theorem Book.rememberCause_losses (book : Book initial config) (role : S.Part) (position : Nat) :
    (book.rememberCause role position).losses = book.losses := by cases role <;> rfl

theorem Book.rememberCause_spent (book : Book initial config) (role : S.Part) (position : Nat) :
    (book.rememberCause role position).spent = book.spent := by cases role <;> rfl

end Netlib.Check.CampusTCPTwoTransferLoss
