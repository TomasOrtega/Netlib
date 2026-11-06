import Netlib.Check.CampusTCPTwoProgressMonitorFacts
import Netlib.Check.CampusTCPTwoProgressWire
import Netlib.Check.CampusTCPTwoProgressSender
import Netlib.Check.CampusTCPRecoveryRoundDrop

/-!
# Actual losses and spent timeout causes

Causes name selected drops in the retained suffix.
The phase proof must derive a current cause before it spends one.
-/

namespace Netlib.Check.CampusTCPTwoProgressLossHistory

open Protocol Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPRoundPhaseBase (Move)
open CampusTCPTwoProgressStart CampusTCPTwoProgressWire

namespace M
export CampusTCPTwoProgressMonitor (Monitor DropTarget Allowed dropTarget observe)
end M
namespace D
export CampusTCPRecoveryRoundDrop (Facts)
end D
namespace S
export CampusTCPTwoProgressSender (Part)
end S
local notation "Config" => CampusTCPTwoProgressMonitor.Config

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current next : Cut input complete} {sender : Actor} {gateway : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper} {config : Config}
variable {monitor : M.Monitor} {actual : Step input} {id : Nat} {target : M.DropTarget}

structure Head (initial : TwoWriteInitial cut sender gateway lower upper) (current : Cut input complete) (role : S.Part) where
  recovery : Recovery.State
  runtime : (endpoint current.endpoints sender).recovery = some recovery
  entry : Recovery.Outstanding
  tail : List Recovery.Outstanding
  ledger : recovery.outstanding = entry :: tail
  identity : entry.id = initial.senderState.idle.recovery.nextId + role.index
  position : entry.start = initial.senderState.idle.recovery.frontier + role.offset lower
  count : entry.count = (role.bytes lower upper).length

structure Loss (initial : TwoWriteInitial cut sender gateway lower upper) (config : Config) where
  before : Cut input complete
  monitor : M.Monitor
  retained : cut.report.steps <+: before.report.steps
  observed : (before.report.steps.drop cut.report.steps.length).foldl (M.observe config) .initial = monitor
  actual : Step input
  move : Move before actual
  id : Nat
  facts : D.Facts before.report.final id actual
  target : M.DropTarget
  selected : M.dropTarget config before.report.final monitor id = some target
  allowed : M.Allowed config before.report.final monitor actual.event

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
  head : Head initial before role
  earlier : loss.move.after.report.steps <+: before.report.steps
  actual : Step input
  move : Move before actual
  event : actual.event = .timeout sender true

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

def isDrop (actual : Step input) : Bool :=
  match actual.event with | .dropPacket _ => true | _ => false

def dropID (actual : Step input) : Option Nat :=
  match actual.event with | .dropPacket id => some id | _ => none

def isTimeout (sender : Actor) (actual : Step input) : Bool :=
  match actual.event with | .timeout actor true => decide (actor = sender) | _ => false

structure History (initial : TwoWriteInitial cut sender gateway lower upper) (config : Config)
    (current : Cut input complete) (monitor : M.Monitor) where
  suffix : List (Step input)
  steps : current.report.steps = cut.report.steps ++ suffix
  observed : suffix.foldl (M.observe config) .initial = monitor
  book : Book initial config
  valid : book.Valid
  dropSteps : suffix.filter isDrop = book.losses.map (·.actual)
  timeoutSteps : suffix.filter (isTimeout sender) = book.spent.map (·.actual)
  dropIDs : monitor.drops = book.losses.map (·.id)
  retries : book.spent.length = monitor.retries
  lossesPast : ∀ loss ∈ book.losses, loss.move.after.report.steps <+: current.report.steps
  timeoutsPast : ∀ entry ∈ book.spent, entry.move.after.report.steps <+: current.report.steps

def History.empty (initial : TwoWriteInitial cut sender gateway lower upper) (config : Config) :
    History initial config cut .initial :=
  ⟨[], (List.append_nil _).symm, rfl, Book.empty initial config, Book.empty_valid initial config,
    rfl, rfl, rfl, rfl, by simp [Book.empty], by simp [Book.empty]⟩

variable {history : History initial config current monitor}

theorem History.count (history : History initial config current monitor) : monitor.retries ≤ monitor.drops.length := by
  rw [← history.retries, history.dropIDs, List.length_map]
  exact history.valid.spent_le

theorem History.credit (history : History initial config current monitor)
    (chosen : history.book.cause role = some position) : monitor.retries < monitor.drops.length := by
  rw [← history.retries, history.dropIDs, List.length_map]
  exact history.valid.cause_credit chosen

private theorem filtered_drop_ids (steps : List (Step input)) : steps.filterMap dropID = (steps.filter isDrop).filterMap dropID := by
  induction steps with
  | nil => rfl
  | cons actual rest ih => cases event : actual.event <;>
      simp only [List.filterMap_cons, List.filter_cons, dropID, isDrop, event, Bool.false_eq_true,
        ite_false, ite_true, ih]

private theorem loss_drop_ids (losses : List (Loss initial config)) :
    (losses.map (·.actual)).filterMap dropID = losses.map (·.id) := by
  induction losses with
  | nil => rfl
  | cons loss rest ih => simp only [List.map_cons, List.filterMap_cons, dropID, loss.facts.event, ih]

theorem History.actual_ids (history : History initial config current monitor) :
    history.suffix.filterMap dropID = monitor.drops := by
  rw [filtered_drop_ids, history.dropSteps, loss_drop_ids, history.dropIDs]

theorem History.actual_drop_count (history : History initial config current monitor) :
    (history.suffix.filter isDrop).length = monitor.drops.length := by
  rw [history.dropSteps, history.dropIDs, List.length_map, List.length_map]

theorem History.actual_timeout_count (history : History initial config current monitor) :
    (history.suffix.filter (isTimeout sender)).length = monitor.retries := by
  rw [history.timeoutSteps, List.length_map, history.retries]

def History.reframe (history : History initial config current monitor) (same : next.report.steps = current.report.steps) :
    History initial config next monitor :=
  { history with
    steps := same.trans history.steps
    lossesPast := fun loss member => same.symm ▸ history.lossesPast loss member
    timeoutsPast := fun entry member => same.symm ▸ history.timeoutsPast entry member }

def History.append (history : History initial config current monitor) (move : Move current actual)
    (noDrop : isDrop actual = false) (noTimeout : isTimeout sender actual = false)
    (dropIDs : (M.observe config monitor actual).drops = monitor.drops)
    (retries : (M.observe config monitor actual).retries = monitor.retries) :
    History initial config move.after (M.observe config monitor actual) := by
  refine ⟨history.suffix ++ [actual], ?_, ?_, history.book, history.valid, ?_, ?_,
    dropIDs.trans history.dropIDs, history.retries.trans retries.symm, ?_, ?_⟩
  · rw [move.history, history.steps, List.append_assoc]
  · rw [List.foldl_append, history.observed]
    rfl
  · simp only [List.filter_append, List.filter_cons, noDrop, Bool.false_eq_true, ite_false,
      List.filter_nil, List.append_nil, history.dropSteps]
  · simp only [List.filter_append, List.filter_cons, noTimeout, Bool.false_eq_true, ite_false,
      List.filter_nil, List.append_nil, history.timeoutSteps]
  · exact fun loss member => (history.lossesPast loss member).trans move.retained
  · exact fun entry member => (history.timeoutsPast entry member).trans move.retained

def History.selectedLoss (history : History initial config current monitor) (move : Move current actual)
    (facts : D.Facts current.report.final id actual)
    (selected : M.dropTarget config current.report.final monitor id = some target)
    (allowed : M.Allowed config current.report.final monitor actual.event) : Loss initial config where
  before := current
  monitor := monitor
  retained := by rw [history.steps]; exact List.prefix_append _ _
  observed := by rw [history.steps, List.drop_append_length]; exact history.observed
  actual := actual
  move := move
  id := id
  facts := facts
  target := target
  selected := selected
  allowed := allowed

def History.drop (history : History initial config current monitor) (move : Move current actual)
    (facts : D.Facts current.report.final id actual)
    (selected : M.dropTarget config current.report.final monitor id = some target)
    (allowed : M.Allowed config current.report.final monitor actual.event) :
    History initial config move.after (M.observe config monitor actual) := by
  let loss := history.selectedLoss move facts selected allowed
  have observed := CampusTCPTwoProgressMonitorFacts.observe_drop config monitor actual move.supported move.passed
    (by simpa only [move.beforeEq] using allowed) facts.event
  have counters := CampusTCPTwoProgressMonitorFacts.drop_counters config monitor actual id
    (by simpa only [move.beforeEq] using selected)
  rw [← observed] at counters
  change ((M.observe config monitor actual).retries, (M.observe config monitor actual).drops) =
    (monitor.retries, monitor.drops ++ [id]) at counters
  have counts := Prod.mk.inj counters
  refine ⟨history.suffix ++ [actual], ?_, ?_, history.book.appendLoss loss, history.valid.appendLoss loss,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [move.history, history.steps, List.append_assoc]
  · rw [List.foldl_append, history.observed]
    rfl
  · simp only [List.filter_append, List.filter_cons, isDrop, facts.event, List.filter_nil, ite_true,
      history.dropSteps, Book.appendLoss, List.map_append, List.map_cons, List.map_nil]
    rfl
  · simp only [List.filter_append, List.filter_cons, isTimeout, facts.event, List.filter_nil,
      Bool.false_eq_true, ite_false, List.append_nil, Book.appendLoss]
    exact history.timeoutSteps
  · rw [counts.2, history.dropIDs]
    simp only [Book.appendLoss, List.map_append, List.map_cons, List.map_nil]
    rfl
  · exact history.retries.trans counts.1.symm
  · intro chosen member
    rcases List.mem_append.mp member with old | fresh
    · exact (history.lossesPast chosen old).trans move.retained
    · have same := List.mem_singleton.mp fresh
      subst chosen
      exact List.prefix_refl _
  · exact fun entry member => (history.timeoutsPast entry member).trans move.retained

def History.clearLower (history : History initial config current monitor) : History initial config current monitor :=
  { history with book := history.book.clearLower, valid := history.valid.clearLower }

def History.clearAll (history : History initial config current monitor) : History initial config current monitor :=
  { history with book := history.book.clearAll, valid := history.valid.clearAll }

theorem History.clearLower_upper (history : History initial config current monitor) :
    history.clearLower.book.upper = history.book.upper := rfl

private theorem fresh_valid (valid : book.Valid) (loss : Loss initial config) (support : Supports loss role) :
    (remember (book.appendLoss loss) role book.losses.length).Valid := by
  apply remember_valid (valid.appendLoss loss) (List.getElem?_concat_length) support
  · change book.losses.length ∉ book.positions
    intro member
    have bound := valid.position_bound member
    omega
  · cases role
    · intro selected
      obtain ⟨prior, found, _, _⟩ := valid.upper book.losses.length selected
      have bound := (List.getElem?_eq_some_iff.mp found).1
      omega
    · intro selected
      obtain ⟨prior, found, _, _⟩ := valid.lower book.losses.length selected
      have bound := (List.getElem?_eq_some_iff.mp found).1
      omega

private def rememberHistory (history : History initial config current monitor) (role : S.Part) (position : Nat)
    (valid : (remember history.book role position).Valid) : History initial config current monitor := by
  cases role <;> exact { history with book := remember history.book _ position, valid := valid }

def History.drop_lower (history : History initial config current monitor) (move : Move current actual)
    (facts : D.Facts current.report.final id actual)
    (selected : M.dropTarget config current.report.final monitor id = some target)
    (allowed : M.Allowed config current.report.final monitor actual.event)
    (support : Supports (history.selectedLoss move facts selected allowed) .lower) :
    History initial config move.after (M.observe config monitor actual) :=
  rememberHistory (history.drop move facts selected allowed) .lower history.book.losses.length
    (fresh_valid history.valid _ support)

def History.drop_upper (history : History initial config current monitor) (move : Move current actual)
    (facts : D.Facts current.report.final id actual)
    (selected : M.dropTarget config current.report.final monitor id = some target)
    (allowed : M.Allowed config current.report.final monitor actual.event)
    (support : Supports (history.selectedLoss move facts selected allowed) .upper) :
    History initial config move.after (M.observe config monitor actual) :=
  rememberHistory (history.drop move facts selected allowed) .upper history.book.losses.length
    (fresh_valid history.valid _ support)

theorem History.drop_lower_cause (history : History initial config current monitor) (move : Move current actual)
    (facts : D.Facts current.report.final id actual)
    (selected : M.dropTarget config current.report.final monitor id = some target)
    (allowed : M.Allowed config current.report.final monitor actual.event)
    (support : Supports (history.selectedLoss move facts selected allowed) .lower) :
    (history.drop_lower move facts selected allowed support).book.lower = some history.book.losses.length := rfl

theorem History.drop_lower_upper (history : History initial config current monitor) (move : Move current actual)
    (facts : D.Facts current.report.final id actual)
    (selected : M.dropTarget config current.report.final monitor id = some target)
    (allowed : M.Allowed config current.report.final monitor actual.event)
    (support : Supports (history.selectedLoss move facts selected allowed) .lower) :
    (history.drop_lower move facts selected allowed support).book.upper = history.book.upper := rfl

theorem History.drop_upper_cause (history : History initial config current monitor) (move : Move current actual)
    (facts : D.Facts current.report.final id actual)
    (selected : M.dropTarget config current.report.final monitor id = some target)
    (allowed : M.Allowed config current.report.final monitor actual.event)
    (support : Supports (history.selectedLoss move facts selected allowed) .upper) :
    (history.drop_upper move facts selected allowed support).book.upper = some history.book.losses.length := rfl

private theorem cause_support (valid : book.Valid) (chosen : book.cause role = some position)
    (found : book.losses[position]? = some loss) : Supports loss role := by
  obtain ⟨prior, stored, support, _⟩ := valid.cause position chosen
  have same : prior = loss := Option.some.inj (stored.symm.trans found)
  exact same ▸ support

def History.spentEntry (history : History initial config current monitor) (role : S.Part) (position : Nat)
    (loss : Loss initial config) (chosen : history.book.cause role = some position)
    (found : history.book.losses[position]? = some loss) (head : Head initial current role)
    (move : Move current actual) (event : actual.event = .timeout sender true) : Spent initial config where
  position := position
  loss := loss
  role := role
  support := cause_support history.valid chosen found
  before := current
  head := head
  earlier := history.lossesPast loss (List.mem_of_getElem? found)
  actual := actual
  move := move
  event := event

private def consume (history : History initial config current monitor) (role : S.Part) (position : Nat)
    (loss : Loss initial config) (chosen : history.book.cause role = some position)
    (found : history.book.losses[position]? = some loss) (head : Head initial current role)
    (move : Move current actual) (event : actual.event = .timeout sender true)
    (dropIDs : (M.observe config monitor actual).drops = monitor.drops)
    (retries : (M.observe config monitor actual).retries = monitor.retries + 1) :
    History initial config move.after (M.observe config monitor actual) := by
  let entry := history.spentEntry role position loss chosen found head move event
  have entries : (spend history.book entry).spent = history.book.spent ++ [entry] := by
    cases role <;> rfl
  have losses : (spend history.book entry).losses = history.book.losses := by cases role <;> rfl
  refine ⟨history.suffix ++ [actual], ?_, ?_, spend history.book entry,
    spend_valid history.valid entry chosen found, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [move.history, history.steps, List.append_assoc]
  · rw [List.foldl_append, history.observed]
    rfl
  · rw [losses]
    simpa only [List.filter_append, List.filter_cons, isDrop, event, Bool.false_eq_true, ite_false,
      List.filter_nil, List.append_nil] using history.dropSteps
  · rw [entries]
    simp only [List.filter_append, List.filter_cons, isTimeout, event, decide_true, ite_true,
      List.filter_nil, List.map_append, List.map_cons, List.map_nil, history.timeoutSteps]
    rfl
  · rw [losses]
    exact dropIDs.trans history.dropIDs
  · rw [entries, List.length_append, List.length_cons, List.length_nil, Nat.zero_add, history.retries, retries]
  · rw [losses]
    exact fun prior member => (history.lossesPast prior member).trans move.retained
  · rw [entries]
    intro selected member
    rcases List.mem_append.mp member with old | fresh
    · exact (history.timeoutsPast selected old).trans move.retained
    · have same := List.mem_singleton.mp fresh
      subst selected
      exact List.prefix_refl _

def History.consume_lower (history : History initial config current monitor) (position : Nat)
    (loss : Loss initial config) (chosen : history.book.lower = some position)
    (found : history.book.losses[position]? = some loss) (head : Head initial current .lower)
    (move : Move current actual) (event : actual.event = .timeout sender true)
    (dropIDs : (M.observe config monitor actual).drops = monitor.drops)
    (retries : (M.observe config monitor actual).retries = monitor.retries + 1) :
    History initial config move.after (M.observe config monitor actual) :=
  consume history .lower position loss chosen found head move event dropIDs retries

def History.consume_upper (history : History initial config current monitor) (position : Nat)
    (loss : Loss initial config) (chosen : history.book.upper = some position)
    (found : history.book.losses[position]? = some loss) (head : Head initial current .upper)
    (move : Move current actual) (event : actual.event = .timeout sender true)
    (dropIDs : (M.observe config monitor actual).drops = monitor.drops)
    (retries : (M.observe config monitor actual).retries = monitor.retries + 1) :
    History initial config move.after (M.observe config monitor actual) :=
  consume history .upper position loss chosen found head move event dropIDs retries

theorem History.consume_lower_book (history : History initial config current monitor) (position : Nat)
    (loss : Loss initial config) (chosen : history.book.lower = some position)
    (found : history.book.losses[position]? = some loss) (head : Head initial current .lower)
    (move : Move current actual) (event : actual.event = .timeout sender true)
    (dropIDs : (M.observe config monitor actual).drops = monitor.drops)
    (retries : (M.observe config monitor actual).retries = monitor.retries + 1) :
    (history.consume_lower position loss chosen found head move event dropIDs retries).book =
      { history.book with lower := none, spent := history.book.spent ++
        [history.spentEntry .lower position loss chosen found head move event] } := rfl

theorem History.consume_upper_book (history : History initial config current monitor) (position : Nat)
    (loss : Loss initial config) (chosen : history.book.upper = some position)
    (found : history.book.losses[position]? = some loss) (head : Head initial current .upper)
    (move : Move current actual) (event : actual.event = .timeout sender true)
    (dropIDs : (M.observe config monitor actual).drops = monitor.drops)
    (retries : (M.observe config monitor actual).retries = monitor.retries + 1) :
    (history.consume_upper position loss chosen found head move event dropIDs retries).book =
      { history.book with upper := none, spent := history.book.spent ++
        [history.spentEntry .upper position loss chosen found head move event] } := rfl

private theorem clock_filters (extra : List (Step input))
    (clocks : ∀ actual ∈ extra, ∃ actor millis, actual.event = .advanceClock actor millis) :
    extra.filter isDrop = [] ∧ extra.filter (isTimeout sender) = [] := by
  induction extra with
  | nil => exact ⟨rfl, rfl⟩
  | cons actual rest ih =>
    obtain ⟨actor, millis, event⟩ := clocks actual List.mem_cons_self
    have tail := ih (fun selected member => clocks selected (List.mem_cons_of_mem _ member))
    simpa only [List.filter_cons, isDrop, isTimeout, event, Bool.false_eq_true, ite_false] using tail

def History.clock (history : History initial config current monitor)
    (placement : CampusTCPRecoveryRoundPhaseBase.At current next)
    (observed : (next.report.steps.drop current.report.steps.length).foldl (M.observe config) monitor = monitor) :
    History initial config next monitor := by
  let extra := next.report.steps.drop current.report.steps.length
  have appended : next.report.steps = current.report.steps ++ extra := by
    obtain ⟨rest, appended, _⟩ := placement.clocks
    dsimp only [extra]
    rw [appended, List.drop_append_length]
  have clocks : ∀ actual ∈ extra, ∃ actor millis, actual.event = .advanceClock actor millis := by
    obtain ⟨rest, appended, clocks⟩ := placement.clocks
    simpa only [extra, appended, List.drop_append_length] using clocks
  have filters := clock_filters (sender := sender) extra clocks
  have folded : extra.foldl (M.observe config) monitor = monitor := by
    simpa only [appended, List.drop_append_length] using observed
  refine ⟨history.suffix ++ extra, ?_, ?_, history.book, history.valid, ?_, ?_, history.dropIDs, history.retries, ?_, ?_⟩
  · rw [appended, history.steps, List.append_assoc]
  · rw [List.foldl_append, history.observed, folded]
  · rw [List.filter_append, filters.1, List.append_nil]
    exact history.dropSteps
  · rw [List.filter_append, filters.2, List.append_nil]
    exact history.timeoutSteps
  · exact fun loss member => (history.lossesPast loss member).trans placement.retained
  · exact fun entry member => (history.timeoutsPast entry member).trans placement.retained

end Netlib.Check.CampusTCPTwoProgressLossHistory
