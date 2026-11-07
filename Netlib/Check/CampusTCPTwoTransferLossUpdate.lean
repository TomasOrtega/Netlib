import Netlib.Check.CampusTCPTwoTransferLossHistory

/-!
# Actual drop and timeout updates through transfer

Each timeout spends one earlier stored loss for its actual current head.
-/

namespace Netlib.Check.CampusTCPTwoTransferLossHistory

open Protocol Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPRoundPhaseBase (Move)
open CampusTCPTwoProgressStart CampusTCPTwoTransferLoss
open CampusTCPTwoProgressLossHistory (Head isDrop dropID)
open CampusTCPTwoExchangeLoss (isTimeoutOutput)

local notation "Config" => CampusTCPTwoTransferMonitor.Config

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current next : Cut input complete} {sender : Actor} {gateway : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper} {config : Config}
variable {monitor : W.Monitor} {actual : Step input} {id : Nat} {target : CampusTCPTwoProgressMonitor.DropTarget}
variable {book : Book initial config} {position : Nat} {loss : Loss initial config} {role : S.Part}

structure DropFrame (config : Config) (monitor : W.Monitor) (actual : Step input) (id : Nat) : Prop where
  dropIDs : (W.observe config monitor actual).exchange.forward.drops = monitor.exchange.forward.drops ++ [id]
  retries : (W.observe config monitor actual).exchange.forward.retries = monitor.exchange.forward.retries
  wholeDropIDs : (W.observe config monitor actual).exchange.drops = monitor.exchange.drops ++ [id]
  wholeTimeouts : (W.observe config monitor actual).exchange.timeouts = monitor.exchange.timeouts

structure TimeoutFrame (config : Config) (monitor : W.Monitor) (actual : Step input) : Prop where
  dropIDs : (W.observe config monitor actual).exchange.forward.drops = monitor.exchange.forward.drops
  retries : (W.observe config monitor actual).exchange.forward.retries = monitor.exchange.forward.retries + 1
  wholeDropIDs : (W.observe config monitor actual).exchange.drops = monitor.exchange.drops
  wholeTimeouts : (W.observe config monitor actual).exchange.timeouts = monitor.exchange.timeouts + 1

def History.drop (history : History initial config current monitor) (move : Move current actual)
    (facts : CampusTCPRecoveryRoundDrop.Facts current.report.final id actual)
    (phase : monitor.exchange.mode = .forward)
    (selected : CampusTCPTwoProgressMonitor.dropTarget (config.at current.report.final).forward
      current.report.final monitor.exchange.forward id = some target)
    (allowed : CampusTCPTwoTransferMonitor.Allowed config current.report.final monitor actual.event)
    (frame : DropFrame config monitor actual id) : History initial config move.after (W.observe config monitor actual) := by
  let loss := history.selectedLoss move facts phase selected allowed
  refine ⟨history.suffix ++ [actual], ?_, ?_, history.book.appendLoss loss, history.valid.appendLoss loss,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [move.history, history.steps, List.append_assoc]
  · rw [List.foldl_append, history.observed]
    rfl
  · simp only [List.filter_append, List.filter_cons, isDrop, facts.event, List.filter_nil, ite_true,
      history.dropSteps, Book.appendLoss, List.map_append, List.map_cons, List.map_nil]
    rfl
  · simp only [List.filter_append, List.filter_cons, isTimeoutOutput, facts.event, List.filter_nil,
      Bool.false_eq_true, ite_false, List.append_nil, Book.appendLoss]
    exact history.timeoutSteps
  · rw [frame.dropIDs, history.dropIDs]
    simp only [Book.appendLoss, List.map_append, List.map_cons, List.map_nil]
    rfl
  · exact history.retries.trans frame.retries.symm
  · rw [frame.wholeDropIDs, history.wholeDropIDs]
    simp only [Book.appendLoss, List.map_append, List.map_cons, List.map_nil]
    rfl
  · exact frame.wholeTimeouts.trans history.wholeTimeouts
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
    ((book.appendLoss loss).rememberCause role book.losses.length).Valid := by
  apply Book.Valid.rememberCause (valid.appendLoss loss) List.getElem?_concat_length support
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
    (valid : (history.book.rememberCause role position).Valid) : History initial config current monitor := by
  cases role <;> exact { history with book := history.book.rememberCause _ position, valid := valid }

def History.drop_lower (history : History initial config current monitor) (move : Move current actual)
    (facts : CampusTCPRecoveryRoundDrop.Facts current.report.final id actual) (phase : monitor.exchange.mode = .forward)
    (selected : CampusTCPTwoProgressMonitor.dropTarget (config.at current.report.final).forward
      current.report.final monitor.exchange.forward id = some target)
    (allowed : CampusTCPTwoTransferMonitor.Allowed config current.report.final monitor actual.event)
    (frame : DropFrame config monitor actual id)
    (support : Supports (history.selectedLoss move facts phase selected allowed) .lower) :
    History initial config move.after (W.observe config monitor actual) :=
  rememberHistory (history.drop move facts phase selected allowed frame) .lower history.book.losses.length
    (fresh_valid history.valid _ support)

def History.drop_upper (history : History initial config current monitor) (move : Move current actual)
    (facts : CampusTCPRecoveryRoundDrop.Facts current.report.final id actual) (phase : monitor.exchange.mode = .forward)
    (selected : CampusTCPTwoProgressMonitor.dropTarget (config.at current.report.final).forward
      current.report.final monitor.exchange.forward id = some target)
    (allowed : CampusTCPTwoTransferMonitor.Allowed config current.report.final monitor actual.event)
    (frame : DropFrame config monitor actual id)
    (support : Supports (history.selectedLoss move facts phase selected allowed) .upper) :
    History initial config move.after (W.observe config monitor actual) :=
  rememberHistory (history.drop move facts phase selected allowed frame) .upper history.book.losses.length
    (fresh_valid history.valid _ support)

theorem History.drop_lower_cause (history : History initial config current monitor) (move : Move current actual)
    (facts : CampusTCPRecoveryRoundDrop.Facts current.report.final id actual) (phase : monitor.exchange.mode = .forward)
    (selected : CampusTCPTwoProgressMonitor.dropTarget (config.at current.report.final).forward
      current.report.final monitor.exchange.forward id = some target)
    (allowed : CampusTCPTwoTransferMonitor.Allowed config current.report.final monitor actual.event)
    (frame : DropFrame config monitor actual id)
    (support : Supports (history.selectedLoss move facts phase selected allowed) .lower) :
    (history.drop_lower move facts phase selected allowed frame support).book.lower = some history.book.losses.length := rfl

theorem History.drop_lower_upper (history : History initial config current monitor) (move : Move current actual)
    (facts : CampusTCPRecoveryRoundDrop.Facts current.report.final id actual) (phase : monitor.exchange.mode = .forward)
    (selected : CampusTCPTwoProgressMonitor.dropTarget (config.at current.report.final).forward
      current.report.final monitor.exchange.forward id = some target)
    (allowed : CampusTCPTwoTransferMonitor.Allowed config current.report.final monitor actual.event)
    (frame : DropFrame config monitor actual id)
    (support : Supports (history.selectedLoss move facts phase selected allowed) .lower) :
    (history.drop_lower move facts phase selected allowed frame support).book.upper = history.book.upper := rfl

theorem History.drop_upper_cause (history : History initial config current monitor) (move : Move current actual)
    (facts : CampusTCPRecoveryRoundDrop.Facts current.report.final id actual) (phase : monitor.exchange.mode = .forward)
    (selected : CampusTCPTwoProgressMonitor.dropTarget (config.at current.report.final).forward
      current.report.final monitor.exchange.forward id = some target)
    (allowed : CampusTCPTwoTransferMonitor.Allowed config current.report.final monitor actual.event)
    (frame : DropFrame config monitor actual id)
    (support : Supports (history.selectedLoss move facts phase selected allowed) .upper) :
    (history.drop_upper move facts phase selected allowed frame support).book.upper = some history.book.losses.length := rfl

theorem History.cause_origin (history : History initial config current monitor) (chosen : history.book.cause role = some position) :
    ∃ loss, history.book.losses[position]? = some loss ∧ Supports loss role ∧ position ∉ history.book.positions ∧
      loss.move.after.report.steps <+: current.report.steps := by
  obtain ⟨loss, stored, support, unused⟩ := history.valid.cause position chosen
  exact ⟨loss, stored, support, unused, history.lossesPast loss (List.mem_of_getElem? stored)⟩

theorem History.whole_credit (history : History initial config current monitor) (chosen : history.book.cause role = some position) :
    monitor.exchange.timeouts < monitor.exchange.drops.length := by
  rw [history.wholeTimeouts, history.wholeDropIDs, List.length_map]
  exact history.valid.cause_credit chosen

private theorem cause_support (valid : book.Valid) (chosen : book.cause role = some position)
    (found : book.losses[position]? = some loss) : Supports loss role := by
  obtain ⟨prior, stored, support, _⟩ := valid.cause position chosen
  have same : prior = loss := Option.some.inj (stored.symm.trans found)
  exact same ▸ support

def History.spentEntry (history : History initial config current monitor) (role : S.Part) (position : Nat)
    (loss : Loss initial config) (chosen : history.book.cause role = some position)
    (found : history.book.losses[position]? = some loss) (head : Head initial current role)
    (move : Move current actual) (event : actual.event = .timeout sender true) (phase : monitor.exchange.mode = .forward)
    (allowed : CampusTCPTwoTransferMonitor.Allowed config current.report.final monitor actual.event) : Spent initial config where
  position := position
  loss := loss
  role := role
  support := cause_support history.valid chosen found
  before := current
  monitor := monitor
  observed := by rw [history.steps, List.drop_append_length]; exact history.observed
  phase := phase
  head := head
  earlier := history.lossesPast loss (List.mem_of_getElem? found)
  actual := actual
  move := move
  event := event
  allowed := allowed

def History.consume (history : History initial config current monitor) (role : S.Part) (position : Nat)
    (loss : Loss initial config) (chosen : history.book.cause role = some position)
    (found : history.book.losses[position]? = some loss) (head : Head initial current role)
    (move : Move current actual) (event : actual.event = .timeout sender true) (phase : monitor.exchange.mode = .forward)
    (allowed : CampusTCPTwoTransferMonitor.Allowed config current.report.final monitor actual.event)
    (frame : TimeoutFrame config monitor actual) : History initial config move.after (W.observe config monitor actual) := by
  let entry := history.spentEntry role position loss chosen found head move event phase allowed
  have entries : (history.book.spendCause entry).spent = history.book.spent ++ [entry] := Book.spendCause_spent _ _
  have losses : (history.book.spendCause entry).losses = history.book.losses := Book.spendCause_losses _ _
  refine ⟨history.suffix ++ [actual], ?_, ?_, history.book.spendCause entry,
    history.valid.spendCause entry chosen found, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [move.history, history.steps, List.append_assoc]
  · rw [List.foldl_append, history.observed]
    rfl
  · rw [losses]
    simpa only [List.filter_append, List.filter_cons, isDrop, event, Bool.false_eq_true, ite_false,
      List.filter_nil, List.append_nil] using history.dropSteps
  · rw [entries]
    simp only [List.filter_append, List.filter_cons, isTimeoutOutput, event, ite_true,
      List.filter_nil, List.map_append, List.map_cons, List.map_nil, history.timeoutSteps]
    rfl
  · rw [losses]
    exact frame.dropIDs.trans history.dropIDs
  · rw [entries, List.length_append, List.length_cons, List.length_nil, Nat.zero_add, history.retries, frame.retries]
  · rw [losses]
    exact frame.wholeDropIDs.trans history.wholeDropIDs
  · rw [entries, frame.wholeTimeouts, history.wholeTimeouts, List.length_append, List.length_cons, List.length_nil, Nat.zero_add]
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
    (move : Move current actual) (event : actual.event = .timeout sender true) (phase : monitor.exchange.mode = .forward)
    (allowed : CampusTCPTwoTransferMonitor.Allowed config current.report.final monitor actual.event)
    (frame : TimeoutFrame config monitor actual) : History initial config move.after (W.observe config monitor actual) :=
  history.consume .lower position loss chosen found head move event phase allowed frame

def History.consume_upper (history : History initial config current monitor) (position : Nat)
    (loss : Loss initial config) (chosen : history.book.upper = some position)
    (found : history.book.losses[position]? = some loss) (head : Head initial current .upper)
    (move : Move current actual) (event : actual.event = .timeout sender true) (phase : monitor.exchange.mode = .forward)
    (allowed : CampusTCPTwoTransferMonitor.Allowed config current.report.final monitor actual.event)
    (frame : TimeoutFrame config monitor actual) : History initial config move.after (W.observe config monitor actual) :=
  history.consume .upper position loss chosen found head move event phase allowed frame

theorem History.consume_lower_book (history : History initial config current monitor) (position : Nat)
    (loss : Loss initial config) (chosen : history.book.lower = some position)
    (found : history.book.losses[position]? = some loss) (head : Head initial current .lower)
    (move : Move current actual) (event : actual.event = .timeout sender true) (phase : monitor.exchange.mode = .forward)
    (allowed : CampusTCPTwoTransferMonitor.Allowed config current.report.final monitor actual.event)
    (frame : TimeoutFrame config monitor actual) :
    (history.consume_lower position loss chosen found head move event phase allowed frame).book =
      { history.book with lower := none, spent := history.book.spent ++
        [history.spentEntry .lower position loss chosen found head move event phase allowed] } := rfl

theorem History.consume_upper_book (history : History initial config current monitor) (position : Nat)
    (loss : Loss initial config) (chosen : history.book.upper = some position)
    (found : history.book.losses[position]? = some loss) (head : Head initial current .upper)
    (move : Move current actual) (event : actual.event = .timeout sender true) (phase : monitor.exchange.mode = .forward)
    (allowed : CampusTCPTwoTransferMonitor.Allowed config current.report.final monitor actual.event)
    (frame : TimeoutFrame config monitor actual) :
    (history.consume_upper position loss chosen found head move event phase allowed frame).book =
      { history.book with upper := none, spent := history.book.spent ++
        [history.spentEntry .upper position loss chosen found head move event phase allowed] } := rfl

end Netlib.Check.CampusTCPTwoTransferLossHistory
