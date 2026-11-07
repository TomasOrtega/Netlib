import Netlib.Check.CampusTCPTwoTransferCurrentReverseConfig
import Netlib.Check.CampusTCPTwoProgressEvidenceBasic
import Netlib.Check.CampusTCPTwoProgressEvidenceStep

/-!
# Actual reverse evidence at the current standby

The reverse task starts at the same stored write.
Its local evidence derives current routing through reverse and done clocks.
-/

namespace Netlib.Check.CampusTCPTwoTransferCurrentReverseAt

open Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPRoundPhaseBase (Move)
open CampusTCPTwoProgressStart
open CampusTCPTwoTransferNative (Checks Routing)
open CampusTCPTwoTransferEvidence (Evidence ReadAdvanced)
open CampusTCPTwoTransferPostRead (After)
open CampusTCPTwoTransferCurrentReverseGeometry (Started)
open CampusTCPTwoTransferLocatedCore (config)

namespace W
export CampusTCPTwoTransferMonitor (Monitor Allowed observe)
end W
namespace X
export CampusTCPTwoExchangeMonitor (Mode Monitor allowed observe)
end X
namespace L
export CampusTCPTwoProgressMonitor (Config Monitor Allowed observe)
export CampusTCPTwoProgressEvidence (Evidence)
end L

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut readBefore writeBefore current : Cut input complete} {sender : Actor} {gateway location : Gateway}
variable {lower upper : List UInt8} {initial : TwoWriteInitial cut sender gateway lower upper}
variable {checks : Checks cut initial.gatewayState.session.entry} {routing : Routing cut gateway}
variable {quantum allowance : Nat} {reverseLower reverseUpper : List UInt8}
variable {readMonitor writeMonitor : W.Monitor} {readActual written : Step input}
variable {evidence : Evidence initial checks routing quantum allowance reverseLower reverseUpper readBefore readMonitor location}
variable {forward : ReadAdvanced evidence readActual} {post : After forward writeBefore writeMonitor}

local notation "cfg" => config initial checks routing quantum allowance reverseLower reverseUpper

def reverseConfig (start : Started post written) : L.Config :=
  CampusTCPTwoProgressSetup.config start.reverseInitial start.reverseNative quantum
    (allowance - writeMonitor.exchange.forward.drops.length)

theorem forward_budget (post : After forward writeBefore writeMonitor) : writeMonitor.exchange.forward.drops.length ≤ allowance := by
  have same := congrArg (fun monitor : L.Monitor => monitor.drops.length) post.forward_eq
  rw [same]
  exact forward.value.lossBound

structure Current (start : Started post written) (current : Cut input complete) (monitor : W.Monitor) where
  reverse : L.Evidence start.reverseInitial start.reverseNative quantum
    (allowance - writeMonitor.exchange.forward.drops.length) current monitor.exchange.reverse
  finished : monitor.mode = .finished
  forward : monitor.exchange.forward = writeMonitor.exchange.forward
  phase : (monitor.exchange.mode = .reverse ∧ monitor.exchange.reverse.mode ≠ .done) ∨
    (monitor.exchange.mode = .done ∧ monitor.exchange.reverse.mode = .done)
  recorded : CampusTCPTwoTransferRecorded.Recorded cut cfg current monitor
  controls : monitor.controls = writeMonitor.controls
  forwardReadSlot : monitor.exchange.forwardReadSlot = writeMonitor.exchange.forwardReadSlot
  writeSlot : monitor.exchange.writeSlot = some writeMonitor.exchange.slots

variable {start : Started post written} {monitor : W.Monitor} {actual : Step input}


def Current.ofStart (start : Started post written) :
    Current start start.boundary.write.move.after (W.observe cfg writeMonitor written) := by
  have initialEvidence : L.Evidence start.reverseInitial start.reverseNative quantum
      (allowance - writeMonitor.exchange.forward.drops.length) start.boundary.write.move.after .initial :=
    CampusTCPTwoProgressEvidence.Evidence.ofInitial start.reverseInitial start.reverseNative quantum _
  refine {
    reverse := ?_
    finished := ?_
    forward := ?_
    phase := ?_
    recorded := start.boundary.recorded
    controls := ?_
    forwardReadSlot := ?_
    writeSlot := ?_ }
  · rw [start.boundary.observed]
    exact initialEvidence
  · rw [start.boundary.observed]
    exact post.finished
  · rw [start.boundary.observed]
    rfl
  · rw [start.boundary.observed]
    exact .inl ⟨rfl, by change CampusTCPTwoProgressMonitor.Mode.originals ≠ .done; decide⟩
  · rw [start.boundary.observed]
    rfl
  · rw [start.boundary.observed]
    rfl
  · rw [start.boundary.observed]
    rfl

variable (value : Current start current monitor)

def Current.native : NativeEnv current .standby start.reverseInitial.gatewayState.session.entry :=
  CampusTCPTwoProgressReframe.native_env start.reverseNative value.reverse.anchor.environment

theorem Current.currentRouting (value : Current start current monitor) : Routing current .standby :=
  Routing.ofNative value.native

theorem Current.config (value : Current start current monitor) :
    reverseConfig start = ((cfg).at current.report.final).reverse monitor.exchange.forward.drops.length := by
  rw [value.forward]
  exact CampusTCPTwoTransferCurrentReverseConfig.config_at start value.currentRouting _

theorem Current.forward_budget (value : Current start current monitor) : monitor.exchange.forward.drops.length ≤ allowance := by
  rw [value.forward]
  exact CampusTCPTwoTransferCurrentReverseAt.forward_budget post

theorem Current.remaining_budget (budget : allowance ≤ 2) : allowance - writeMonitor.exchange.forward.drops.length ≤ 2 :=
  Nat.le_trans (Nat.sub_le _ _) budget

private theorem local_mode_beq (left right : CampusTCPTwoProgressMonitor.Mode) :
    (left == right) = decide (left = right) := by cases left <;> cases right <;> rfl

private theorem no_drain (state : State input) (monitor : W.Monitor) (finished : monitor.mode = .finished) :
    CampusTCPTwoTransferMonitor.drainTicket state monitor = none :=
  CampusTCPTwoTransferControlObserve.noDrain_of_non_capture state monitor (by rw [finished]; decide)

private theorem no_control (monitor : W.Monitor) (finished : monitor.mode = .finished) :
    CampusTCPTwoTransferMonitor.controlDemand monitor = none := by
  rw [CampusTCPTwoTransferMonitor.controlDemand, finished]

private theorem inner_allowed (value : Current start current monitor)
    (allowed : W.Allowed cfg current.report.final monitor actual.event) :
    CampusTCPTwoExchangeMonitor.Allowed ((cfg).at current.report.final) current.report.final monitor.exchange actual.event := by
  simpa only [W.Allowed, CampusTCPTwoTransferMonitor.allowed, value.finished, reduceCtorEq,
    decide_false, Bool.false_eq_true, ite_false, no_drain _ _ value.finished, no_control _ value.finished,
    CampusTCPTwoExchangeMonitor.Allowed] using allowed

theorem Current.local_allowed (value : Current start current monitor)
    (allowed : W.Allowed cfg current.report.final monitor actual.event) :
    L.Allowed (reverseConfig start) current.report.final monitor.exchange.reverse actual.event := by
  have inner := inner_allowed value allowed
  rcases value.phase with ⟨mode, _⟩ | ⟨mode, _⟩
  · simpa only [CampusTCPTwoExchangeMonitor.Allowed, CampusTCPTwoExchangeMonitor.allowed, mode,
      ← value.config, L.Allowed] using inner
  · cases event : actual.event with
    | advanceClock actor millis =>
      simpa only [CampusTCPTwoExchangeMonitor.Allowed, CampusTCPTwoExchangeMonitor.allowed, mode,
        event, ← value.config, L.Allowed] using inner
    | _ => simp only [CampusTCPTwoExchangeMonitor.Allowed, CampusTCPTwoExchangeMonitor.allowed,
        mode, event, Bool.false_eq_true] at inner

private theorem done_clock (value : Current start current monitor) (mode : monitor.exchange.mode = .done)
    (allowed : W.Allowed cfg current.report.final monitor actual.event) :
    ∃ actor millis, actual.event = .advanceClock actor millis := by
  have inner := inner_allowed value allowed
  cases event : actual.event with
  | advanceClock actor millis => exact ⟨actor, millis, rfl⟩
  | _ => simp only [CampusTCPTwoExchangeMonitor.Allowed, CampusTCPTwoExchangeMonitor.allowed,
      mode, event, Bool.false_eq_true] at inner

def afterStep (monitor : W.Monitor) (actual : Step input) (localMonitor : L.Monitor) : W.Monitor :=
  { monitor with exchange := { monitor.exchange with
    mode := if localMonitor.mode == .done then .done else .reverse
    reverse := localMonitor
    drops := match actual.event with | .dropPacket id => monitor.exchange.drops ++ [id] | _ => monitor.exchange.drops
    timeouts := match actual.event with | .timeout _ true => monitor.exchange.timeouts + 1 | _ => monitor.exchange.timeouts
    slots := monitor.exchange.slots + 1
    reverseReadSlot := if monitor.exchange.mode == .reverse && localMonitor.mode == .done then
      some monitor.exchange.slots else monitor.exchange.reverseReadSlot } }

private theorem observe_step (value : Current start current monitor) (move : Move current actual)
    (allowed : W.Allowed cfg current.report.final monitor actual.event)
    (healthy : (L.observe (reverseConfig start) monitor.exchange.reverse actual).mode ≠ .invalid) :
    W.observe cfg monitor actual = afterStep monitor actual (L.observe (reverseConfig start) monitor.exchange.reverse actual) := by
  have inner := inner_allowed value allowed
  have checked : (actual.result.supported && actual.result.passed &&
      CampusTCPTwoTransferMonitor.allowed cfg actual.before monitor actual.event) = true := by
    rw [move.supported, move.passed, move.beforeEq]
    exact allowed
  have innerChecked : (actual.result.supported && actual.result.passed &&
      X.allowed ((cfg).at actual.before) actual.before monitor.exchange actual.event) = true := by
    rw [move.supported, move.passed, move.beforeEq]
    exact inner
  have placedConfig : reverseConfig start = ((cfg).at actual.before).reverse monitor.exchange.forward.drops.length := by
    rw [move.beforeEq]
    exact value.config
  rw [W.observe, ite_eq_left checked, move.beforeEq, no_drain _ _ value.finished, no_control _ value.finished]
  unfold CampusTCPTwoTransferMonitor.ordinary
  rw [X.observe, ite_eq_left innerChecked]
  rcases value.phase with ⟨mode, _⟩ | ⟨mode, done⟩
  · rw [mode, ← placedConfig]
    cases next : (L.observe (reverseConfig start) monitor.exchange.reverse actual).mode <;>
      simp only [next, local_mode_beq, reduceCtorEq, decide_false, decide_true, Bool.false_eq_true,
        ite_true, ite_false] at healthy ⊢
    all_goals first
      | exact False.elim (healthy rfl)
      | (
        first
        | (change (if decide (monitor.exchange.mode = .invalid) then _ else _) = _
           rw [mode]
           simp only [reduceCtorEq, decide_false, Bool.false_eq_true, ite_false])
        | skip
        unfold afterStep
        rw [next, mode]
        simp only [local_mode_beq, reduceCtorEq, decide_false, decide_true, Bool.false_eq_true,
          Bool.and_false, ite_true, ite_false]
        congr 2 <;> exact mode)
  · obtain ⟨actor, millis, event⟩ := done_clock value mode allowed
    have localAllowed := value.local_allowed allowed
    have fixed : L.observe (reverseConfig start) monitor.exchange.reverse actual = monitor.exchange.reverse :=
      CampusTCPTwoProgressMonitorFacts.observe_clock _ _ actual move.supported move.passed
        (by rw [move.beforeEq]; exact localAllowed) event
    rw [mode]
    change (if decide (monitor.exchange.mode = .invalid) then _ else _) = _
    rw [mode]
    simp only [reduceCtorEq, decide_false, Bool.false_eq_true, ite_false]
    unfold afterStep
    rw [fixed, done, mode]
    simp only [local_mode_beq, decide_true, ite_true]
    congr 2
    change { monitor.exchange with
      slots := monitor.exchange.slots + 1
      drops := match actual.event with | .dropPacket id => monitor.exchange.drops ++ [id] | _ => monitor.exchange.drops
      timeouts := match actual.event with | .timeout _ true => monitor.exchange.timeouts + 1 | _ => monitor.exchange.timeouts } =
      { monitor.exchange with
        mode := .done
        slots := monitor.exchange.slots + 1
        drops := match actual.event with | .dropPacket id => monitor.exchange.drops ++ [id] | _ => monitor.exchange.drops
        timeouts := match actual.event with | .timeout _ true => monitor.exchange.timeouts + 1 | _ => monitor.exchange.timeouts }
    exact congrArg (fun selectedMode : X.Mode => { monitor.exchange with
      mode := selectedMode
      slots := monitor.exchange.slots + 1
      drops := match actual.event with | .dropPacket id => monitor.exchange.drops ++ [id] | _ => monitor.exchange.drops
      timeouts := match actual.event with | .timeout _ true => monitor.exchange.timeouts + 1 | _ => monitor.exchange.timeouts }) mode

structure Advanced (value : Current start current monitor) (actual : Step input) where
  move : Move current actual
  next : Current start move.after (W.observe cfg monitor actual)
  observed : W.observe cfg monitor actual = afterStep monitor actual (L.observe (reverseConfig start) monitor.exchange.reverse actual)


theorem step (value : Current start current monitor) (budget : allowance ≤ 2)
    (actual : Step input) (before : actual.before = current.report.final)
    (allowed : W.Allowed cfg current.report.final monitor actual.event) : Nonempty (Advanced value actual) := by
  have localAllowed := value.local_allowed allowed
  obtain ⟨move, ⟨next⟩⟩ := value.reverse.step (Nat.le_trans (Nat.sub_le _ _) budget) actual before localAllowed
  have observed := observe_step value move allowed next.healthy
  have reverseEq : (W.observe cfg monitor actual).exchange.reverse = L.observe (reverseConfig start) monitor.exchange.reverse actual := by
    rw [observed]
    rfl
  let nextValue : Current start move.after (W.observe cfg monitor actual) := {
    reverse := reverseEq.symm ▸ next
    finished := by rw [observed]; exact value.finished
    forward := by rw [observed]; exact value.forward
    phase := by
      rw [observed]
      change ((if (L.observe (reverseConfig start) monitor.exchange.reverse actual).mode == .done then (.done : X.Mode) else .reverse) = .reverse ∧
          (L.observe (reverseConfig start) monitor.exchange.reverse actual).mode ≠ .done) ∨
        ((if (L.observe (reverseConfig start) monitor.exchange.reverse actual).mode == .done then (.done : X.Mode) else .reverse) = .done ∧
          (L.observe (reverseConfig start) monitor.exchange.reverse actual).mode = .done)
      cases mode : (L.observe (reverseConfig start) monitor.exchange.reverse actual).mode <;>
        simp only [local_mode_beq, reduceCtorEq, decide_false, decide_true, Bool.false_eq_true,
          ite_true, ite_false, false_and, false_or, true_and]
      all_goals decide
    recorded := value.recorded.snoc move allowed
    controls := by rw [observed]; exact value.controls
    forwardReadSlot := by rw [observed]; exact value.forwardReadSlot
    writeSlot := by rw [observed]; exact value.writeSlot }
  exact ⟨⟨move, nextValue, observed⟩⟩

theorem Advanced.reverse_observed (advance : Advanced value actual) :
    (W.observe cfg monitor actual).exchange.reverse = L.observe (reverseConfig start) monitor.exchange.reverse actual := by
  rw [advance.observed]
  rfl

end Netlib.Check.CampusTCPTwoTransferCurrentReverseAt
