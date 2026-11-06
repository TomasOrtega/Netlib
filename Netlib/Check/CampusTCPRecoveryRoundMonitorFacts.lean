import Netlib.Check.CampusTCPRecoveryRoundMonitor
import Netlib.Check.CampusTCPRoundMonitorFacts
import Netlib.Check.CampusTCPRoundServiceBound

namespace Netlib.Check.CampusTCPRecoveryRoundMonitorFacts

open CampusTCPModel

namespace M
export CampusTCPRecoveryRoundMonitor
  (Config Monitor Demand serves observe observeOrdinary nextDemand packetAt allowed Allowed clockAllowed freeClock)
end M
namespace R
export CampusTCPRoundMonitor (Action actionOf nextAction advance)
end R

variable {input : Input} {id : Nat}

theorem actionOf_iff (event : Event) (action : R.Action) : R.actionOf event = some action ↔ event = action.event := by
  constructor
  · exact CampusTCPRoundServiceBound.action_event event action
  · intro same
    rw [same]
    exact CampusTCPRoundMonitor.Action.actionOf_event action

theorem serves_operation (action : R.Action) (event : Event) :
    M.serves (.operation action) event = true ↔ event = action.event := by
  simp only [CampusTCPRecoveryRoundMonitor.serves, decide_eq_true_eq, actionOf_iff]

private theorem drop_match (event : Event) (packet : Nat) :
    (match event with | .dropPacket id => id == packet | _ => false) = true ↔ event = .dropPacket packet := by
  cases event <;> simp

theorem serves_resolution (action : R.Action) (packet : Nat) (event : Event) :
    M.serves (.resolution action packet) event = true ↔ event = action.event ∨ event = .dropPacket packet := by
  simp only [CampusTCPRecoveryRoundMonitor.serves, Bool.or_eq_true, decide_eq_true_eq, actionOf_iff]
  exact or_congr Iff.rfl (drop_match event packet)

theorem serves_tick (target : Nat) (event : Event) :
    M.serves (.tick target) event = true ↔ event = .advanceClock .client target := by
  cases event <;> simp only [CampusTCPRecoveryRoundMonitor.serves, Bool.false_eq_true, reduceCtorEq]
  rename_i actor millis
  cases actor <;> simp

theorem serves_timeout (event : Event) :
    M.serves .timeout event = true ↔ event = .timeout .client true := by
  cases event <;> simp only [CampusTCPRecoveryRoundMonitor.serves, Bool.false_eq_true, reduceCtorEq]
  rename_i actor policy
  cases actor <;> cases policy <;> simp

theorem allowed_iff (config : M.Config) (before : State input) (monitor : M.Monitor) (event : Event) :
    M.Allowed config before monitor event ↔
      ((∃ demand, M.nextDemand config before monitor = some demand ∧ M.serves demand event = true) ∨
        M.freeClock config before monitor event = true) ∧
      (match event with | .advanceClock .. => M.clockAllowed config before event | _ => true) = true := by
  unfold CampusTCPRecoveryRoundMonitor.Allowed CampusTCPRecoveryRoundMonitor.allowed
  cases M.nextDemand config before monitor <;> simp [Bool.and_eq_true, Bool.or_eq_true] <;> intro _ <;> rfl

theorem allowed_at (config : M.Config) (before : State input) (monitor : M.Monitor) (event : Event)
    (demand : M.Demand) (selected : M.nextDemand config before monitor = some demand) :
    M.Allowed config before monitor event ↔
      (M.serves demand event = true ∨ M.freeClock config before monitor event = true) ∧
      (match event with | .advanceClock .. => M.clockAllowed config before event | _ => true) = true := by
  rw [allowed_iff]
  simp [selected]

theorem freeClock_event (config : M.Config) (before : State input) (monitor : M.Monitor) (event : Event)
    (free : M.freeClock config before monitor event = true) :
    ∃ actor millis, event = .advanceClock actor millis ∧ M.clockAllowed config before event = true := by
  have guarded := free
  simp only [CampusTCPRecoveryRoundMonitor.freeClock, Bool.and_eq_true] at guarded
  have clock : M.clockAllowed config before event = true := guarded.1
  cases event
  all_goals first
    | exact ⟨_, _, rfl, clock⟩
    | cases connection : before.connection <;>
        simp only [CampusTCPRecoveryRoundMonitor.clockAllowed, connection, Bool.false_eq_true] at clock

theorem freeClock_action (config : M.Config) (before : State input) (monitor : M.Monitor) (action : R.Action) :
    M.freeClock config before monitor action.event = false := by
  cases connection : before.connection <;> cases action <;>
    simp only [CampusTCPRecoveryRoundMonitor.freeClock, CampusTCPRecoveryRoundMonitor.clockAllowed,
      CampusTCPRoundMonitor.Action.event, connection, Bool.false_and]

theorem nextDemand_action (config : M.Config) (before : State input) (monitor : M.Monitor)
    (waiting : monitor.waiting = false) (action : R.Action)
    (next : R.nextAction config.toConfig before monitor.round = some action) :
    M.nextDemand config before monitor = some (match M.packetAt monitor with
      | some packet => if monitor.drops.length < 2 then .resolution action packet else .operation action
      | none => .operation action) := by
  simp only [CampusTCPRecoveryRoundMonitor.nextDemand, waiting, Bool.false_eq_true, ite_false, next,
    bind, Option.bind]
  cases M.packetAt monitor <;> simp only
  · rfl
  · split <;> rfl

theorem nextDemand_operation (config : M.Config) (before : State input) (monitor : M.Monitor)
    (waiting : monitor.waiting = false) (action : R.Action)
    (next : R.nextAction config.toConfig before monitor.round = some action) (packet : M.packetAt monitor = none) :
    M.nextDemand config before monitor = some (.operation action) := by
  rw [nextDemand_action config before monitor waiting action next, packet]

theorem nextDemand_resolution (config : M.Config) (before : State input) (monitor : M.Monitor)
    (waiting : monitor.waiting = false) (action : R.Action)
    (next : R.nextAction config.toConfig before monitor.round = some action) (packet : M.packetAt monitor = some id)
    (credit : monitor.drops.length < 2) : M.nextDemand config before monitor = some (.resolution action id) := by
  simpa only [packet, credit, ite_true] using nextDemand_action config before monitor waiting action next

theorem nextDemand_exhausted (config : M.Config) (before : State input) (monitor : M.Monitor)
    (waiting : monitor.waiting = false) (action : R.Action)
    (next : R.nextAction config.toConfig before monitor.round = some action) (packet : M.packetAt monitor = some id)
    (credit : 2 ≤ monitor.drops.length) : M.nextDemand config before monitor = some (.operation action) := by
  simpa only [packet, Nat.not_lt.mpr credit, ite_false] using nextDemand_action config before monitor waiting action next

theorem nextDemand_action_exists (config : M.Config) (before : State input) (monitor : M.Monitor)
    (waiting : monitor.waiting = false) (demand : M.Demand) (selected : M.nextDemand config before monitor = some demand) :
    ∃ action, R.nextAction config.toConfig before monitor.round = some action ∧
      (demand = .operation action ∨ ∃ packet, demand = .resolution action packet) := by
  unfold CampusTCPRecoveryRoundMonitor.nextDemand at selected
  simp only [waiting, Bool.false_eq_true, ite_false] at selected
  cases next : R.nextAction config.toConfig before monitor.round with
  | none => simp only [next, bind, Option.bind] at selected; cases selected
  | some action =>
    refine ⟨action, rfl, ?_⟩
    simp only [next, bind, Option.bind] at selected
    cases packet : M.packetAt monitor with
    | none => simp only [packet, pure, Option.some.injEq] at selected; exact .inl selected.symm
    | some id =>
      simp only [packet] at selected
      split at selected
      · exact .inr ⟨id, (Option.some.inj selected).symm⟩
      · exact .inl (Option.some.inj selected).symm

theorem observe_clock (config : M.Config) (monitor : M.Monitor) (actual : Step input)
    (supported : actual.result.supported = true) (passed : actual.result.passed = true)
    (actor : Actor) (millis : Nat) (event : actual.event = .advanceClock actor millis) :
    M.observe config monitor actual = monitor := by
  simp only [CampusTCPRecoveryRoundMonitor.observe, supported, passed, Bool.and_self, ite_true, event]

theorem observe_ordinary (config : M.Config) (monitor : M.Monitor) (actual : Step input)
    (waiting : monitor.waiting = false) (supported : actual.result.supported = true)
    (passed : actual.result.passed = true) (action : R.Action) (event : actual.event = action.event) :
    M.observe config monitor actual = M.observeOrdinary config monitor actual := by
  unfold CampusTCPRecoveryRoundMonitor.observe
  rw [supported, passed]
  simp only [Bool.and_self, ite_true, event]
  cases action <;> simp only [CampusTCPRoundMonitor.Action.event, waiting, Bool.false_eq_true, ite_false]

theorem observe_action (config : M.Config) (monitor : M.Monitor) (actual : Step input)
    (waiting : monitor.waiting = false) (supported : actual.result.supported = true)
    (passed : actual.result.passed = true) (action : R.Action)
    (next : R.nextAction config.toConfig actual.before monitor.round = some action) (event : actual.event = action.event) :
    M.observe config monitor actual = { monitor with
      round := R.advance config.toConfig monitor.round actual
      firstDataReceipt := match monitor.firstDataReceipt with
        | some index => some index
        | none => if monitor.round.phase == .dataLink then (R.advance config.toConfig monitor.round actual).refs.dataReceipt else none } := by
  rw [observe_ordinary config monitor actual waiting supported passed action event]
  simp only [CampusTCPRecoveryRoundMonitor.observeOrdinary]
  rw [CampusTCPRoundMonitorFacts.observe_action config.toConfig monitor.round actual action supported passed next event]
  rfl

theorem observeOrdinary_fields (config : M.Config) (monitor : M.Monitor) (actual : Step input) :
    (M.observeOrdinary config monitor actual).round = CampusTCPRoundMonitor.observe config.toConfig monitor.round actual ∧
      (M.observeOrdinary config monitor actual).waiting = monitor.waiting ∧
      (M.observeOrdinary config monitor actual).drops = monitor.drops ∧
      (M.observeOrdinary config monitor actual).retries = monitor.retries ∧
      (M.observeOrdinary config monitor actual).firstDataReceipt = match monitor.firstDataReceipt with
        | some index => some index
        | none => if monitor.round.phase == .dataLink then
            (CampusTCPRoundMonitor.observe config.toConfig monitor.round actual).refs.dataReceipt else none := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

end Netlib.Check.CampusTCPRecoveryRoundMonitorFacts
