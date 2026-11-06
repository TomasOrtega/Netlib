import Netlib.Check.CampusTCPGapProgressMonitor
import Netlib.Check.CampusTCPRoundMonitorFacts
import Netlib.Check.CampusTCPRoundServiceBound
import Netlib.Check.CampusTCPTimedClock

/-!
# Monitor laws for actual held-gap steps

Demand laws select current actions and packet identities.
Observation laws read the stored results of the same actual step.
-/

namespace Netlib.Check.CampusTCPGapProgressMonitorFacts

open CampusTCPModel

namespace M
export CampusTCPGapProgressMonitor
  (Config Monitor Demand serves observe nextDemand nextAction packetAt allowed Allowed clockAllowed freeClock advance)
end M
namespace R
export CampusTCPRoundMonitor (Action actionOf)
end R

variable {input : Input} {id : Nat}

private theorem actor_beq (left right : Actor) : (left == right) = true ↔ left = right := by
  cases left <;> cases right <;> decide

private theorem actor_beq_self (actor : Actor) : (actor == actor) = true := by
  cases actor <;> rfl

theorem actionOf_iff (event : Event) (action : R.Action) : R.actionOf event = some action ↔ event = action.event := by
  constructor
  · exact CampusTCPRoundServiceBound.action_event event action
  · intro same
    rw [same]
    exact CampusTCPRoundMonitor.Action.actionOf_event action

theorem serves_operation (action : R.Action) (event : Event) :
    M.serves (.operation action) event = true ↔ event = action.event := by
  simp only [M.serves, decide_eq_true_eq, actionOf_iff]

private theorem drop_match (event : Event) (packet : Nat) :
    (match event with | .dropPacket id => id == packet | _ => false) = true ↔ event = .dropPacket packet := by
  cases event <;> simp

theorem serves_resolution (action : R.Action) (packet : Nat) (event : Event) :
    M.serves (.resolution action packet) event = true ↔ event = action.event ∨ event = .dropPacket packet := by
  simp only [M.serves, Bool.or_eq_true, decide_eq_true_eq, actionOf_iff]
  exact or_congr Iff.rfl (drop_match event packet)

theorem serves_tick (actor : Actor) (target : Nat) (event : Event) :
    M.serves (.tick actor target) event = true ↔ event = .advanceClock actor target := by
  cases event <;> simp only [M.serves, Bool.false_eq_true, reduceCtorEq]
  rename_i selected millis
  simp only [Bool.and_eq_true, actor_beq, beq_iff_eq]
  constructor
  · rintro ⟨rfl, rfl⟩
    rfl
  · intro same
    cases same
    exact ⟨rfl, rfl⟩

theorem serves_timeout (actor : Actor) (event : Event) :
    M.serves (.timeout actor) event = true ↔ event = .timeout actor true := by
  cases event <;> simp only [M.serves, Bool.false_eq_true, reduceCtorEq]
  rename_i selected policy
  cases actor <;> cases selected <;> cases policy <;> simp [BEq.beq] <;> rfl

theorem allowed_iff (config : M.Config) (before : State input) (monitor : M.Monitor) (event : Event) :
    M.Allowed config before monitor event ↔
      ((∃ demand, M.nextDemand config before monitor = some demand ∧ M.serves demand event = true) ∨
        M.freeClock config before monitor event = true) ∧
      (match event with | .advanceClock .. => M.clockAllowed config before event | _ => true) = true := by
  unfold M.Allowed M.allowed
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
  simp only [M.freeClock, Bool.and_eq_true] at guarded
  have clock : M.clockAllowed config before event = true := guarded.1
  cases event
  all_goals first
    | exact ⟨_, _, rfl, clock⟩
    | cases connection : before.connection <;>
        simp only [M.clockAllowed, CampusTCPRecoveryRoundMonitor.clockAllowed, connection, Bool.false_eq_true] at clock

theorem freeClock_action (config : M.Config) (before : State input) (monitor : M.Monitor) (action : R.Action) :
    M.freeClock config before monitor action.event = false := by
  cases connection : before.connection <;> cases action <;>
    simp only [M.freeClock, M.clockAllowed, CampusTCPRecoveryRoundMonitor.clockAllowed,
      CampusTCPRoundMonitor.Action.event, connection, Bool.false_and]

theorem nextDemand_action (config : M.Config) (before : State input) (monitor : M.Monitor)
    (waiting : monitor.waiting = false) (action : R.Action)
    (next : M.nextAction config before monitor = some action) :
    M.nextDemand config before monitor = some (match M.packetAt monitor with
      | some packet => if monitor.drops.length < config.lossAllowance then .resolution action packet else .operation action
      | none => .operation action) := by
  simp only [M.nextDemand, waiting, Bool.false_eq_true, ite_false, next, bind, Option.bind]
  cases M.packetAt monitor <;> simp only
  · rfl
  · split <;> rfl

theorem nextDemand_operation (config : M.Config) (before : State input) (monitor : M.Monitor)
    (waiting : monitor.waiting = false) (action : R.Action)
    (next : M.nextAction config before monitor = some action) (packet : M.packetAt monitor = none) :
    M.nextDemand config before monitor = some (.operation action) := by
  rw [nextDemand_action config before monitor waiting action next, packet]

theorem nextDemand_resolution (config : M.Config) (before : State input) (monitor : M.Monitor)
    (waiting : monitor.waiting = false) (action : R.Action)
    (next : M.nextAction config before monitor = some action) (packet : M.packetAt monitor = some id)
    (credit : monitor.drops.length < config.lossAllowance) :
    M.nextDemand config before monitor = some (.resolution action id) := by
  simpa only [packet, credit, ite_true] using nextDemand_action config before monitor waiting action next

theorem nextDemand_exhausted (config : M.Config) (before : State input) (monitor : M.Monitor)
    (waiting : monitor.waiting = false) (action : R.Action)
    (next : M.nextAction config before monitor = some action) (packet : M.packetAt monitor = some id)
    (credit : config.lossAllowance ≤ monitor.drops.length) : M.nextDemand config before monitor = some (.operation action) := by
  simpa only [packet, Nat.not_lt.mpr credit, ite_false] using nextDemand_action config before monitor waiting action next

theorem nextDemand_action_exists (config : M.Config) (before : State input) (monitor : M.Monitor)
    (waiting : monitor.waiting = false) (demand : M.Demand) (selected : M.nextDemand config before monitor = some demand) :
    ∃ action, M.nextAction config before monitor = some action ∧
      (demand = .operation action ∨ ∃ packet, demand = .resolution action packet) := by
  unfold M.nextDemand at selected
  simp only [waiting, Bool.false_eq_true, ite_false] at selected
  cases next : M.nextAction config before monitor with
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
  simp only [M.observe, supported, passed, Bool.and_self, ite_true, event]

theorem observe_action (config : M.Config) (monitor : M.Monitor) (actual : Step input)
    (waiting : monitor.waiting = false) (supported : actual.result.supported = true)
    (passed : actual.result.passed = true) (action : R.Action)
    (next : M.nextAction config actual.before monitor = some action) (event : actual.event = action.event) :
    M.observe config monitor actual = M.advance config monitor actual := by
  unfold M.observe
  rw [supported, passed]
  simp only [Bool.and_self, ite_true, event]
  cases action <;> simp only [CampusTCPRoundMonitor.Action.event, waiting, Bool.false_eq_true, ite_false,
    next, R.actionOf, ite_true]

theorem observe_drop (config : M.Config) (monitor : M.Monitor) (actual : Step input)
    (supported : actual.result.supported = true) (passed : actual.result.passed = true)
    (action : R.Action) (next : M.nextDemand config actual.before monitor = some (.resolution action id))
    (event : actual.event = .dropPacket id) :
    M.observe config monitor actual = { monitor with waiting := true, drops := monitor.drops ++ [id] } := by
  simp only [M.observe, supported, passed, Bool.and_self, ite_true, event, next, beq_self_eq_true, ite_true]

theorem observe_timeout (config : M.Config) (monitor : M.Monitor) (actual : Step input)
    (supported : actual.result.supported = true) (passed : actual.result.passed = true)
    (waiting : monitor.waiting = true) (event : actual.event = .timeout config.sender true) :
    M.observe config monitor actual = { CampusTCPGapProgressMonitor.observeOutput config monitor actual true .dataIngress with
      waiting := false, retries := monitor.retries + 1 } := by
  simp only [M.observe, supported, passed, Bool.and_self, ite_true, event, waiting, actor_beq_self]

private theorem nextAction_snapshot (config : M.Config) (state : State input) (monitor : M.Monitor) :
    M.nextAction config (CampusTCPRoundStutter.snapshot state) monitor = M.nextAction config state monitor := by
  cases monitor.phase <;> rfl

theorem Frame.nextAction (frame : CampusTCPTimedClock.Frame before endpoints after updated)
    (config : M.Config) (monitor : M.Monitor) : M.nextAction config after monitor = M.nextAction config before monitor := by
  have same := congrArg (fun state => M.nextAction config state monitor) frame.fixed
  simpa only [nextAction_snapshot] using same.symm

end Netlib.Check.CampusTCPGapProgressMonitorFacts
