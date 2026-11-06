import Netlib.Check.CampusTCPTwoProgressMonitor
import Netlib.Check.CampusTCPGapProgressMonitorFacts

/-!
# Observation laws for two TCP records

These laws inspect stored steps and current lane references.
They do not establish that a selected endpoint operation succeeds.
-/

namespace Netlib.Check.CampusTCPTwoProgressMonitorFacts

open CampusTCPModel CampusTCPEnabled
open CampusTCPTwoProgressMonitor
local notation "Config" => CampusTCPTwoProgressMonitor.Config
namespace G
export CampusTCPGapProgressMonitor
  (Monitor Demand serves observeOutput observeAssignment observeService observeReceipt)
end G
namespace R
export CampusTCPRoundMonitor (Action Phase)
end R

variable {input : Input} {id : Nat} {actor : Actor} {millis : Nat}

theorem phase_beq (left right : R.Phase) : (left == right) = decide (left = right) := by
  cases left <;> cases right <;> rfl

theorem mode_beq (left right : Mode) : (left == right) = decide (left = right) := by
  cases left <;> cases right <;> rfl

theorem phase_beq_false (left right : R.Phase) : (left == right) = false ↔ left ≠ right := by
  rw [phase_beq, decide_eq_false_iff_not]

theorem phase_beq_self (phase : R.Phase) : (phase == phase) = true := by cases phase <;> rfl

theorem serves_single (demand : G.Demand) (event : Event) :
    serves (.single demand) event = true ↔ G.serves demand event = true := Iff.rfl

theorem serves_originalChoice (lower upper : Option G.Demand) (event : Event) :
    serves (.originalChoice lower upper) event = true ↔
      servesOption lower event = true ∨ servesOption upper event = true := by
  simp only [serves, Bool.or_eq_true]

theorem servesOption_iff (selected : Option G.Demand) (event : Event) :
    servesOption selected event = true ↔ ∃ demand, selected = some demand ∧ G.serves demand event = true := by
  cases selected <;> simp [servesOption]

theorem originalChoice_branch (lower upper : Option G.Demand) (event : Event)
    (served : serves (.originalChoice lower upper) event = true) :
    (∃ demand, lower = some demand ∧ G.serves demand event = true) ∨
      (∃ demand, upper = some demand ∧ G.serves demand event = true) := by
  exact (serves_originalChoice lower upper event).mp served |>.imp
    (servesOption_iff lower event).mp (servesOption_iff upper event).mp

theorem serves_operation (action : R.Action) (event : Event) :
    serves (.single (.operation action)) event = true ↔ event = action.event :=
  CampusTCPGapProgressMonitorFacts.serves_operation action event

theorem serves_resolution (action : R.Action) (id : Nat) (event : Event) :
    serves (.single (.resolution action id)) event = true ↔ event = action.event ∨ event = .dropPacket id :=
  CampusTCPGapProgressMonitorFacts.serves_resolution action id event

theorem serves_tick (actor : Actor) (millis : Nat) (event : Event) :
    serves (.single (.tick actor millis)) event = true ↔ event = .advanceClock actor millis :=
  CampusTCPGapProgressMonitorFacts.serves_tick actor millis event

theorem serves_timeout (actor : Actor) (event : Event) :
    serves (.single (.timeout actor)) event = true ↔ event = .timeout actor true :=
  CampusTCPGapProgressMonitorFacts.serves_timeout actor event

theorem laneDemand_action (config : Config) (state : State input) (monitor : Monitor) (lane : Lane)
    (selected : laneDemand config state monitor lane = some demand) :
    ∃ action, CampusTCPGapProgressMonitor.nextAction config.toConfig state lane.toGap = some action ∧
      (demand = .operation action ∨ ∃ id, demand = .resolution action id) := by
  unfold laneDemand at selected
  cases next : CampusTCPGapProgressMonitor.nextAction config.toConfig state lane.toGap with
  | none => simp only [next, bind, Option.bind] at selected; cases selected
  | some action =>
    refine ⟨action, rfl, ?_⟩
    simp only [next, bind, Option.bind] at selected
    cases packet : CampusTCPGapProgressMonitor.packetAt lane.toGap with
    | none =>
      simp only [packet] at selected
      exact Or.inl (Option.some.inj selected).symm
    | some id =>
      simp only [packet] at selected
      split at selected
      · exact Or.inr ⟨id, (Option.some.inj selected).symm⟩
      · exact Or.inl (Option.some.inj selected).symm

theorem dropTarget_packet (config : Config) (state : State input) (monitor : Monitor) (id : Nat)
    (found : dropTarget config state monitor id = some target) :
    match target with
    | .lower => exposedPacket config state monitor.lower = some id
    | .upper => exposedPacket config state monitor.upper = some id
    | .retry => exposedPacket config state monitor.retry = some id
    | .ack => ∃ lane, monitor.ack = some lane ∧ exposedPacket config state lane = some id := by
  unfold dropTarget at found
  split at found
  · split at found
    · split at found
      · rename_i selected
        cases (Option.some.inj found).symm
        exact beq_iff_eq.mp selected
      · split at found
        · rename_i selected
          cases (Option.some.inj found).symm
          exact beq_iff_eq.mp selected
        · split at found
          · rename_i selected
            cases (Option.some.inj found).symm
            exact beq_iff_eq.mp selected
          · cases ack : monitor.ack with
            | none => simp only [ack] at found; cases found
            | some lane =>
              simp only [ack] at found
              split at found
              · rename_i selected
                cases (Option.some.inj found).symm
                exact ⟨lane, rfl, beq_iff_eq.mp selected⟩
              · cases found
    · cases found
  · cases found

theorem allowed_iff (config : Config) (state : State input) (monitor : Monitor) (event : Event) :
    Allowed config state monitor event ↔ monitor.mode ≠ .invalid ∧
      ((∃ demand, nextDemand config state monitor = some demand ∧ serves demand event = true) ∨
        (∃ id target, event = .dropPacket id ∧ dropTarget config state monitor id = some target) ∨
        freeClock config state monitor event = true) ∧
      (match event with | .advanceClock .. => clockAllowed config state event | _ => true) = true := by
  unfold Allowed allowed
  cases mode : monitor.mode <;> cases next : nextDemand config state monitor <;>
    cases event <;> simp_all [mode_beq, Bool.and_eq_true, Bool.or_eq_true, Option.isSome_iff_exists, or_assoc]

theorem freeClock_event (config : Config) (state : State input) (monitor : Monitor) (event : Event)
    (free : freeClock config state monitor event = true) :
    ∃ actor millis, event = .advanceClock actor millis ∧ clockAllowed config state event = true := by
  exact CampusTCPGapProgressMonitorFacts.freeClock_event config.toConfig state
    { waiting := monitor.waiting } event free

theorem observe_clock (config : Config) (monitor : Monitor) (actual : Step input)
    (supported : actual.result.supported = true) (passed : actual.result.passed = true)
    (allowed : Allowed config actual.before monitor actual.event)
    (event : actual.event = .advanceClock actor millis) : CampusTCPTwoProgressMonitor.observe config monitor actual = monitor := by
  unfold CampusTCPTwoProgressMonitor.observe
  rw [supported, passed]
  simp only [Bool.true_and]
  rw [show CampusTCPTwoProgressMonitor.allowed config actual.before monitor actual.event = true from allowed]
  simp only [ite_true, event]

theorem observe_drop (config : Config) (monitor : Monitor) (actual : Step input)
    (supported : actual.result.supported = true) (passed : actual.result.passed = true)
    (allowed : Allowed config actual.before monitor actual.event) (event : actual.event = .dropPacket id) :
    CampusTCPTwoProgressMonitor.observe config monitor actual = observeDrop config monitor actual id := by
  unfold CampusTCPTwoProgressMonitor.observe
  rw [supported, passed]
  simp only [Bool.true_and]
  rw [show CampusTCPTwoProgressMonitor.allowed config actual.before monitor actual.event = true from allowed]
  simp only [ite_true, event]

theorem observe_timeout (config : Config) (monitor : Monitor) (actual : Step input)
    (supported : actual.result.supported = true) (passed : actual.result.passed = true)
    (allowed : Allowed config actual.before monitor actual.event) (event : actual.event = .timeout actor true) :
    CampusTCPTwoProgressMonitor.observe config monitor actual = observeTimeout config monitor actual := by
  unfold CampusTCPTwoProgressMonitor.observe
  rw [supported, passed]
  simp only [Bool.true_and]
  rw [show CampusTCPTwoProgressMonitor.allowed config actual.before monitor actual.event = true from allowed]
  simp only [ite_true, event]

theorem observe_action (config : Config) (monitor : Monitor) (actual : Step input)
    (supported : actual.result.supported = true) (passed : actual.result.passed = true)
    (allowed : Allowed config actual.before monitor actual.event) (action : R.Action)
    (event : actual.event = action.event) : CampusTCPTwoProgressMonitor.observe config monitor actual = observeOrdinary config monitor actual := by
  unfold CampusTCPTwoProgressMonitor.observe
  rw [supported, passed]
  simp only [Bool.true_and]
  rw [show CampusTCPTwoProgressMonitor.allowed config actual.before monitor actual.event = true from allowed]
  cases action <;> simp only [ite_true, event, CampusTCPRoundMonitor.Action.event]

theorem observe_send_lower (config : Config) (monitor : Monitor) (actual : Step input)
    (mode : monitor.mode = .originals) (pending : monitor.lower.phase = .needSend) :
    observeOrdinary config monitor actual = observeSend config monitor actual .lower := by
  simp only [observeOrdinary, mode, pending, phase_beq_self, ite_true]

theorem observe_send_upper (config : Config) (monitor : Monitor) (actual : Step input)
    (mode : monitor.mode = .originals) (first : monitor.lower.phase ≠ .needSend)
    (pending : monitor.upper.phase = .needSend) :
    observeOrdinary config monitor actual = observeSend config monitor actual .upper := by
  simp only [observeOrdinary, mode, (phase_beq_false _ _).mpr first, Bool.false_eq_true, ite_false,
    pending, phase_beq_self, ite_true]

theorem observe_ack (config : Config) (monitor : Monitor) (actual : Step input) (lane : Lane)
    (mode : monitor.mode = .originals ∨ monitor.mode = .recovery)
    (first : monitor.lower.phase ≠ .needSend) (second : monitor.upper.phase ≠ .needSend)
    (ack : monitor.ack = some lane) :
    observeOrdinary config monitor actual = observeAck config monitor actual lane := by
  rcases mode with mode | mode <;>
    simp only [observeOrdinary, mode, (phase_beq_false _ _).mpr first, (phase_beq_false _ _).mpr second,
      Bool.false_eq_true, ite_false, ack]

theorem observe_original_lower (config : Config) (monitor : Monitor) (actual : Step input)
    (mode : monitor.mode = .originals) (first : monitor.lower.phase ≠ .needSend)
    (second : monitor.upper.phase ≠ .needSend) (ack : monitor.ack = none)
    (served : servesOption (laneDemand config actual.before monitor monitor.lower) actual.event = true) :
    observeOrdinary config monitor actual = observeData config monitor actual .lower := by
  simp only [observeOrdinary, mode, (phase_beq_false _ _).mpr first, (phase_beq_false _ _).mpr second,
    Bool.false_eq_true, ite_false, ack, served, ite_true]

theorem observe_original_upper (config : Config) (monitor : Monitor) (actual : Step input)
    (mode : monitor.mode = .originals) (first : monitor.lower.phase ≠ .needSend)
    (second : monitor.upper.phase ≠ .needSend) (ack : monitor.ack = none)
    (lower : servesOption (laneDemand config actual.before monitor monitor.lower) actual.event = false)
    (upper : servesOption (laneDemand config actual.before monitor monitor.upper) actual.event = true) :
    observeOrdinary config monitor actual = observeData config monitor actual .upper := by
  simp only [observeOrdinary, mode, (phase_beq_false _ _).mpr first, (phase_beq_false _ _).mpr second,
    Bool.false_eq_true, ite_false, ack, lower, upper, ite_true]

theorem output_phase (config : CampusTCPGapProgressMonitor.Config) (monitor : G.Monitor)
    (actual : Step input) (data : Bool) (next : R.Phase) :
    (G.observeOutput config monitor actual data next).phase = next ∨
      (G.observeOutput config monitor actual data next).phase = .invalid := by
  cases data <;> cases output : actual.result.output with
  | none => simp only [G.observeOutput, output]; exact Or.inr rfl
  | some produced =>
    simp [G.observeOutput, output]
    try dsimp only
    split
    · split
      · exact Or.inr rfl
      · exact Or.inl rfl
    · exact Or.inr rfl

theorem assignment_phase (monitor : G.Monitor) (actual : Step input) (data : Bool) (next : R.Phase) :
    (G.observeAssignment monitor actual data next).phase = next ∨
      (G.observeAssignment monitor actual data next).phase = .invalid := by
  cases data <;> unfold G.observeAssignment
  all_goals
    try dsimp only
    split
    · exact Or.inr rfl
    · exact Or.inl rfl

theorem service_phase (monitor : G.Monitor) (actual : Step input) (data : Bool) (next : R.Phase) :
    (G.observeService monitor actual data next).phase = next ∨
      (G.observeService monitor actual data next).phase = .invalid := by
  cases data <;> unfold G.observeService
  all_goals
    try dsimp only
    split
    · exact Or.inr rfl
    · split
      · exact Or.inr rfl
      · try dsimp only
        split
        · exact Or.inr rfl
        · exact Or.inl rfl

theorem receipt_phase (config : CampusTCPGapProgressMonitor.Config) (monitor : G.Monitor)
    (actual : Step input) (data : Bool) (next : R.Phase) :
    (G.observeReceipt config monitor actual data next).phase = next ∨
      (G.observeReceipt config monitor actual data next).phase = .invalid := by
  cases data <;> cases receipt : actual.result.receipt with
  | none => simp only [G.observeReceipt, receipt]; exact Or.inr rfl
  | some received =>
    cases application : actual.result.application with
    | none => simp only [G.observeReceipt, receipt, application]; exact Or.inr rfl
    | some pair =>
      rcases pair with ⟨actor, operation⟩
      simp [G.observeReceipt, receipt, application]
      split
      · exact Or.inl rfl
      · exact Or.inr rfl

def counters (monitor : Monitor) : Nat × List Nat := (monitor.retries, monitor.drops)

theorem normalize_frame (config : Config) (state : State input) (monitor : Monitor) :
    { normalize config state monitor with mode := monitor.mode, waiting := monitor.waiting } = monitor := by
  generalize computed : normalize config state monitor = result
  unfold normalize at computed
  repeat' (first | split at computed | (dsimp (config := { zetaHave := true }) only at computed; split at computed))
  all_goals cases computed; rfl

theorem normalize_counters (config : Config) (state : State input) (monitor : Monitor) :
    counters (normalize config state monitor) = counters monitor := by
  have frame := congrArg counters (normalize_frame config state monitor)
  simpa (config := { zetaHave := true }) only [counters] using frame

theorem normalize_lanes (config : Config) (state : State input) (monitor : Monitor) :
    (normalize config state monitor).lower = monitor.lower ∧
      (normalize config state monitor).upper = monitor.upper ∧
      (normalize config state monitor).retry = monitor.retry ∧
      (normalize config state monitor).ack = monitor.ack := by
  have frame := normalize_frame config state monitor
  have lower := congrArg Monitor.lower frame
  have upper := congrArg Monitor.upper frame
  have retry := congrArg Monitor.retry frame
  have ack := congrArg Monitor.ack frame
  simpa (config := { zetaHave := true }) only using And.intro lower (And.intro upper (And.intro retry ack))

theorem recordData_counters (monitor : Monitor) (lane : Lane) (actual : Step input) :
    counters (recordData monitor lane actual) = counters monitor := by
  cases receipt : lane.refs.dataReceipt <;> cases application : actual.result.application with
  | none => simp only [recordData, receipt, application]; rfl
  | some pair =>
    cases pair
    simp only [recordData, receipt, application]
    rfl

theorem data_counters (config : Config) (monitor : Monitor) (actual : Step input) (target : DropTarget) :
    counters (observeData config monitor actual target) = counters monitor := by
  cases target <;> unfold observeData
  all_goals
    try dsimp only
    split
    · rfl
    · split
      · exact recordData_counters _ _ _
      · rfl

theorem ack_counters (config : Config) (monitor : Monitor) (actual : Step input) (lane : Lane) :
    counters (observeAck config monitor actual lane) = counters monitor := by
  unfold observeAck
  dsimp only
  split
  · rfl
  · split
    · split
      · rfl
      · exact normalize_counters _ _ _
    · rfl

theorem send_counters (config : Config) (monitor : Monitor) (actual : Step input) (target : Original) :
    counters (observeSend config monitor actual target) = counters monitor := by
  cases target <;> unfold observeSend
  all_goals dsimp only; split <;> rfl

theorem read_counters (config : Config) (monitor : Monitor) (actual : Step input) :
    counters (observeRead config monitor actual) = counters monitor := by
  cases application : actual.result.application with
  | none => simp only [observeRead, application]; rfl
  | some pair =>
    cases pair
    simp only [observeRead, application]
    split <;> rfl

theorem ordinary_counters (config : Config) (monitor : Monitor) (actual : Step input) :
    counters (observeOrdinary config monitor actual) = counters monitor := by
  cases mode : monitor.mode <;> simp only [observeOrdinary, mode]
  case originals =>
    split
    · exact send_counters _ _ _ _
    · split
      · exact send_counters _ _ _ _
      · split
        · exact ack_counters _ _ _ _
        · split
          · exact data_counters _ _ _ _
          · split
            · exact data_counters _ _ _ _
            · rfl
  case recovery =>
    split
    · exact ack_counters _ _ _ _
    · split
      · rfl
      · exact data_counters _ _ _ _
  case needRead => exact read_counters _ _ _
  all_goals rfl

theorem drop_counters (config : Config) (monitor : Monitor) (actual : Step input) (id : Nat)
    (target : dropTarget config actual.before monitor id = some selected) :
    counters (observeDrop config monitor actual id) = (monitor.retries, monitor.drops ++ [id]) := by
  rw [observeDrop, target]
  cases selected <;> exact normalize_counters _ _ _

theorem timeout_counters (config : Config) (monitor : Monitor) (actual : Step input)
    (decoded : (G.observeOutput config.toConfig monitor.retry.toGap actual true .dataIngress).phase ≠ .invalid) :
    counters (observeTimeout config monitor actual) = (monitor.retries + 1, monitor.drops) := by
  simp only [observeTimeout, Lane.ofGap, (phase_beq_false _ _).mpr decoded, Bool.false_eq_true, ite_false, counters]

theorem timeout_counters_cases (config : Config) (monitor : Monitor) (actual : Step input) :
    counters (observeTimeout config monitor actual) = counters monitor ∨
      counters (observeTimeout config monitor actual) = (monitor.retries + 1, monitor.drops) := by
  unfold observeTimeout
  dsimp only
  split
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem serves_copy_false (demand : Demand) (id : Nat) : serves demand (.copyPacket id) = false := by
  have old : ∀ value, G.serves value (.copyPacket id) = false := by intro value; cases value <;> rfl
  cases demand with
  | single demand => exact old demand
  | originalChoice lower upper => cases lower <;> cases upper <;> simp [serves, servesOption, old]

theorem serves_write_false (demand : Demand) (actor : Actor) (bytes : List UInt8) :
    serves demand (.write actor bytes) = false := by
  have old : ∀ value, G.serves value (.write actor bytes) = false := by intro value; cases value <;> rfl
  cases demand with
  | single demand => exact old demand
  | originalChoice lower upper => cases lower <;> cases upper <;> simp [serves, servesOption, old]

theorem Allowed.copy_false (config : Config) (state : State input) (monitor : Monitor) (id : Nat) :
    ¬Allowed config state monitor (.copyPacket id) := by
  unfold Allowed allowed
  cases monitor.mode <;> cases nextDemand config state monitor <;> cases state.connection <;>
    simp [serves_copy_false, freeClock, CampusTCPGapProgressMonitor.freeClock]

theorem Allowed.write_false (config : Config) (state : State input) (monitor : Monitor) (actor : Actor) (bytes : List UInt8) :
    ¬Allowed config state monitor (.write actor bytes) := by
  unfold Allowed allowed
  cases monitor.mode <;> cases nextDemand config state monitor <;> cases state.connection <;>
    simp [serves_write_false, freeClock, CampusTCPGapProgressMonitor.freeClock]

theorem Allowed.done_read_false (config : Config) (state : State input) (monitor : Monitor)
    (done : monitor.mode = .done) (actor : Actor) (count : Nat) :
    ¬Allowed config state monitor (.read actor count) := by
  unfold Allowed allowed
  cases state.connection <;>
    simp [nextDemand, done, mode_beq, freeClock, CampusTCPGapProgressMonitor.freeClock]

theorem Allowed.read_exact (config : Config) (state : State input) (monitor : Monitor)
    (ready : monitor.mode = .needRead) (allowed : Allowed config state monitor (.read actor count)) :
    actor = config.sender.other ∧ count = config.bytes.length := by
  obtain ⟨_, selected | dropped | free, _⟩ := (allowed_iff config state monitor (.read actor count)).mp allowed
  · obtain ⟨demand, pending, served⟩ := selected
    simp only [nextDemand, ready, Option.some.injEq] at pending
    subst demand
    exact Event.read.inj ((serves_operation _ _).mp served)
  · obtain ⟨id, target, event, _⟩ := dropped
    cases event
  · obtain ⟨actor, millis, event, _⟩ := freeClock_event config state monitor _ free
    cases event

end Netlib.Check.CampusTCPTwoProgressMonitorFacts
