import Netlib.Check.CampusTCPTwoProgressPhaseNetwork

/-!
# Healthy observation of the actual network moves

Current dispatch selects a lane.
The stored assignment or service supplies its next phase.
-/

namespace Netlib.Check.CampusTCPTwoProgressPhaseObserve

open Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart CampusTCPTwoProgressPhaseBase
open CampusTCPTwoProgressSetup (config)

namespace M
export CampusTCPTwoProgressMonitor
  (Monitor Lane laneDemand servesOption dataLane ackLane observe observeOrdinary observeData observeAck)
end M
namespace G
export CampusTCPGapProgressMonitor (nextAction packetAt serves)
end G
namespace F
export CampusTCPTwoProgressMonitorFacts (phase_beq_false observe_original_lower observe_original_upper observe_ack)
end F
namespace P
export CampusTCPTwoProgressPaths (DataIngress DataTicket AckIngress AckTicket)
end P
namespace N
export CampusTCPTwoProgressPhaseNetwork (DataAssigned DataServed AckAssigned AckServed)
end N
namespace S
export CampusTCPTwoProgressSender (Stage Part)
end S
namespace R
export CampusTCPTwoProgressReceiver (Stage)
end R
local notation "Config" => CampusTCPTwoProgressMonitor.Config

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current : Cut input complete} {sender : Actor} {gateway : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {native : NativeEnv cut gateway initial.gatewayState.session.entry} {quantum allowance : Nat}
variable {monitor : M.Monitor} {sent : S.Stage initial} {received : R.Stage} {part : S.Part}
variable {lane afterLane : M.Lane} {actual : Step input} {count : Nat}
variable {core : Core initial native quantum allowance current monitor sent received}

theorem laneDemand_serves (cfg : Config) (state : State input) (monitor : M.Monitor) (lane : M.Lane)
    (action : CampusTCPRoundMonitor.Action)
    (next : G.nextAction cfg.toConfig state lane.toGap = some action) :
    M.servesOption (M.laneDemand cfg state monitor lane) action.event = true := by
  cases packet : G.packetAt lane.toGap with
  | none => simp [M.laneDemand, next, packet, M.servesOption, G.serves, CampusTCPRoundMonitor.Action.actionOf_event]
  | some id =>
    by_cases budget : monitor.drops.length < cfg.lossAllowance
    all_goals simp [M.laneDemand, next, packet, budget, M.servesOption, G.serves, CampusTCPRoundMonitor.Action.actionOf_event]

private theorem data_lower_frame (cfg : Config) (monitor : M.Monitor) (actual : Step input)
    (decoded : M.dataLane cfg monitor.lower actual = afterLane)
    (valid : afterLane.phase ≠ .invalid) (active : afterLane.phase ≠ .done) :
    M.observeData cfg monitor actual .lower = { monitor with lower := afterLane, lastOriginal := some .lower } := by
  simp only [M.observeData, decoded, (F.phase_beq_false _ _).mpr valid, Bool.false_eq_true, ite_false,
    (F.phase_beq_false _ _).mpr active]

private theorem data_upper_frame (cfg : Config) (monitor : M.Monitor) (actual : Step input)
    (decoded : M.dataLane cfg monitor.upper actual = afterLane)
    (valid : afterLane.phase ≠ .invalid) (active : afterLane.phase ≠ .done) :
    M.observeData cfg monitor actual .upper = { monitor with upper := afterLane, lastOriginal := some .upper } := by
  simp only [M.observeData, decoded, (F.phase_beq_false _ _).mpr valid, Bool.false_eq_true, ite_false,
    (F.phase_beq_false _ _).mpr active]

private theorem data_retry_frame (cfg : Config) (monitor : M.Monitor) (actual : Step input)
    (decoded : M.dataLane cfg monitor.retry actual = afterLane)
    (valid : afterLane.phase ≠ .invalid) (active : afterLane.phase ≠ .done) :
    M.observeData cfg monitor actual .retry = { monitor with retry := afterLane } := by
  simp only [M.observeData, decoded, (F.phase_beq_false _ _).mpr valid, Bool.false_eq_true, ite_false,
    (F.phase_beq_false _ _).mpr active]

private theorem ack_frame (cfg : Config) (monitor : M.Monitor) (actual : Step input)
    (decoded : M.ackLane cfg lane actual = afterLane)
    (valid : afterLane.phase ≠ .invalid) (active : afterLane.phase ≠ .done) :
    M.observeAck cfg monitor actual lane = { monitor with ack := some afterLane } := by
  simp only [M.observeAck, decoded, (F.phase_beq_false _ _).mpr valid, Bool.false_eq_true, ite_false,
    (F.phase_beq_false _ _).mpr active]

theorem data_assigned_lane {path : P.DataIngress initial current part lane} (value : N.DataAssigned core path actual) :
    M.dataLane (config initial native quantum allowance) lane actual = value.value.nextLane := by
  simp only [M.dataLane, path.phase]
  exact value.value.observed

theorem data_served_lane {path : P.DataTicket initial native current part lane} (value : N.DataServed core path actual) :
    M.dataLane (config initial native quantum allowance) lane actual = value.value.nextLane := by
  simp only [M.dataLane, path.phase]
  exact value.value.observed

theorem ack_assigned_lane {path : P.AckIngress initial current count lane} (value : N.AckAssigned core path actual) :
    M.ackLane (config initial native quantum allowance) lane actual = value.value.nextLane := by
  simp only [M.ackLane, path.phase]
  exact value.value.observed

theorem ack_served_lane {path : P.AckTicket initial native current (received.bytes lower upper).length lane}
    (value : N.AckServed core path actual) :
    M.ackLane (config initial native quantum allowance) lane actual = value.value.nextLane := by
  simp only [M.ackLane, path.phase]
  exact value.value.observed

theorem data_assigned_serves {path : P.DataIngress initial current part lane} (value : N.DataAssigned core path actual) :
    M.servesOption (M.laneDemand (config initial native quantum allowance) actual.before monitor lane) actual.event = true := by
  rw [value.value.value.move.beforeEq, value.value.event]
  have served := laneDemand_serves (config initial native quantum allowance) current.report.final monitor lane _
    (path.action (config initial native quantum allowance))
  cases sender <;> exact served

theorem data_served_serves {path : P.DataTicket initial native current part lane} (value : N.DataServed core path actual) :
    M.servesOption (M.laneDemand (config initial native quantum allowance) actual.before monitor lane) actual.event = true := by
  rw [value.value.value.move.beforeEq, value.value.value.facts.event]
  exact laneDemand_serves _ _ _ _ _ (path.action (config initial native quantum allowance))

theorem data_assigned_lower {path : P.DataIngress initial current part monitor.lower} (value : N.DataAssigned core path actual)
    (mode : monitor.mode = .originals) (first : monitor.lower.phase ≠ .needSend)
    (second : monitor.upper.phase ≠ .needSend) (ack : monitor.ack = none) :
    M.observe (config initial native quantum allowance) monitor actual =
      { monitor with lower := value.value.nextLane, lastOriginal := some .lower } := by
  rw [value.advance.ordinary, F.observe_original_lower _ _ _ mode first second ack (data_assigned_serves value)]
  apply data_lower_frame _ _ _ (data_assigned_lane value)
  all_goals rw [value.value.ticket.phase]; decide

theorem data_assigned_upper {path : P.DataIngress initial current part monitor.upper} (value : N.DataAssigned core path actual)
    (mode : monitor.mode = .originals) (first : monitor.lower.phase ≠ .needSend)
    (second : monitor.upper.phase ≠ .needSend) (ack : monitor.ack = none)
    (lower : M.servesOption (M.laneDemand (config initial native quantum allowance) actual.before monitor monitor.lower) actual.event = false) :
    M.observe (config initial native quantum allowance) monitor actual =
      { monitor with upper := value.value.nextLane, lastOriginal := some .upper } := by
  rw [value.advance.ordinary, F.observe_original_upper _ _ _ mode first second ack lower (data_assigned_serves value)]
  apply data_upper_frame _ _ _ (data_assigned_lane value)
  all_goals rw [value.value.ticket.phase]; decide

theorem data_assigned_retry {path : P.DataIngress initial current part monitor.retry} (value : N.DataAssigned core path actual)
    (mode : monitor.mode = .recovery) (ack : monitor.ack = none) (waiting : monitor.waiting = false) :
    M.observe (config initial native quantum allowance) monitor actual = { monitor with retry := value.value.nextLane } := by
  rw [value.advance.ordinary]
  simp only [M.observeOrdinary, mode, ack, waiting, Bool.false_eq_true, ite_false]
  simpa only [mode, ack, waiting] using data_retry_frame _ _ _ (data_assigned_lane value)
    (by rw [value.value.ticket.phase]; decide) (by rw [value.value.ticket.phase]; decide)

theorem data_served_lower {path : P.DataTicket initial native current part monitor.lower} (value : N.DataServed core path actual)
    (mode : monitor.mode = .originals) (first : monitor.lower.phase ≠ .needSend)
    (second : monitor.upper.phase ≠ .needSend) (ack : monitor.ack = none) :
    M.observe (config initial native quantum allowance) monitor actual =
      { monitor with lower := value.value.nextLane, lastOriginal := some .lower } := by
  rw [value.advance.ordinary, F.observe_original_lower _ _ _ mode first second ack (data_served_serves value)]
  apply data_lower_frame _ _ _ (data_served_lane value)
  all_goals rw [value.value.link.phase]; decide

theorem data_served_upper {path : P.DataTicket initial native current part monitor.upper} (value : N.DataServed core path actual)
    (mode : monitor.mode = .originals) (first : monitor.lower.phase ≠ .needSend)
    (second : monitor.upper.phase ≠ .needSend) (ack : monitor.ack = none)
    (lower : M.servesOption (M.laneDemand (config initial native quantum allowance) actual.before monitor monitor.lower) actual.event = false) :
    M.observe (config initial native quantum allowance) monitor actual =
      { monitor with upper := value.value.nextLane, lastOriginal := some .upper } := by
  rw [value.advance.ordinary, F.observe_original_upper _ _ _ mode first second ack lower (data_served_serves value)]
  apply data_upper_frame _ _ _ (data_served_lane value)
  all_goals rw [value.value.link.phase]; decide

theorem data_served_retry {path : P.DataTicket initial native current part monitor.retry} (value : N.DataServed core path actual)
    (mode : monitor.mode = .recovery) (ack : monitor.ack = none) (waiting : monitor.waiting = false) :
    M.observe (config initial native quantum allowance) monitor actual = { monitor with retry := value.value.nextLane } := by
  rw [value.advance.ordinary]
  simp only [M.observeOrdinary, mode, ack, waiting, Bool.false_eq_true, ite_false]
  simpa only [mode, ack, waiting] using data_retry_frame _ _ _ (data_served_lane value)
    (by rw [value.value.link.phase]; decide) (by rw [value.value.link.phase]; decide)

theorem ack_assigned {path : P.AckIngress initial current count lane} (value : N.AckAssigned core path actual)
    (active : monitor.mode = .originals ∨ monitor.mode = .recovery)
    (first : monitor.lower.phase ≠ .needSend) (second : monitor.upper.phase ≠ .needSend) (ack : monitor.ack = some lane) :
    M.observe (config initial native quantum allowance) monitor actual = { monitor with ack := some value.value.nextLane } := by
  rw [value.advance.ordinary, F.observe_ack _ _ _ _ active first second ack]
  apply ack_frame _ _ _ (ack_assigned_lane value)
  all_goals rw [value.value.ticket.phase]; decide

theorem ack_served {path : P.AckTicket initial native current (received.bytes lower upper).length lane}
    (value : N.AckServed core path actual) (active : monitor.mode = .originals ∨ monitor.mode = .recovery)
    (first : monitor.lower.phase ≠ .needSend) (second : monitor.upper.phase ≠ .needSend) (ack : monitor.ack = some lane) :
    M.observe (config initial native quantum allowance) monitor actual = { monitor with ack := some value.value.nextLane } := by
  rw [value.advance.ordinary, F.observe_ack _ _ _ _ active first second ack]
  apply ack_frame _ _ _ (ack_served_lane value)
  all_goals rw [value.value.link.phase]; decide

end Netlib.Check.CampusTCPTwoProgressPhaseObserve
