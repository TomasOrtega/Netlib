import Netlib.Check.CampusTCPTwoTransferServicePaths

/-!
# Exact ordinary service observation at the current location

The actual service supplies its new link and custody identity.
The selected lane retains every other path and exchange counter.
-/

namespace Netlib.Check.CampusTCPTwoTransferServiceObserve

open Protocol Protocol.TCP CampusTCPEnabled
open CampusTCPModel (Input State Step Event Served Ticket Transit)
open CampusTCPRound (Cut)
open CampusTCPTwoTransferMonitor
open CampusTCPTwoTransferDrainObserve (linkLane)

namespace N
export CampusTCPTwoTransferNetwork (Service)
end N
namespace L
export CampusTCPTwoProgressMonitor (Monitor Lane dataLane ackLane observeData observeAck observeOrdinary laneDemand servesOption)
end L
namespace F
export CampusTCPTwoProgressMonitorFacts (observe_action observe_original_lower observe_original_upper observe_ack phase_beq_false)
end F
namespace X
export CampusTCPTwoExchangeMonitor (observe allowed)
end X

local notation "Config" => CampusTCPTwoTransferMonitor.Config

variable {input : Input} {complete : TCPHandshake.Completed input.active input.passive}
variable {current : Cut input complete} {config : Config} {monitor : Monitor} {actual : Step input}
variable {item : Theory.Outstanding.Item (Ticket input.active input.passive)}
variable {hit : FlowNAT.Hit} {session : Admission.Session} {served : Served input}
variable {emission : WireForwarding.Emission served.ticket.value.source.packet}
variable {emitted : served.evidence.output = some emission}

private theorem outer_valid (ordinary : monitor.mode = .armed ∨ monitor.mode = .finished) : monitor.mode ≠ .invalid := by
  rcases ordinary with mode | mode <;> rw [mode] <;> decide

private theorem noDrain (ordinary : monitor.mode = .armed ∨ monitor.mode = .finished) :
    drainTicket state monitor = none := by
  apply CampusTCPTwoTransferControlObserve.noDrain_of_non_capture
  rcases ordinary with mode | mode <;> rw [mode] <;> decide

theorem local_allowed (ordinary : monitor.mode = .armed ∨ monitor.mode = .finished)
    (control : controlDemand monitor = none) (forward : monitor.exchange.mode = .forward)
    (allowed : Allowed config state monitor event) :
    CampusTCPTwoProgressMonitor.Allowed (config.at state).forward state monitor.exchange.forward event := by
  simpa only [CampusTCPTwoProgressMonitor.Allowed, Allowed, CampusTCPTwoTransferMonitor.allowed, outer_valid ordinary, decide_false,
    Bool.false_eq_true, ite_false, noDrain ordinary, control, X.allowed, forward] using allowed

def afterService (monitor : Monitor) (next : L.Monitor) : Monitor :=
  { monitor with exchange := { monitor.exchange with forward := next, slots := monitor.exchange.slots + 1 } }

theorem afterService_healthy (ordinary : monitor.mode = .armed ∨ monitor.mode = .finished) (next : L.Monitor) :
    (afterService monitor next).mode ≠ .invalid := outer_valid ordinary

private theorem service_ordinary (value : N.Service current item hit session actual served emission emitted)
    (ordinary : monitor.mode = .armed ∨ monitor.mode = .finished)
    (control : controlDemand monitor = none) (forward : monitor.exchange.mode = .forward)
    (allowed : Allowed config current.report.final monitor actual.event) :
    CampusTCPTwoProgressMonitor.observe (config.at actual.before).forward monitor.exchange.forward actual =
      L.observeOrdinary (config.at actual.before).forward monitor.exchange.forward actual := by
  apply F.observe_action _ _ _ value.move.supported value.move.passed
    (by rw [value.move.beforeEq]; exact local_allowed ordinary control forward allowed) (.serve item.id)
  exact value.facts.event

private theorem lift_service (value : N.Service current item hit session actual served emission emitted)
    (ordinaryMode : monitor.mode = .armed ∨ monitor.mode = .finished)
    (control : controlDemand monitor = none) (forward : monitor.exchange.mode = .forward)
    (allowed : Allowed config current.report.final monitor actual.event)
    (next : L.Monitor) (observed : L.observeOrdinary (config.at actual.before).forward monitor.exchange.forward actual = next)
    (mode : next.mode = monitor.exchange.forward.mode)
    (healthy : monitor.exchange.forward.mode ≠ .invalid) (unfinished : monitor.exchange.forward.mode ≠ .done) :
    observe config monitor actual = afterService monitor next := by
  have localAllowed := local_allowed ordinaryMode control forward allowed
  have checked : (actual.result.supported && actual.result.passed &&
      CampusTCPTwoTransferMonitor.allowed config actual.before monitor actual.event) = true := by
    rw [value.move.supported, value.move.passed, value.move.beforeEq]
    exact allowed
  have innerChecked : (actual.result.supported && actual.result.passed &&
      CampusTCPTwoExchangeMonitor.allowed (config.at actual.before) actual.before monitor.exchange actual.event) = true := by
    rw [value.move.supported, value.move.passed]
    simpa only [Bool.true_and, X.allowed, forward, value.move.beforeEq, CampusTCPTwoProgressMonitor.Allowed] using localAllowed
  have localObserved := (service_ordinary value ordinaryMode control forward allowed).trans observed
  rw [observe, ite_eq_left checked, value.move.beforeEq, noDrain ordinaryMode, control]
  unfold CampusTCPTwoTransferMonitor.ordinary
  rw [X.observe, ite_eq_left innerChecked, forward, localObserved]
  simp only [mode, CampusTCPTwoProgressMonitorFacts.mode_beq, healthy, unfinished, decide_false,
    Bool.false_eq_true, ite_false]
  change (if decide (monitor.exchange.mode = .invalid) then _ else _) = _
  rw [forward]
  simp only [reduceCtorEq, decide_false, Bool.false_eq_true, ite_false]
  unfold afterService
  congr 2
  · change (match actual.event with | .dropPacket id => monitor.exchange.drops ++ [id] | _ => monitor.exchange.drops) = _
    rw [value.facts.event]
  · change (match actual.event with | .timeout _ true => monitor.exchange.timeouts + 1 | _ => monitor.exchange.timeouts) = _
    rw [value.facts.event]

private theorem service_lane (value : N.Service current item hit session actual served emission emitted)
    (localConfig : CampusTCPTwoProgressMonitor.Config) (lane : L.Lane) (phase : lane.phase = .dataTicket) (packet : Nat)
    (pending : actual.result.state.custody.pendingID (Transit.linkAt current.report.final.services.length) = some packet) :
    L.dataLane localConfig lane actual = linkLane lane current.report.final.services.length packet := by
  simp only [L.dataLane, phase, CampusTCPGapProgressMonitor.observeService, value.facts.recorded, emitted,
    value.move.beforeEq, pending, CampusTCPTwoProgressMonitor.Lane.toGap, CampusTCPTwoProgressMonitor.Lane.ofGap]
  rfl

private theorem lane_serves (localConfig : CampusTCPTwoProgressMonitor.Config) (state : State input)
    (localMonitor : L.Monitor) (lane : L.Lane) (action : CampusTCPRoundMonitor.Action)
    (next : CampusTCPGapProgressMonitor.nextAction localConfig.toConfig state lane.toGap = some action) :
    L.servesOption (L.laneDemand localConfig state localMonitor lane) action.event = true := by
  cases packet : CampusTCPGapProgressMonitor.packetAt lane.toGap with
  | none => simp [L.laneDemand, next, packet, L.servesOption, CampusTCPGapProgressMonitor.serves,
      CampusTCPRoundMonitor.Action.actionOf_event]
  | some id =>
    by_cases budget : localMonitor.drops.length < localConfig.lossAllowance
    all_goals simp [L.laneDemand, next, packet, budget, L.servesOption, CampusTCPGapProgressMonitor.serves,
      CampusTCPRoundMonitor.Action.actionOf_event]

private theorem ticket_serves (value : N.Service current item hit session actual served emission emitted)
    (lane : L.Lane) (phase : lane.phase = .dataTicket) (ticket : lane.refs.dataTicket = some item.id) :
    L.servesOption (L.laneDemand (config.at actual.before).forward actual.before monitor.exchange.forward lane) actual.event = true := by
  rw [value.facts.event]
  apply lane_serves _ _ _ _ (.serve item.id)
  simp only [CampusTCPGapProgressMonitor.nextAction, CampusTCPTwoProgressMonitor.Lane.toGap, phase, ticket]
  obtain ⟨completed, _, same, _⟩ := value.facts.completed
  have member : item ∈ actual.before.work.pending := by
    rw [← same]
    exact completed.member
  unfold CampusTCPRoundMonitor.ticketAction
  simp only [bind, Option.bind]
  cases found : actual.before.work.pending.find? (fun candidate => candidate.id == item.id) with
  | none => exact False.elim ((List.find?_eq_none.mp found) item member (beq_self_eq_true _))
  | some candidate => rfl

theorem lower_observe (value : N.Service current item hit session actual served emission emitted)
    (ordinary : monitor.mode = .armed ∨ monitor.mode = .finished)
    (control : controlDemand monitor = none) (forward : monitor.exchange.mode = .forward)
    (allowed : Allowed config current.report.final monitor actual.event)
    (mode : monitor.exchange.forward.mode = .originals)
    (first : monitor.exchange.forward.lower.phase = .dataTicket)
    (ticket : monitor.exchange.forward.lower.refs.dataTicket = some item.id)
    (second : monitor.exchange.forward.upper.phase ≠ .needSend) (ack : monitor.exchange.forward.ack = none) :
    ∃ packet, actual.result.state.custody.pendingID (Transit.linkAt current.report.final.services.length) = some packet ∧
      observe config monitor actual = afterService monitor
        { monitor.exchange.forward with
          lower := linkLane monitor.exchange.forward.lower current.report.final.services.length packet
          lastOriginal := some .lower } := by
  obtain ⟨packet, pending⟩ := CampusTCPRoundMonitorFacts.service_pending actual served value.facts.recorded emission emitted
  rw [value.move.beforeEq] at pending
  have decoded := service_lane value (config.at actual.before).forward _ first packet pending
  have firstNot : monitor.exchange.forward.lower.phase ≠ .needSend := by rw [first]; decide
  have observed := F.observe_original_lower (config.at actual.before).forward _ actual mode firstNot second ack (ticket_serves value _ first ticket)
  have update : L.observeData (config.at actual.before).forward monitor.exchange.forward actual .lower =
      { monitor.exchange.forward with
        lower := linkLane monitor.exchange.forward.lower current.report.final.services.length packet
        lastOriginal := some .lower } := by simp only [L.observeData, decoded]; rfl
  refine ⟨packet, pending, lift_service value ordinary control forward allowed _ (observed.trans update) rfl ?_ ?_⟩
  all_goals rw [mode]; decide

theorem upper_observe (value : N.Service current item hit session actual served emission emitted)
    (ordinary : monitor.mode = .armed ∨ monitor.mode = .finished)
    (control : controlDemand monitor = none) (forward : monitor.exchange.mode = .forward)
    (allowed : Allowed config current.report.final monitor actual.event)
    (mode : monitor.exchange.forward.mode = .originals)
    (first : monitor.exchange.forward.lower.phase ≠ .needSend)
    (second : monitor.exchange.forward.upper.phase = .dataTicket)
    (ticket : monitor.exchange.forward.upper.refs.dataTicket = some item.id) (ack : monitor.exchange.forward.ack = none)
    (lower : L.servesOption (L.laneDemand (config.at actual.before).forward actual.before monitor.exchange.forward
      monitor.exchange.forward.lower) actual.event = false) :
    ∃ packet, actual.result.state.custody.pendingID (Transit.linkAt current.report.final.services.length) = some packet ∧
      observe config monitor actual = afterService monitor
        { monitor.exchange.forward with
          upper := linkLane monitor.exchange.forward.upper current.report.final.services.length packet
          lastOriginal := some .upper } := by
  obtain ⟨packet, pending⟩ := CampusTCPRoundMonitorFacts.service_pending actual served value.facts.recorded emission emitted
  rw [value.move.beforeEq] at pending
  have decoded := service_lane value (config.at actual.before).forward _ second packet pending
  have secondNot : monitor.exchange.forward.upper.phase ≠ .needSend := by rw [second]; decide
  have observed := F.observe_original_upper (config.at actual.before).forward _ actual mode first secondNot ack lower (ticket_serves value _ second ticket)
  have update : L.observeData (config.at actual.before).forward monitor.exchange.forward actual .upper =
      { monitor.exchange.forward with
        upper := linkLane monitor.exchange.forward.upper current.report.final.services.length packet
        lastOriginal := some .upper } := by simp only [L.observeData, decoded]; rfl
  refine ⟨packet, pending, lift_service value ordinary control forward allowed _ (observed.trans update) rfl ?_ ?_⟩
  all_goals rw [mode]; decide

theorem retry_observe (value : N.Service current item hit session actual served emission emitted)
    (ordinary : monitor.mode = .armed ∨ monitor.mode = .finished)
    (control : controlDemand monitor = none) (forward : monitor.exchange.mode = .forward)
    (allowed : Allowed config current.report.final monitor actual.event)
    (mode : monitor.exchange.forward.mode = .recovery)
    (phase : monitor.exchange.forward.retry.phase = .dataTicket)
    (ack : monitor.exchange.forward.ack = none) (waiting : monitor.exchange.forward.waiting = false) :
    ∃ packet, actual.result.state.custody.pendingID (Transit.linkAt current.report.final.services.length) = some packet ∧
      observe config monitor actual = afterService monitor
        { monitor.exchange.forward with retry := linkLane monitor.exchange.forward.retry current.report.final.services.length packet } := by
  obtain ⟨packet, pending⟩ := CampusTCPRoundMonitorFacts.service_pending actual served value.facts.recorded emission emitted
  rw [value.move.beforeEq] at pending
  have decoded := service_lane value (config.at actual.before).forward _ phase packet pending
  have observed : L.observeOrdinary (config.at actual.before).forward monitor.exchange.forward actual =
      { monitor.exchange.forward with retry := linkLane monitor.exchange.forward.retry current.report.final.services.length packet } := by
    simp only [L.observeOrdinary, mode, ack, waiting, Bool.false_eq_true, ite_false, L.observeData, decoded]
    rfl
  refine ⟨packet, pending, lift_service value ordinary control forward allowed _ observed rfl ?_ ?_⟩
  all_goals rw [mode]; decide

def ackLinkLane (lane : L.Lane) (index packet : Nat) : L.Lane :=
  ⟨.ackLink, { lane.refs with ackService := some index, ackLinkPacket := some packet }⟩

theorem ack_observe (value : N.Service current item hit session actual served emission emitted)
    (ordinary : monitor.mode = .armed ∨ monitor.mode = .finished)
    (control : controlDemand monitor = none) (forward : monitor.exchange.mode = .forward)
    (allowed : Allowed config current.report.final monitor actual.event)
    (mode : monitor.exchange.forward.mode = .originals ∨ monitor.exchange.forward.mode = .recovery)
    (first : monitor.exchange.forward.lower.phase ≠ .needSend) (second : monitor.exchange.forward.upper.phase ≠ .needSend)
    (lane : L.Lane) (ack : monitor.exchange.forward.ack = some lane) (phase : lane.phase = .ackTicket) :
    ∃ packet, actual.result.state.custody.pendingID (Transit.linkAt current.report.final.services.length) = some packet ∧
      observe config monitor actual = afterService monitor
        { monitor.exchange.forward with ack := some (ackLinkLane lane current.report.final.services.length packet) } := by
  obtain ⟨packet, pending⟩ := CampusTCPRoundMonitorFacts.service_pending actual served value.facts.recorded emission emitted
  rw [value.move.beforeEq] at pending
  have decoded : L.ackLane (config.at actual.before).forward lane actual = ackLinkLane lane current.report.final.services.length packet := by
    simp only [L.ackLane, phase, CampusTCPGapProgressMonitor.observeService, value.facts.recorded, emitted,
      value.move.beforeEq, pending, CampusTCPTwoProgressMonitor.Lane.toGap, CampusTCPTwoProgressMonitor.Lane.ofGap]
    rfl
  have observed := F.observe_ack (config.at actual.before).forward _ actual _ mode first second ack
  have update : L.observeAck (config.at actual.before).forward monitor.exchange.forward actual lane =
      { monitor.exchange.forward with ack := some (ackLinkLane lane current.report.final.services.length packet) } := by
    simp only [L.observeAck, decoded]
    rfl
  refine ⟨packet, pending, lift_service value ordinary control forward allowed _ (observed.trans update) rfl ?_ ?_⟩
  all_goals rcases mode with mode | mode <;> rw [mode] <;> decide

end Netlib.Check.CampusTCPTwoTransferServiceObserve
