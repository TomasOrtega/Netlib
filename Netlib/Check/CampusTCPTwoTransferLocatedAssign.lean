import Netlib.Check.CampusTCPTwoTransferControlState
import Netlib.Check.CampusTCPTwoTransferPhaseState
import Netlib.Check.CampusTCPTwoProgressPhaseObserve

/-!
# Actual ordinary assignments at the current gateway

The current control phase supplies routing. The stored assignment supplies the
new ticket, while endpoint state and the actual loss suffix remain unchanged.
-/

namespace Netlib.Check.CampusTCPTwoTransferLocatedAssign

open Protocol Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart
open CampusTCPTwoTransferNative (Checks Routing)
open CampusTCPTwoTransferLocatedCore (Core config)
open CampusTCPTwoTransferState (LiveAt)
open CampusTCPTwoTransferControlState (Phase)
open CampusTCPTwoTransferPhaseState (Active)
open CampusTCPTwoTransferPaths (DataIngress DataTicket AckIngress AckTicket dataTicketLane ackTicketLane)

namespace N
export CampusTCPTwoTransferNetwork (Assignment assign_at)
end N
namespace M
export CampusTCPTwoProgressMonitor (Monitor Lane Allowed observe observeOrdinary observeData observeAck laneDemand servesOption)
end M
namespace W
export CampusTCPTwoTransferMonitor (Monitor Allowed observe drainTicket controlDemand)
end W
namespace F
export CampusTCPTwoProgressMonitorFacts (observe_action observe_original_lower observe_original_upper observe_ack phase_beq_false)
end F

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current : Cut input complete} {sender : Actor} {gateway location : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {checks : Checks cut initial.gatewayState.session.entry} {routing : Routing cut gateway}
variable {quantum allowance : Nat} {reverseLower reverseUpper : List UInt8}
variable {monitor : W.Monitor} {sent : CampusTCPTwoProgressSender.Stage initial}
variable {received : CampusTCPTwoProgressReceiver.Stage} {part : CampusTCPTwoProgressSender.Part}
variable {lane : M.Lane} {actual : Step input} {index : Nat} {ingress : I.InterfaceRef}
variable {produced : Produced input.active input.passive}

local notation "cfg" => config initial checks routing quantum allowance reverseLower reverseUpper

theorem allowed_assign (config : CampusTCPTwoTransferMonitor.Config) (state : State input) (monitor : W.Monitor)
    (allowed : W.Allowed config state monitor (.assign index ingress)) :
    W.drainTicket state monitor = none ∧ W.controlDemand monitor = none ∧
      CampusTCPTwoExchangeMonitor.Allowed (config.at state) state monitor.exchange (.assign index ingress) := by
  by_cases invalid : monitor.mode = .invalid
  · simp only [W.Allowed, CampusTCPTwoTransferMonitor.allowed, invalid, decide_true, ite_true, Bool.false_eq_true] at allowed
  · cases drain : W.drainTicket state monitor with
    | some ticket => simp [W.Allowed, CampusTCPTwoTransferMonitor.allowed, invalid, drain,
        CampusTCPTwoTransferMonitor.drainServes] at allowed
    | none =>
      cases selected : W.controlDemand monitor with
      | none => exact ⟨rfl, rfl, by simpa only [W.Allowed, CampusTCPTwoTransferMonitor.allowed, invalid,
          decide_false, Bool.false_eq_true, ite_false, drain, selected, CampusTCPTwoExchangeMonitor.Allowed] using allowed⟩
      | some kind =>
        cases kind <;> simp [W.Allowed, CampusTCPTwoTransferMonitor.allowed, invalid, drain, selected,
          CampusTCPTwoTransferMonitor.Control.serves] at allowed

theorem current_routing (phase : Phase current.report.final monitor.mode location)
    (ordinary : W.controlDemand monitor = none) : Routing current location := by
  generalize modeEq : monitor.mode = mode at phase
  cases phase with
  | armed source =>
    exact ⟨fun actor => by cases actor <;> first | exact source.client | exact source.server,
      source.paused, fun _ => ⟨source.unsealed, source.unfenced⟩, by intro impossible; cases impossible⟩
  | finished fields =>
    exact CampusTCPTwoTransferControlState.finished_routing (.finished fields)
  | capture | install | clientRoute | serverRoute | fence | resume =>
    simp only [W.controlDemand, modeEq] at ordinary
    cases ordinary

def afterAssign (monitor : W.Monitor) (forward : M.Monitor) : W.Monitor :=
  { monitor with exchange := { monitor.exchange with forward, slots := monitor.exchange.slots + 1 } }

theorem observe_assign (value : N.Assignment current index ingress produced actual)
    (phase : monitor.exchange.mode = .forward) (allowed : W.Allowed cfg current.report.final monitor actual.event)
    (forward : M.Monitor) (mode : forward.mode = .originals ∨ forward.mode = .recovery)
    (localStep : M.observe ((cfg).at current.report.final).forward monitor.exchange.forward actual = forward) :
    W.observe cfg monitor actual = afterAssign monitor forward := by
  obtain ⟨drain, control, ordinary⟩ := allowed_assign cfg current.report.final monitor
    (by rw [← value.facts.event]; exact allowed)
  have checked : (actual.result.supported && actual.result.passed &&
      CampusTCPTwoExchangeMonitor.allowed ((cfg).at actual.before) actual.before monitor.exchange actual.event) = true := by
    rw [value.move.supported, value.move.passed, value.move.beforeEq]
    simpa only [value.facts.event, Bool.true_and, CampusTCPTwoExchangeMonitor.Allowed] using ordinary
  have exchangeStep : CampusTCPTwoExchangeMonitor.observe ((cfg).at actual.before) monitor.exchange actual =
      { monitor.exchange with forward, slots := monitor.exchange.slots + 1 } := by
    rw [CampusTCPTwoExchangeMonitor.observe, ite_eq_left checked, value.move.beforeEq]
    simp only [phase, localStep]
    have valid : (forward.mode == .invalid) = false := by
      rcases mode with original | recovery
      · rw [original]; rfl
      · rw [recovery]; rfl
    have active : (forward.mode == .done) = false := by
      rcases mode with original | recovery
      · rw [original]; rfl
      · rw [recovery]; rfl
    rw [valid, active]
    simp only [Bool.false_eq_true, ite_false]
    change { monitor.exchange with
      forward := forward
      slots := monitor.exchange.slots + 1
      drops := (match actual.event with | .dropPacket id => monitor.exchange.drops ++ [id] | _ => monitor.exchange.drops)
      timeouts := (match actual.event with | .timeout _ true => monitor.exchange.timeouts + 1 | _ => monitor.exchange.timeouts) } = _
    rw [value.facts.event]
    simp only [phase]
  have checkedWhole : (actual.result.supported && actual.result.passed &&
      CampusTCPTwoTransferMonitor.allowed cfg actual.before monitor actual.event) = true := by
    rw [value.move.supported, value.move.passed, value.move.beforeEq]
    exact allowed
  rw [W.observe, ite_eq_left checkedWhole, value.move.beforeEq, drain, control]
  rw [CampusTCPTwoTransferMonitor.ordinary, exchangeStep]
  simp only [phase, reduceCtorEq, decide_false, Bool.false_eq_true, ite_false, afterAssign]

private def assignmentLive (live : LiveAt initial current location sent monitor.exchange.forward.retries received)
    (value : N.Assignment current index ingress produced actual)
    (retries : (W.observe cfg monitor actual).exchange.forward.retries = monitor.exchange.forward.retries) :
    LiveAt initial value.move.after location sent (W.observe cfg monitor actual).exchange.forward.retries received := by
  exact ⟨⟨⟨live.anchor.retained.trans value.move.retained, fun selected => (live.anchor.policy selected).trans
    (CampusTCPRoundEnvironment.service_environment _ _ value.environment selected)⟩,
    by rw [value.endpoints]; exact live.anchor.guards⟩,
    by rw [value.endpoints, retries]; exact live.senderFlight,
    by rw [value.endpoints]; exact live.receiverFacts,
    live.gatewayState.reframe (value.serviceFrame location), live.gatewayWindow,
    live.history.same (by rw [value.endpoints])⟩

private def assignmentCore (core : Core initial checks routing quantum allowance reverseLower reverseUpper current monitor location sent received)
    (value : N.Assignment current index ingress produced actual)
    (forward : M.Monitor) (observed : W.observe cfg monitor actual = afterAssign monitor forward)
    (drops : forward.drops = monitor.exchange.forward.drops) (retries : forward.retries = monitor.exchange.forward.retries)
    (queue : CampusTCPTwoTransferQueue.Closed value.move.after.report.final forward) :
    Core initial checks routing quantum allowance reverseLower reverseUpper value.move.after (W.observe cfg monitor actual) location sent received := by
  have counter : (W.observe cfg monitor actual).exchange.forward.retries = monitor.exchange.forward.retries := by
    rw [observed]; exact retries
  let live := assignmentLive core.live value counter
  have recovery : live.senderFlight.recovery = core.live.senderFlight.recovery := by
    have same := congrArg (fun endpoints => (endpoint endpoints sender).recovery) value.endpoints
    exact Option.some.inj (live.senderFlight.runtime.symm.trans (same.trans core.live.senderFlight.runtime))
  let sources := CampusTCPTwoTransferSources.Frame.assignment value
  exact {
    live
    senderWindow := by rw [value.endpoints]; exact core.senderWindow
    originals := sources.originals core.originals
    originalTimes := core.originalTimes
    writer := sources.writer core.writer
    losses := core.losses.append value.move
      (by rw [CampusTCPTwoProgressLossHistory.isDrop, value.facts.event])
      (by rw [CampusTCPTwoExchangeLoss.isTimeoutOutput, value.facts.event])
      (by rw [observed]; exact drops) counter (by rw [observed]; rfl) (by rw [observed]; rfl)
    lossBound := by rw [observed]; change forward.drops.length ≤ allowance; rw [drops]; exact core.lossBound
    primaryQueue := by rw [observed]; exact queue
    retired := core.retired
    gatewayAck := core.gatewayAck
    peerSettled := core.peerSettled
    peerWindow := core.peerWindow
    covered := core.covered
    duplicates := by rw [recovery]; exact core.duplicates
    emptyDuplicate := by rw [recovery]; exact core.emptyDuplicate
    deadline := by rw [recovery]; exact core.deadline
    estimatorBeforeRetire := by rw [recovery]; exact core.estimatorBeforeRetire
    rtoBeforeRetire := by rw [recovery, counter]; exact core.rtoBeforeRetire
    rtoPending := by rw [recovery, counter]; exact core.rtoPending }

def dataAfter (monitor : M.Monitor) (part : CampusTCPTwoProgressSender.Part) (lane : M.Lane) : M.Monitor :=
  match part with
  | .lower => { monitor with lower := lane, lastOriginal := some .lower }
  | .upper => { monitor with upper := lane, lastOriginal := some .upper }

structure DataAssigned (core : Core initial checks routing quantum allowance reverseLower reverseUpper current monitor location sent received)
    (path : DataIngress initial current part lane) (actual : Step input) where
  value : N.Assignment current path.output.index (checks.ingress (current.report.final.owner sender) sender) path.output.produced actual
  next : Core initial checks routing quantum allowance reverseLower reverseUpper value.move.after (W.observe cfg monitor actual) location sent received
  gateway : next.live.gatewayState = core.live.gatewayState.reframe (value.serviceFrame location)
  ticket : DataTicket initial checks value.move.after part (dataTicketLane lane value.ticket.id)
  literal : ticket = DataTicket.ofAssignment path checks value
  assigned : ticket.assignedGateway = location
  observed : W.observe cfg monitor actual = afterAssign monitor
    (dataAfter monitor.exchange.forward part (dataTicketLane lane value.ticket.id))
  healthy : (W.observe cfg monitor actual).mode ≠ .invalid
  book : next.losses.book = core.losses.book

private theorem data_observed (path : DataIngress initial current part lane)
    (value : N.Assignment current path.output.index (checks.ingress (current.report.final.owner sender) sender) path.output.produced actual) :
    CampusTCPTwoProgressMonitor.dataLane ((cfg).at current.report.final).forward lane actual = dataTicketLane lane value.ticket.id := by
  simp only [CampusTCPTwoProgressMonitor.dataLane, path.phase]
  exact DataTicket.assignment_observed path checks value

private theorem data_lower (path : DataIngress initial current .lower monitor.exchange.forward.lower)
    (value : N.Assignment current path.output.index (checks.ingress (current.report.final.owner sender) sender) path.output.produced actual)
    (allowed : M.Allowed ((cfg).at current.report.final).forward current.report.final monitor.exchange.forward actual.event)
    (mode : monitor.exchange.forward.mode = .originals) (first : monitor.exchange.forward.lower.phase ≠ .needSend)
    (second : monitor.exchange.forward.upper.phase ≠ .needSend) (ack : monitor.exchange.forward.ack = none) :
    M.observe ((cfg).at current.report.final).forward monitor.exchange.forward actual =
      dataAfter monitor.exchange.forward .lower (dataTicketLane monitor.exchange.forward.lower value.ticket.id) := by
  have serves := CampusTCPTwoProgressPhaseObserve.laneDemand_serves ((cfg).at current.report.final).forward
    current.report.final monitor.exchange.forward _ _ (path.action ((cfg).at current.report.final).forward)
  have selected : M.servesOption (M.laneDemand ((cfg).at current.report.final).forward actual.before monitor.exchange.forward
      monitor.exchange.forward.lower) actual.event = true := by
    rw [value.move.beforeEq, value.facts.event]
    cases sender <;> exact serves
  rw [F.observe_action _ _ _ value.move.supported value.move.passed (by rw [value.move.beforeEq]; exact allowed)
    (.assign path.output.index _) value.facts.event,
    F.observe_original_lower _ _ _ mode first second ack selected]
  simp only [M.observeData, data_observed path value, dataTicketLane,
    show (CampusTCPRoundMonitor.Phase.dataTicket == .invalid) = false by rfl,
    show (CampusTCPRoundMonitor.Phase.dataTicket == .done) = false by rfl, Bool.false_eq_true, ite_false, dataAfter]

private theorem data_upper (path : DataIngress initial current .upper monitor.exchange.forward.upper)
    (value : N.Assignment current path.output.index (checks.ingress (current.report.final.owner sender) sender) path.output.produced actual)
    (allowed : M.Allowed ((cfg).at current.report.final).forward current.report.final monitor.exchange.forward actual.event)
    (mode : monitor.exchange.forward.mode = .originals) (first : monitor.exchange.forward.lower.phase ≠ .needSend)
    (second : monitor.exchange.forward.upper.phase ≠ .needSend) (ack : monitor.exchange.forward.ack = none)
    (lowerServes : M.servesOption (M.laneDemand ((cfg).at current.report.final).forward current.report.final monitor.exchange.forward
      monitor.exchange.forward.lower) actual.event = false) :
    M.observe ((cfg).at current.report.final).forward monitor.exchange.forward actual =
      dataAfter monitor.exchange.forward .upper (dataTicketLane monitor.exchange.forward.upper value.ticket.id) := by
  have serves := CampusTCPTwoProgressPhaseObserve.laneDemand_serves ((cfg).at current.report.final).forward
    current.report.final monitor.exchange.forward _ _ (path.action ((cfg).at current.report.final).forward)
  have selected : M.servesOption (M.laneDemand ((cfg).at current.report.final).forward actual.before monitor.exchange.forward
      monitor.exchange.forward.upper) actual.event = true := by
    rw [value.move.beforeEq, value.facts.event]
    cases sender <;> exact serves
  rw [F.observe_action _ _ _ value.move.supported value.move.passed (by rw [value.move.beforeEq]; exact allowed)
    (.assign path.output.index _) value.facts.event,
    F.observe_original_upper _ _ _ mode first second ack (by rw [value.move.beforeEq]; exact lowerServes) selected]
  simp only [M.observeData, data_observed path value, dataTicketLane,
    show (CampusTCPRoundMonitor.Phase.dataTicket == .invalid) = false by rfl,
    show (CampusTCPRoundMonitor.Phase.dataTicket == .done) = false by rfl, Bool.false_eq_true, ite_false, dataAfter]

private theorem finish_data (core : Core initial checks routing quantum allowance reverseLower reverseUpper current monitor location sent received)
    (path : DataIngress initial current part lane)
    (value : N.Assignment current path.output.index (checks.ingress (current.report.final.owner sender) sender) path.output.produced actual)
    (owners : Routing current location) (healthy : monitor.mode ≠ .invalid)
    (observed : W.observe cfg monitor actual = afterAssign monitor (dataAfter monitor.exchange.forward part (dataTicketLane lane value.ticket.id)))
    (queue : CampusTCPTwoTransferQueue.Closed value.move.after.report.final
      (dataAfter monitor.exchange.forward part (dataTicketLane lane value.ticket.id))) : Nonempty (DataAssigned core path actual) := by
  let next := assignmentCore core value _ observed (by cases part <;> rfl) (by cases part <;> rfl) queue
  exact ⟨{
    value, next, gateway := rfl, ticket := DataTicket.ofAssignment path checks value, literal := rfl
    assigned := owners.owners sender
    observed
    healthy := by rw [observed]; exact healthy
    book := rfl }⟩

theorem lower_at (core : Core initial checks routing quantum allowance reverseLower reverseUpper current monitor location sent received)
    (active : Active core) (phase : Phase current.report.final monitor.mode location)
    (path : DataIngress initial current .lower monitor.exchange.forward.lower)
    (mode : monitor.exchange.forward.mode = .originals) (ack : monitor.exchange.forward.ack = none)
    (allowed : W.Allowed cfg current.report.final monitor
      (.assign path.output.index (checks.ingress (current.report.final.owner sender) sender))) :
    ∃ actual, Nonempty (DataAssigned core path actual) := by
  obtain ⟨drain, control, ordinary⟩ := allowed_assign cfg current.report.final monitor allowed
  have owners := current_routing phase control
  obtain ⟨actual, ⟨value⟩⟩ := N.assign_at current path.output.index _ path.output.produced path.output.stored
    (by rw [path.output.actor]; exact checks.route core.live.anchor.toRetained owners sender) path.pending
  have allowedActual : W.Allowed cfg current.report.final monitor actual.event := by rw [value.facts.event]; exact allowed
  have localAllowed : M.Allowed ((cfg).at current.report.final).forward current.report.final monitor.exchange.forward actual.event := by
    simpa only [M.Allowed, CampusTCPTwoExchangeMonitor.Allowed, CampusTCPTwoExchangeMonitor.allowed, active.exchange, value.facts.event] using ordinary
  have localStep := data_lower path value localAllowed mode active.lower_not_needSend active.upper_not_needSend ack
  have observed := observe_assign value active.exchange allowedActual
    (dataAfter monitor.exchange.forward .lower (dataTicketLane monitor.exchange.forward.lower value.ticket.id)) (Or.inl mode) localStep
  have queue := core.primaryQueue.assign_lower value path.phase
  have afterQueue : CampusTCPTwoTransferQueue.Closed value.move.after.report.final
      (dataAfter monitor.exchange.forward .lower (dataTicketLane monitor.exchange.forward.lower value.ticket.id)) :=
    queue.reframe rfl rfl rfl rfl
  have healthy : monitor.mode ≠ .invalid := by
    intro invalid
    simp only [W.Allowed, CampusTCPTwoTransferMonitor.allowed, invalid, decide_true, ite_true, Bool.false_eq_true] at allowed
  exact ⟨actual, finish_data core path value owners healthy observed afterQueue⟩

theorem upper_at (core : Core initial checks routing quantum allowance reverseLower reverseUpper current monitor location sent received)
    (active : Active core) (phase : Phase current.report.final monitor.mode location)
    (path : DataIngress initial current .upper monitor.exchange.forward.upper)
    (mode : monitor.exchange.forward.mode = .originals) (ack : monitor.exchange.forward.ack = none)
    (lowerServes : M.servesOption (M.laneDemand ((cfg).at current.report.final).forward current.report.final monitor.exchange.forward
      monitor.exchange.forward.lower) (.assign path.output.index (checks.ingress (current.report.final.owner sender) sender)) = false)
    (allowed : W.Allowed cfg current.report.final monitor
      (.assign path.output.index (checks.ingress (current.report.final.owner sender) sender))) :
    ∃ actual, Nonempty (DataAssigned core path actual) := by
  obtain ⟨drain, control, ordinary⟩ := allowed_assign cfg current.report.final monitor allowed
  have owners := current_routing phase control
  obtain ⟨actual, ⟨value⟩⟩ := N.assign_at current path.output.index _ path.output.produced path.output.stored
    (by rw [path.output.actor]; exact checks.route core.live.anchor.toRetained owners sender) path.pending
  have allowedActual : W.Allowed cfg current.report.final monitor actual.event := by rw [value.facts.event]; exact allowed
  have localAllowed : M.Allowed ((cfg).at current.report.final).forward current.report.final monitor.exchange.forward actual.event := by
    simpa only [M.Allowed, CampusTCPTwoExchangeMonitor.Allowed, CampusTCPTwoExchangeMonitor.allowed, active.exchange, value.facts.event] using ordinary
  have localStep := data_upper path value localAllowed mode active.lower_not_needSend active.upper_not_needSend ack
    (by rw [value.facts.event]; exact lowerServes)
  have observed := observe_assign value active.exchange allowedActual
    (dataAfter monitor.exchange.forward .upper (dataTicketLane monitor.exchange.forward.upper value.ticket.id)) (Or.inl mode) localStep
  have queue := core.primaryQueue.assign_upper value path.phase
  have afterQueue : CampusTCPTwoTransferQueue.Closed value.move.after.report.final
      (dataAfter monitor.exchange.forward .upper (dataTicketLane monitor.exchange.forward.upper value.ticket.id)) :=
    queue.reframe rfl rfl rfl rfl
  have healthy : monitor.mode ≠ .invalid := by
    intro invalid
    simp only [W.Allowed, CampusTCPTwoTransferMonitor.allowed, invalid, decide_true, ite_true, Bool.false_eq_true] at allowed
  exact ⟨actual, finish_data core path value owners healthy observed afterQueue⟩

private theorem standby_queue (closed : CampusTCPTwoTransferQueue.Closed current.report.final monitor.exchange.forward)
    (value : N.Assignment current index ingress produced actual) (standby : value.ticket.value.gateway = .standby) :
    CampusTCPTwoTransferQueue.Closed value.move.after.report.final monitor.exchange.forward := by
  intro item member primary
  rw [value.move.final, value.facts.work] at member
  rcases List.mem_append.mp member with old | fresh
  · exact closed item old primary
  · have same : item = value.ticket := List.mem_singleton.mp fresh
    subst item
    rw [standby] at primary
    cases primary

theorem finished_location (phase : Phase current.report.final monitor.mode location) (finished : monitor.mode = .finished) :
    location = .standby := by
  have fixed : Phase current.report.final .finished location := finished ▸ phase
  cases fixed
  rfl

structure RetryAssigned (core : Core initial checks routing quantum allowance reverseLower reverseUpper current monitor location sent received)
    (path : DataIngress initial current part monitor.exchange.forward.retry) (actual : Step input) where
  value : N.Assignment current path.output.index (checks.ingress (current.report.final.owner sender) sender) path.output.produced actual
  next : Core initial checks routing quantum allowance reverseLower reverseUpper value.move.after (W.observe cfg monitor actual) location sent received
  gateway : next.live.gatewayState = core.live.gatewayState.reframe (value.serviceFrame location)
  ticket : DataTicket initial checks value.move.after part (dataTicketLane monitor.exchange.forward.retry value.ticket.id)
  literal : ticket = DataTicket.ofAssignment path checks value
  assigned : ticket.assignedGateway = location
  observed : W.observe cfg monitor actual = afterAssign monitor
    { monitor.exchange.forward with retry := dataTicketLane monitor.exchange.forward.retry value.ticket.id }
  healthy : (W.observe cfg monitor actual).mode ≠ .invalid
  book : next.losses.book = core.losses.book

theorem retry_at (core : Core initial checks routing quantum allowance reverseLower reverseUpper current monitor location sent received)
    (active : Active core) (phase : Phase current.report.final monitor.mode location) (finished : monitor.mode = .finished)
    (path : DataIngress initial current part monitor.exchange.forward.retry)
    (mode : monitor.exchange.forward.mode = .recovery) (ack : monitor.exchange.forward.ack = none)
    (waiting : monitor.exchange.forward.waiting = false)
    (allowed : W.Allowed cfg current.report.final monitor
      (.assign path.output.index (checks.ingress (current.report.final.owner sender) sender))) :
    ∃ actual, Nonempty (RetryAssigned core path actual) := by
  obtain ⟨drain, control, ordinary⟩ := allowed_assign cfg current.report.final monitor allowed
  have owners := current_routing phase control
  have location := finished_location phase finished
  obtain ⟨actual, ⟨value⟩⟩ := N.assign_at current path.output.index _ path.output.produced path.output.stored
    (by rw [path.output.actor]; exact checks.route core.live.anchor.toRetained owners sender) path.pending
  have allowedActual : W.Allowed cfg current.report.final monitor actual.event := by rw [value.facts.event]; exact allowed
  have localAllowed : M.Allowed ((cfg).at current.report.final).forward current.report.final monitor.exchange.forward actual.event := by
    simpa only [M.Allowed, CampusTCPTwoExchangeMonitor.Allowed, CampusTCPTwoExchangeMonitor.allowed, active.exchange, value.facts.event] using ordinary
  have localStep : M.observe ((cfg).at current.report.final).forward monitor.exchange.forward actual =
      { monitor.exchange.forward with retry := dataTicketLane monitor.exchange.forward.retry value.ticket.id } := by
    rw [F.observe_action _ _ _ value.move.supported value.move.passed (by rw [value.move.beforeEq]; exact localAllowed)
      (.assign path.output.index _) value.facts.event]
    simp only [M.observeOrdinary, mode, ack, waiting, Bool.false_eq_true, ite_false]
    simp only [M.observeData, data_observed path value, dataTicketLane,
      show (CampusTCPRoundMonitor.Phase.dataTicket == .invalid) = false by rfl,
      show (CampusTCPRoundMonitor.Phase.dataTicket == .done) = false by rfl, Bool.false_eq_true, ite_false]
    simp only [mode, ack, waiting]
  have observed := observe_assign value active.exchange allowedActual
    { monitor.exchange.forward with retry := dataTicketLane monitor.exchange.forward.retry value.ticket.id } (Or.inr mode) localStep
  have queue := standby_queue core.primaryQueue value (by rw [value.ticket_gateway, path.output.actor, owners.owners sender, location])
  let next := assignmentCore core value _ observed rfl rfl (queue.reframe rfl rfl rfl rfl)
  exact ⟨actual, ⟨{
    value, next, gateway := rfl, ticket := DataTicket.ofAssignment path checks value, literal := rfl
    assigned := owners.owners sender
    observed
    healthy := by rw [observed]; change monitor.mode ≠ .invalid; rw [finished]; decide
    book := rfl }⟩⟩

structure AckAssigned (core : Core initial checks routing quantum allowance reverseLower reverseUpper current monitor location sent received)
    (path : AckIngress initial current (received.bytes lower upper).length lane) (actual : Step input) where
  value : N.Assignment current path.output.index (checks.ingress (current.report.final.owner sender.other) sender.other) path.output.produced actual
  next : Core initial checks routing quantum allowance reverseLower reverseUpper value.move.after (W.observe cfg monitor actual) location sent received
  gateway : next.live.gatewayState = core.live.gatewayState.reframe (value.serviceFrame location)
  ticket : AckTicket initial checks value.move.after (received.bytes lower upper).length (ackTicketLane lane value.ticket.id)
  literal : ticket = AckTicket.ofAssignment path checks value
  assigned : ticket.assignedGateway = location
  observed : W.observe cfg monitor actual = afterAssign monitor
    { monitor.exchange.forward with ack := some (ackTicketLane lane value.ticket.id) }
  healthy : (W.observe cfg monitor actual).mode ≠ .invalid
  book : next.losses.book = core.losses.book

theorem ack_at (core : Core initial checks routing quantum allowance reverseLower reverseUpper current monitor location sent received)
    (active : Active core) (phase : Phase current.report.final monitor.mode location) (finished : monitor.mode = .finished)
    (path : AckIngress initial current (received.bytes lower upper).length lane) (pending : monitor.exchange.forward.ack = some lane)
    (allowed : W.Allowed cfg current.report.final monitor
      (.assign path.output.index (checks.ingress (current.report.final.owner sender.other) sender.other))) :
    ∃ actual, Nonempty (AckAssigned core path actual) := by
  obtain ⟨drain, control, ordinary⟩ := allowed_assign cfg current.report.final monitor allowed
  have owners := current_routing phase control
  have location := finished_location phase finished
  obtain ⟨actual, ⟨value⟩⟩ := N.assign_at current path.output.index _ path.output.produced path.output.stored
    (by rw [path.output.actor]; exact checks.route core.live.anchor.toRetained owners sender.other) path.pending
  have allowedActual : W.Allowed cfg current.report.final monitor actual.event := by rw [value.facts.event]; exact allowed
  have localAllowed : M.Allowed ((cfg).at current.report.final).forward current.report.final monitor.exchange.forward actual.event := by
    simpa only [M.Allowed, CampusTCPTwoExchangeMonitor.Allowed, CampusTCPTwoExchangeMonitor.allowed, active.exchange, value.facts.event] using ordinary
  have decoded : CampusTCPTwoProgressMonitor.ackLane ((cfg).at current.report.final).forward lane actual = ackTicketLane lane value.ticket.id := by
    simp only [CampusTCPTwoProgressMonitor.ackLane, path.phase]
    exact AckTicket.assignment_observed path checks value
  have localStep : M.observe ((cfg).at current.report.final).forward monitor.exchange.forward actual =
      { monitor.exchange.forward with ack := some (ackTicketLane lane value.ticket.id) } := by
    rw [F.observe_action _ _ _ value.move.supported value.move.passed (by rw [value.move.beforeEq]; exact localAllowed)
      (.assign path.output.index _) value.facts.event,
      F.observe_ack _ _ _ lane active.mode active.lower_not_needSend active.upper_not_needSend pending]
    simp only [M.observeAck, decoded, ackTicketLane,
      show (CampusTCPRoundMonitor.Phase.ackTicket == .invalid) = false by rfl,
      show (CampusTCPRoundMonitor.Phase.ackTicket == .done) = false by rfl, Bool.false_eq_true, ite_false]
  have nextMode : ({ monitor.exchange.forward with ack := some (ackTicketLane lane value.ticket.id) } : M.Monitor).mode = .originals ∨
      ({ monitor.exchange.forward with ack := some (ackTicketLane lane value.ticket.id) } : M.Monitor).mode = .recovery := active.mode
  have observed := observe_assign value active.exchange allowedActual _ nextMode localStep
  have queue := standby_queue core.primaryQueue value (by rw [value.ticket_gateway, path.output.actor, owners.owners sender.other, location])
  let next := assignmentCore core value _ observed rfl rfl (queue.reframe rfl rfl rfl rfl)
  exact ⟨actual, ⟨{
    value, next, gateway := rfl, ticket := AckTicket.ofAssignment path checks value, literal := rfl
    assigned := owners.owners sender.other
    observed
    healthy := by rw [observed]; change monitor.mode ≠ .invalid; rw [finished]; decide
    book := rfl }⟩⟩

theorem Step.lower_assign (actual : Step input)
    (core : Core initial checks routing quantum allowance reverseLower reverseUpper current monitor location sent received)
    (active : Active core) (phase : Phase current.report.final monitor.mode location)
    (path : DataIngress initial current .lower monitor.exchange.forward.lower)
    (mode : monitor.exchange.forward.mode = .originals) (ack : monitor.exchange.forward.ack = none)
    (allowed : W.Allowed cfg current.report.final monitor actual.event)
    (before : actual.before = current.report.final)
    (event : actual.event = .assign path.output.index (checks.ingress (current.report.final.owner sender) sender)) :
    Nonempty (DataAssigned core path actual) := by
  obtain ⟨enabled, ⟨value⟩⟩ := lower_at core active phase path mode ack (by rw [← event]; exact allowed)
  have same := CampusTCPRoundPhaseBase.Step.eq_of_before_event enabled actual
    (value.value.move.beforeEq.trans before.symm) (value.value.facts.event.trans event.symm)
  exact ⟨same ▸ value⟩

theorem Step.upper_assign (actual : Step input)
    (core : Core initial checks routing quantum allowance reverseLower reverseUpper current monitor location sent received)
    (active : Active core) (phase : Phase current.report.final monitor.mode location)
    (path : DataIngress initial current .upper monitor.exchange.forward.upper)
    (mode : monitor.exchange.forward.mode = .originals) (ack : monitor.exchange.forward.ack = none)
    (lowerServes : M.servesOption (M.laneDemand ((cfg).at current.report.final).forward current.report.final monitor.exchange.forward
      monitor.exchange.forward.lower) actual.event = false)
    (allowed : W.Allowed cfg current.report.final monitor actual.event)
    (before : actual.before = current.report.final)
    (event : actual.event = .assign path.output.index (checks.ingress (current.report.final.owner sender) sender)) :
    Nonempty (DataAssigned core path actual) := by
  obtain ⟨enabled, ⟨value⟩⟩ := upper_at core active phase path mode ack
    (by rw [← event]; exact lowerServes) (by rw [← event]; exact allowed)
  have same := CampusTCPRoundPhaseBase.Step.eq_of_before_event enabled actual
    (value.value.move.beforeEq.trans before.symm) (value.value.facts.event.trans event.symm)
  exact ⟨same ▸ value⟩

theorem Step.retry_assign (actual : Step input)
    (core : Core initial checks routing quantum allowance reverseLower reverseUpper current monitor location sent received)
    (active : Active core) (phase : Phase current.report.final monitor.mode location) (finished : monitor.mode = .finished)
    (path : DataIngress initial current part monitor.exchange.forward.retry)
    (mode : monitor.exchange.forward.mode = .recovery) (ack : monitor.exchange.forward.ack = none)
    (waiting : monitor.exchange.forward.waiting = false)
    (allowed : W.Allowed cfg current.report.final monitor actual.event)
    (before : actual.before = current.report.final)
    (event : actual.event = .assign path.output.index (checks.ingress (current.report.final.owner sender) sender)) :
    Nonempty (RetryAssigned core path actual) := by
  obtain ⟨enabled, ⟨value⟩⟩ := retry_at core active phase finished path mode ack waiting (by rw [← event]; exact allowed)
  have same := CampusTCPRoundPhaseBase.Step.eq_of_before_event enabled actual
    (value.value.move.beforeEq.trans before.symm) (value.value.facts.event.trans event.symm)
  exact ⟨same ▸ value⟩

theorem Step.ack_assign (actual : Step input)
    (core : Core initial checks routing quantum allowance reverseLower reverseUpper current monitor location sent received)
    (active : Active core) (phase : Phase current.report.final monitor.mode location) (finished : monitor.mode = .finished)
    (path : AckIngress initial current (received.bytes lower upper).length lane) (pending : monitor.exchange.forward.ack = some lane)
    (allowed : W.Allowed cfg current.report.final monitor actual.event)
    (before : actual.before = current.report.final)
    (event : actual.event = .assign path.output.index (checks.ingress (current.report.final.owner sender.other) sender.other)) :
    Nonempty (AckAssigned core path actual) := by
  obtain ⟨enabled, ⟨value⟩⟩ := ack_at core active phase finished path pending (by rw [← event]; exact allowed)
  have same := CampusTCPRoundPhaseBase.Step.eq_of_before_event enabled actual
    (value.value.move.beforeEq.trans before.symm) (value.value.facts.event.trans event.symm)
  exact ⟨same ▸ value⟩

end Netlib.Check.CampusTCPTwoTransferLocatedAssign
