import Netlib.Check.CampusTCPTwoTransferPreparationState
import Netlib.Check.CampusTCPTwoProgressPhaseSend

/-!
# Actual original sends before and after transfer

Each send keeps the original selected writer and the complete loss suffix.
The current endpoint state enables the operation at its actual gateway location.
-/

namespace Netlib.Check.CampusTCPTwoTransferPreparationSend

open Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart
open CampusTCPTwoTransferNative (Checks Routing)
open CampusTCPTwoTransferLocatedCore (Core config)
open CampusTCPTwoTransferState (LiveAt)
open CampusTCPTwoTransferPreparationState (Written PendingUpper LowerPath)
open CampusTCPTwoProgressPhaseBase (OriginalTimes emitted)

namespace S
export CampusTCPTwoProgressSender (Part Original Stage Flight)
end S
namespace R
export CampusTCPTwoProgressReceiver (Stage Facts)
end R
namespace M
export CampusTCPTwoProgressMonitor (Monitor Lane Allowed observe observeSend)
end M
namespace W
export CampusTCPTwoTransferMonitor (Monitor Allowed observe)
end W
namespace F
export CampusTCPTwoProgressMonitorFacts (observe_action observe_send_lower observe_send_upper)
end F
namespace Send
export CampusTCPTwoProgressSend (SendFacts)
end Send
namespace O
export CampusTCPTwoProgressSourceHistory (Issued Originals)
end O
namespace P
export CampusTCPTwoProgressPaths (DataIngress)
end P

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current : Cut input complete} {sender : Actor} {gateway location : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {checks : Checks cut initial.gatewayState.session.entry} {routing : Routing cut gateway}
variable {quantum allowance : Nat} {reverseLower reverseUpper : List UInt8}
variable {monitor : W.Monitor} {actual : Step input} {count timeouts : Nat}
variable {sent next : S.Stage initial} {received : R.Stage} {part : S.Part}

local notation "cfg" => config initial checks routing quantum allowance reverseLower reverseUpper

abbrev ingressLane := CampusTCPTwoProgressPhaseSend.ingressLane

private theorem original_packet (facts : Send.SendFacts current sender count actual) (original : S.Original initial part)
    (same : original.operation = facts.localStep) : facts.packet = original.packet := by
  have present : facts.localStep.result.output = some original.packet := by rw [← same]; exact original.origin.actual
  exact Option.some.inj (facts.origin.actual.symm.trans present)

private theorem application_eq (actor : Actor) (first second : T.Step) (packet output : EstablishedReceive.Input)
    (origin : ApplicationTrace.OutputOrigin first packet) (other : ApplicationTrace.OutputOrigin second output)
    (sameStep : first = second) (samePacket : packet = output) :
    (Produced.application actor first packet origin : Produced input.active input.passive) =
      .application actor second output other := by cases sameStep; cases samePacket; rfl

private theorem original_production (facts : Send.SendFacts current sender count actual) (original : S.Original initial part)
    (same : original.operation = facts.localStep) :
    facts.produced = CampusTCPTwoProgressOriginalPath.source original := by
  have packet := original_packet facts original same
  rw [facts.production]
  exact application_eq sender facts.localStep original.operation facts.packet original.packet facts.origin original.origin same.symm packet

private theorem data_fields (live : LiveAt initial current location sent timeouts received) (original : S.Original initial part)
    (facts : Send.SendFacts current sender count actual) (same : original.operation = facts.localStep) :
    CampusTCPTwoProgressWire.DataFields initial (part.offset lower) (part.bytes lower upper) facts.produced := by
  have before : original.operation.before = endpoint current.endpoints sender := by rw [same]; exact facts.localBefore
  have transport := Endpoint.emit_transport _ _ _ original.encoded
  have production := original_production facts original same
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [production]
    change original.packet.packet.header = _
    rw [transport.1, before, live.senderFlight.inbound]
    exact initial.input_tuple sender
  · rw [production]
    exact original.sequence
  · rw [production]
    change original.packet.packet.segment.acknowledgment = _
    rw [transport.2.2.1, before]
    exact live.senderFlight.receiveNext
  · rw [production]
    exact original.payload
  · rw [production]
    exact (CampusTCPRoundLocal.emit_profile _ _ _ original.encoded).1
  · rw [production]
    change 1 < original.packet.packet.ip.packet.ttl.toNat
    rw [CampusTCPRoundLocal.emit_ttl _ _ _ original.encoded]
    decide
  · rw [production]
    exact Endpoint.emit_window_floor _ _ _ (by rw [before]; exact live.senderFlight.prepared.1)
      (by rw [before]; exact live.senderFlight.advertised) original.encoded

private def after_live (live : LiveAt initial current location sent timeouts received) (facts : Send.SendFacts current sender count actual)
    (flight : S.Flight initial (endpoint facts.move.after.endpoints sender) next timeouts) :
    LiveAt initial facts.move.after location next timeouts received := by
  let receiver : R.Facts initial (endpoint facts.move.after.endpoints sender.other) received := by
    rw [facts.peer]
    exact live.receiverFacts
  exact ⟨⟨⟨live.anchor.retained.trans facts.move.retained, fun selected => (live.anchor.policy selected).trans
    (CampusTCPRoundEnvironment.service_environment _ _ facts.environment selected)⟩,
    CampusTCPTwoProgressState.endpoint_guards flight receiver⟩, flight, receiver,
    live.gatewayState.reframe (facts.serviceFrame location), live.gatewayWindow, live.history.same facts.peerSteps⟩

private theorem send_recovery (facts : Send.SendFacts current sender count actual)
    (before : S.Flight initial (endpoint current.endpoints sender) sent timeouts)
    (after : S.Flight initial (endpoint facts.move.after.endpoints sender) next nextTimeouts) :
    after.recovery = Recovery.sent before.recovery count := by
  have runtime := after.runtime.symm.trans (congrArg (fun state : Endpoint.State => state.recovery) facts.sendState)
  change some after.recovery = (endpoint current.endpoints sender).recovery.map (fun recovery => Recovery.sent recovery count) at runtime
  rw [before.runtime, Option.map_some] at runtime
  exact Option.some.inj runtime

private theorem allowed_send (config : CampusTCPTwoTransferMonitor.Config) (state : State input) (monitor : W.Monitor)
    (actor : Actor) (count : Nat) (allowed : W.Allowed config state monitor (.send actor count true)) :
    CampusTCPTwoTransferMonitor.drainTicket state monitor = none ∧
      CampusTCPTwoTransferMonitor.controlDemand monitor = none ∧
      CampusTCPTwoExchangeMonitor.Allowed (config.at state) state monitor.exchange (.send actor count true) := by
  by_cases invalid : monitor.mode = .invalid
  · simp only [W.Allowed, CampusTCPTwoTransferMonitor.allowed, invalid, decide_true, ite_true, Bool.false_eq_true] at allowed
  · cases drain : CampusTCPTwoTransferMonitor.drainTicket state monitor with
    | some ticket => simp [W.Allowed, CampusTCPTwoTransferMonitor.allowed, invalid, drain,
        CampusTCPTwoTransferMonitor.drainServes] at allowed
    | none =>
      cases selected : CampusTCPTwoTransferMonitor.controlDemand monitor with
      | none => exact ⟨rfl, rfl, by simpa only [W.Allowed, CampusTCPTwoTransferMonitor.allowed, invalid,
          decide_false, Bool.false_eq_true, ite_false, drain, selected, CampusTCPTwoExchangeMonitor.Allowed] using allowed⟩
      | some kind =>
        cases kind <;> simp [W.Allowed, CampusTCPTwoTransferMonitor.allowed, invalid, drain, selected,
          CampusTCPTwoTransferMonitor.Control.serves] at allowed

private theorem output_lane (facts : Send.SendFacts current sender count actual)
    (actor : facts.produced.actor = sender) (lane : M.Lane) :
    CampusTCPTwoProgressMonitor.Lane.ofGap (CampusTCPGapProgressMonitor.observeOutput ((cfg).at current.report.final).forward.toConfig
      lane.toGap actual true .dataIngress) = ingressLane lane current.report.final.outputs.length facts.packetID := by
  have custody := facts.custody
  rw [facts.move.final] at custody
  have self : (sender == sender) = true := by cases sender <;> rfl
  have configSender : ((cfg).at current.report.final).forward.sender = sender := rfl
  simp only [CampusTCPGapProgressMonitor.observeOutput, facts.output, actor, configSender, ite_true, self, facts.move.beforeEq,
    custody, CampusTCPTwoProgressMonitor.Lane.toGap, CampusTCPTwoProgressMonitor.Lane.ofGap, ingressLane]
  rfl

def afterSend (monitor : W.Monitor) (forward : M.Monitor) : W.Monitor :=
  { monitor with exchange := { monitor.exchange with forward, slots := monitor.exchange.slots + 1 } }

private theorem observe_send (facts : Send.SendFacts current sender count actual)
    (phase : monitor.exchange.mode = .forward) (allowed : W.Allowed cfg current.report.final monitor actual.event)
    (forward : M.Monitor) (mode : forward.mode = .originals)
    (localStep : M.observe ((cfg).at current.report.final).forward monitor.exchange.forward actual = forward) :
    W.observe cfg monitor actual = afterSend monitor forward := by
  obtain ⟨drain, control, ordinary⟩ := allowed_send cfg current.report.final monitor sender count (by rw [← facts.event]; exact allowed)
  have checked : (actual.result.supported && actual.result.passed &&
      CampusTCPTwoExchangeMonitor.allowed ((cfg).at actual.before) actual.before monitor.exchange actual.event) = true := by
    rw [facts.move.supported, facts.move.passed, facts.move.beforeEq]
    simpa only [facts.event, Bool.true_and, CampusTCPTwoExchangeMonitor.Allowed] using ordinary
  have exchangeStep : CampusTCPTwoExchangeMonitor.observe ((cfg).at actual.before) monitor.exchange actual =
      { monitor.exchange with forward, slots := monitor.exchange.slots + 1 } := by
    rw [CampusTCPTwoExchangeMonitor.observe, ite_eq_left checked, facts.move.beforeEq]
    simp only [phase, localStep, mode]
    rw [show (CampusTCPTwoProgressMonitor.Mode.originals == .invalid) = false by rfl,
      show (CampusTCPTwoProgressMonitor.Mode.originals == .done) = false by rfl]
    simp only [Bool.false_eq_true, ite_false]
    change { monitor.exchange with
      forward := forward
      slots := monitor.exchange.slots + 1
      drops := (match actual.event with | .dropPacket id => monitor.exchange.drops ++ [id] | _ => monitor.exchange.drops)
      timeouts := (match actual.event with | .timeout _ true => monitor.exchange.timeouts + 1 | _ => monitor.exchange.timeouts) } = _
    rw [facts.event]
    simp only [phase]
  have checkedWhole : (actual.result.supported && actual.result.passed &&
      CampusTCPTwoTransferMonitor.allowed cfg actual.before monitor actual.event) = true := by
    rw [facts.move.supported, facts.move.passed, facts.move.beforeEq]
    exact allowed
  rw [W.observe, ite_eq_left checkedWhole, facts.move.beforeEq, drain, control]
  rw [CampusTCPTwoTransferMonitor.ordinary, exchangeStep]
  simp only [phase, reduceCtorEq, decide_false, Bool.false_eq_true, ite_false, afterSend]

private def ingress (facts : Send.SendFacts current sender (part.bytes lower upper).length actual)
    (actor : facts.produced.actor = sender) (application : CampusTCPDeliveryEnabled.ApplicationSource facts.produced)
    (fields : CampusTCPTwoProgressWire.DataFields initial (part.offset lower) (part.bytes lower upper) facts.produced)
    (lane : M.Lane) : P.DataIngress initial facts.move.after part
      (ingressLane lane current.report.final.outputs.length facts.packetID) where
  output := ⟨current.report.final.outputs.length, facts.produced, facts.source, actor, application, fields⟩
  packetID := facts.packetID
  custody := facts.custody
  phase := rfl
  outputRef := rfl
  packetRef := rfl

private def issued (facts : Send.SendFacts current sender (part.bytes lower upper).length actual)
    (original : S.Original initial part) (same : original.operation = facts.localStep)
    (writer : CampusTCPTwoProgressWriteHistory.History initial current (CampusTCPTwoProgressSourceHistory.beforeBytes lower part)) :
    O.Issued initial facts.move.after part original where
  sent := writer.sent facts (by rw [original_packet facts original same]; exact original.payload)
  operation := same.symm
  packet := original_packet facts original same

private def after_core (core : Core initial checks routing quantum allowance reverseLower reverseUpper current monitor location sent .empty)
    (facts : Send.SendFacts current sender count actual)
    (flight : S.Flight initial (endpoint facts.move.after.endpoints sender) next monitor.exchange.forward.retries)
    (space : CampusTCPTwoProgressSenderWindow.Reserved initial (endpoint facts.move.after.endpoints sender) next)
    (originals : O.Originals initial facts.move.after next) (times : OriginalTimes initial next)
    (writer : CampusTCPTwoProgressWriteHistory.History initial facts.move.after (emitted initial next))
    (oldZero : sent.retiredBytes = 0) (newZero : next.retiredBytes = 0)
    (primaryEmpty : current.report.final.outstanding .primary = 0) (forward : M.Monitor)
    (observed : W.observe cfg monitor actual = afterSend monitor forward)
    (counts : forward.retries = monitor.exchange.forward.retries) (drops : forward.drops = monitor.exchange.forward.drops) :
    Core initial checks routing quantum allowance reverseLower reverseUpper facts.move.after
      (W.observe cfg monitor actual) location next .empty := by
  have counter : (W.observe cfg monitor actual).exchange.forward.retries = monitor.exchange.forward.retries := by
    rw [observed]
    exact counts
  let raw := after_live core.live facts flight
  let live : LiveAt initial facts.move.after location next (W.observe cfg monitor actual).exchange.forward.retries .empty := {
    raw with senderFlight := counter.symm ▸ raw.senderFlight }
  have recovery := send_recovery facts core.live.senderFlight live.senderFlight
  have duplicate : live.senderFlight.recovery.duplicateAcks = core.live.senderFlight.recovery.duplicateAcks := by rw [recovery]; rfl
  exact {
    live
    senderWindow := space
    originals
    originalTimes := times
    writer
    losses := core.losses.append facts.move
      (by rw [CampusTCPTwoProgressLossHistory.isDrop, facts.event])
      (by rw [CampusTCPTwoExchangeLoss.isTimeoutOutput, facts.event])
      (by rw [observed]; exact drops) counter (by rw [observed]; rfl) (by rw [observed]; rfl)
    lossBound := by rw [observed]; exact drops ▸ core.lossBound
    primaryQueue := CampusTCPTwoTransferQueue.Closed.of_zero (by simpa only [State.outstanding, facts.work] using primaryEmpty)
    retired := by rw [newZero]; exact Nat.zero_le _
    gatewayAck := core.gatewayAck
    peerSettled := core.peerSettled
    peerWindow := core.peerWindow
    covered := by intro part impossible; cases part <;> cases impossible
    duplicates := duplicate ▸ core.duplicates
    emptyDuplicate := fun _ => duplicate ▸ core.emptyDuplicate rfl
    deadline := by rw [recovery]; exact RecoveryDeadline.sent _ _ core.deadline
    estimatorBeforeRetire := fun _ => by rw [recovery]; exact core.estimatorBeforeRetire oldZero
    rtoBeforeRetire := fun _ => by rw [recovery, counter]; exact core.rtoBeforeRetire oldZero
    rtoPending := fun _ => RTOEnvelope.of_power (by rw [recovery, counter]; exact core.rtoBeforeRetire oldZero) }

structure First (before : Written initial checks routing quantum allowance reverseLower reverseUpper current monitor location)
    (actual : Step input) where
  facts : Send.SendFacts current sender lower.length actual
  original : S.Original initial .lower
  sameStep : original.operation = facts.localStep
  production : facts.produced = CampusTCPTwoProgressOriginalPath.source original
  fields : CampusTCPTwoProgressWire.DataFields initial 0 lower facts.produced
  observed : W.observe cfg monitor actual = afterSend monitor
    { monitor.exchange.forward with lower := ingressLane monitor.exchange.forward.lower current.report.final.outputs.length facts.packetID }
  next : PendingUpper initial checks routing quantum allowance reverseLower reverseUpper facts.move.after
    (W.observe cfg monitor actual) location original
  book : next.core.losses.book = before.core.losses.book
  path : P.DataIngress initial facts.move.after .lower (W.observe cfg monitor actual).exchange.forward.lower
  pathSource : path.output.produced = CampusTCPTwoProgressOriginalPath.source original
  allowed : W.Allowed cfg current.report.final monitor actual.event

theorem first_at (before : Written initial checks routing quantum allowance reverseLower reverseUpper current monitor location)
    (allowed : W.Allowed cfg current.report.final monitor (.send sender lower.length true)) :
    ∃ actual, Nonempty (First before actual) := by
  obtain ⟨original, operation, _, ⟨flight⟩⟩ := before.core.live.senderFlight.first_send current.report.final.time
  obtain ⟨actual, ⟨facts⟩⟩ := CampusTCPTwoProgressSend.Report.send_enabled current sender lower.length
    before.first_send_ready before.core.live.senderFlight.prepared
  have same : original.operation = facts.localStep := by rw [operation, facts.made]
  have selected : endpoint facts.move.after.endpoints sender = original.operation.result.state :=
    facts.selected.trans (congrArg (fun step : T.Step => step.result.state) same.symm)
  have nextFlight : S.Flight initial (endpoint facts.move.after.endpoints sender) (.lower original) monitor.exchange.forward.retries := by
    rw [selected]
    exact flight
  have production := original_production facts original same
  have fields := data_fields before.core.live original facts same
  have currentAllowed : W.Allowed cfg current.report.final monitor actual.event := by rw [facts.event]; exact allowed
  have ordinary := (allowed_send cfg current.report.final monitor sender lower.length allowed).2.2
  have localAllowed : M.Allowed ((cfg).at current.report.final).forward current.report.final monitor.exchange.forward actual.event := by
    simpa only [CampusTCPTwoExchangeMonitor.Allowed, CampusTCPTwoExchangeMonitor.allowed, before.exchange,
      M.Allowed, facts.event] using ordinary
  let forward : M.Monitor := { monitor.exchange.forward with
    lower := ingressLane monitor.exchange.forward.lower current.report.final.outputs.length facts.packetID }
  have localStep : M.observe ((cfg).at current.report.final).forward monitor.exchange.forward actual = forward := by
    rw [F.observe_action _ _ _ facts.move.supported facts.move.passed
      (by rw [facts.move.beforeEq]; exact localAllowed) (.send sender lower.length true) facts.event,
      F.observe_send_lower _ _ _ before.mode before.lowerPending]
    have output := output_lane (initial := initial) (checks := checks) (routing := routing) (quantum := quantum)
      (allowance := allowance) (reverseLower := reverseLower) (reverseUpper := reverseUpper)
      facts (by rw [production]; rfl) monitor.exchange.forward.lower
    simp only [M.observeSend, output, ingressLane]
    rfl
  have observed := observe_send facts before.exchange currentAllowed forward before.mode localStep
  have payload : facts.packet.packet.segment.payload = lower := by
    rw [original_packet facts original same]
    exact original.payload
  have reserve : CampusTCPTwoProgressSenderWindow.Reserved initial (endpoint facts.move.after.endpoints sender) (.lower original) := by
    apply CampusTCPTwoProgressSenderWindow.congr before.core.senderWindow
    · rw [facts.sendState]
      rfl
    · exact Nat.le_refl _
  have primaryEmpty : current.report.final.outstanding .primary = 0 := by
    apply before.core.primaryQueue.no_tickets_zero (CampusTCPOrigins.Report.work_valid current.report)
    · rw [before.lowerPending]; decide
    · rw [before.upperPending]; decide
  let originalIssued : O.Originals initial facts.move.after (.lower original) :=
    issued (initial := initial) (part := .lower) facts original same before.core.writer
  let nextCore := after_core before.core facts nextFlight reserve originalIssued
    (by change (endpoint cut.endpoints sender).now ≤ original.operation.before.now
        rw [same, facts.localBefore]; exact before.core.live.senderFlight.monotone)
    (by simpa only [emitted, List.nil_append] using before.core.writer.send facts payload)
    rfl rfl primaryEmpty forward observed rfl rfl
  let rawPath := ingress (initial := initial) (part := .lower) facts
    (by rw [production]; rfl) (by rw [production]; trivial) fields monitor.exchange.forward.lower
  let path : P.DataIngress initial facts.move.after .lower (W.observe cfg monitor actual).exchange.forward.lower :=
    rawPath.reindex (by rw [observed]; rfl)
  let next : PendingUpper initial checks routing quantum allowance reverseLower reverseUpper facts.move.after
      (W.observe cfg monitor actual) location original := {
    core := nextCore
    exchange := by rw [observed]; exact before.exchange
    mode := by rw [observed]; exact before.mode
    lowerPath := .ingress path production
    upperPending := by rw [observed]; exact before.upperPending
    ack := by rw [observed]; exact before.ack
    waiting := by rw [observed]; exact before.waiting
    retry := by rw [observed]; exact before.retry
    retries := by rw [observed]; exact before.retries
    sources := before.sources.non_delivery facts.move (by rw [facts.event]; trivial) }
  exact ⟨actual, ⟨⟨facts, original, same, production, fields, observed, next, rfl, path, production, currentAllowed⟩⟩⟩

variable {first : S.Original initial .lower}

structure Second (before : PendingUpper initial checks routing quantum allowance reverseLower reverseUpper current monitor location first)
    (actual : Step input) where
  facts : Send.SendFacts current sender upper.length actual
  original : S.Original initial .upper
  sameStep : original.operation = facts.localStep
  production : facts.produced = CampusTCPTwoProgressOriginalPath.source original
  fields : CampusTCPTwoProgressWire.DataFields initial lower.length upper facts.produced
  observed : W.observe cfg monitor actual = afterSend monitor
    { monitor.exchange.forward with upper := ingressLane monitor.exchange.forward.upper current.report.final.outputs.length facts.packetID }
  next : Core initial checks routing quantum allowance reverseLower reverseUpper facts.move.after
    (W.observe cfg monitor actual) location (.both first original first.entry) .empty
  book : next.losses.book = before.core.losses.book
  lowerPath : LowerPath initial facts.move.after first (W.observe cfg monitor actual).exchange.forward.lower next.losses.book
  path : P.DataIngress initial facts.move.after .upper (W.observe cfg monitor actual).exchange.forward.upper
  pathSource : path.output.produced = CampusTCPTwoProgressOriginalPath.source original
  sources : CampusTCPTwoProgressReceiptSources.History initial facts.move.after
  allowed : W.Allowed cfg current.report.final monitor actual.event

theorem second_at (before : PendingUpper initial checks routing quantum allowance reverseLower reverseUpper current monitor location first)
    (allowed : W.Allowed cfg current.report.final monitor (.send sender upper.length true)) :
    ∃ actual, Nonempty (Second before actual) := by
  obtain ⟨original, operation, _, ⟨flight⟩⟩ := before.core.live.senderFlight.second_send current.report.final.time
  obtain ⟨actual, ⟨facts⟩⟩ := CampusTCPTwoProgressSend.Report.send_enabled current sender upper.length
    before.second_send_ready before.core.live.senderFlight.prepared
  have same : original.operation = facts.localStep := by rw [operation, facts.made]
  have selected : endpoint facts.move.after.endpoints sender = original.operation.result.state :=
    facts.selected.trans (congrArg (fun step : T.Step => step.result.state) same.symm)
  have nextFlight : S.Flight initial (endpoint facts.move.after.endpoints sender) (.both first original first.entry)
      monitor.exchange.forward.retries := by
    rw [selected]
    exact flight
  have production := original_production facts original same
  have fields := data_fields before.core.live original facts same
  have currentAllowed : W.Allowed cfg current.report.final monitor actual.event := by rw [facts.event]; exact allowed
  have ordinary := (allowed_send cfg current.report.final monitor sender upper.length allowed).2.2
  have localAllowed : M.Allowed ((cfg).at current.report.final).forward current.report.final monitor.exchange.forward actual.event := by
    simpa only [CampusTCPTwoExchangeMonitor.Allowed, CampusTCPTwoExchangeMonitor.allowed, before.exchange,
      M.Allowed, facts.event] using ordinary
  let forward : M.Monitor := { monitor.exchange.forward with
    upper := ingressLane monitor.exchange.forward.upper current.report.final.outputs.length facts.packetID }
  have lowerPending : monitor.exchange.forward.lower.phase ≠ .needSend := by
    rcases before.lowerPath.phase with phase | phase <;> rw [phase] <;> decide
  have localStep : M.observe ((cfg).at current.report.final).forward monitor.exchange.forward actual = forward := by
    rw [F.observe_action _ _ _ facts.move.supported facts.move.passed
      (by rw [facts.move.beforeEq]; exact localAllowed) (.send sender upper.length true) facts.event,
      F.observe_send_upper _ _ _ before.mode lowerPending before.upperPending]
    have output := output_lane (initial := initial) (checks := checks) (routing := routing) (quantum := quantum)
      (allowance := allowance) (reverseLower := reverseLower) (reverseUpper := reverseUpper)
      facts (by rw [production]; rfl) monitor.exchange.forward.upper
    simp only [M.observeSend, output, ingressLane]
    rfl
  have observed := observe_send facts before.exchange currentAllowed forward before.mode localStep
  have payload : facts.packet.packet.segment.payload = upper := by
    rw [original_packet facts original same]
    exact original.payload
  have reserve : CampusTCPTwoProgressSenderWindow.Reserved initial (endpoint facts.move.after.endpoints sender)
      (.both first original first.entry) := by
    apply CampusTCPTwoProgressSenderWindow.congr before.core.senderWindow
    · rw [facts.sendState]
      rfl
    · exact Nat.le_refl _
  let firstIssued : O.Issued initial facts.move.after .lower first := before.issued.retain_steps facts.move.retained
  let upperIssued := issued (initial := initial) (part := .upper) facts original same before.core.writer
  let nextCore := after_core before.core facts nextFlight reserve ⟨firstIssued, upperIssued⟩
    ⟨before.core.originalTimes, by rw [same, facts.localBefore]; exact before.core.live.senderFlight.monotone⟩
    (before.core.writer.send facts payload) rfl rfl before.primary_empty forward observed rfl rfl
  have book : nextCore.losses.book = before.core.losses.book := rfl
  have lowerPath : LowerPath initial facts.move.after first (W.observe cfg monitor actual).exchange.forward.lower nextCore.losses.book := by
    cases before.lowerPath with
    | ingress path source =>
      exact .ingress ((CampusTCPTwoProgressPhaseSend.SendFacts.retain_ingress facts path).reindex (by rw [observed]; rfl)) source
    | lost phase position loss found source cause =>
      refine .lost (by rw [observed]; exact phase) position loss ?_ source ?_
      · rw [book]
        exact found
      · rw [book]
        exact cause
  let rawPath := ingress (initial := initial) (part := .upper) facts
    (by rw [production]; rfl) (by rw [production]; trivial) fields monitor.exchange.forward.upper
  let path : P.DataIngress initial facts.move.after .upper (W.observe cfg monitor actual).exchange.forward.upper :=
    rawPath.reindex (by rw [observed]; rfl)
  exact ⟨actual, ⟨⟨facts, original, same, production, fields, observed, nextCore, book, lowerPath, path, production,
    before.sources.non_delivery facts.move (by rw [facts.event]; trivial), currentAllowed⟩⟩⟩

theorem Step.first_send (before : Written initial checks routing quantum allowance reverseLower reverseUpper current monitor location)
    (allowed : W.Allowed cfg current.report.final monitor (.send sender lower.length true)) (actual : Step input)
    (atCurrent : actual.before = current.report.final) (event : actual.event = .send sender lower.length true) :
    Nonempty (First before actual) := by
  obtain ⟨enabled, ⟨value⟩⟩ := first_at before allowed
  have same := CampusTCPRoundPhaseBase.Step.eq_of_before_event enabled actual
    (value.facts.move.beforeEq.trans atCurrent.symm) (value.facts.event.trans event.symm)
  exact ⟨same ▸ value⟩

theorem Step.second_send (before : PendingUpper initial checks routing quantum allowance reverseLower reverseUpper current monitor location first)
    (allowed : W.Allowed cfg current.report.final monitor (.send sender upper.length true)) (actual : Step input)
    (atCurrent : actual.before = current.report.final) (event : actual.event = .send sender upper.length true) :
    Nonempty (Second before actual) := by
  obtain ⟨enabled, ⟨value⟩⟩ := second_at before allowed
  have same := CampusTCPRoundPhaseBase.Step.eq_of_before_event enabled actual
    (value.facts.move.beforeEq.trans atCurrent.symm) (value.facts.event.trans event.symm)
  exact ⟨same ▸ value⟩

end Netlib.Check.CampusTCPTwoTransferPreparationSend
