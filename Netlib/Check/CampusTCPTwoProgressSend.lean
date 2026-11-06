import Netlib.Check.CampusTCPTwoProgressState
import Netlib.Check.CampusTCPTwoProgressWire
import Netlib.Check.CampusTCPTwoProgressSenderWindow
import Netlib.Check.CampusTCPRoundMonitorFacts
import Netlib.Check.CampusTCPTimedTimeout

/-!
# Actual original sends for the two-record task

The local original and campus output cite the same evaluated operation.
The retained suffix supplies its selected write ancestry separately.
-/

namespace Netlib.Check.CampusTCPTwoProgressSend

open Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPGapProgressPhaseBase (Move)
open CampusTCPTwoProgressStart (TwoWriteInitial)
open CampusTCPTwoProgressState (Live)

namespace S
export CampusTCPTwoProgressSender (Part Original Stage Flight)
end S
namespace R
export CampusTCPTwoProgressReceiver (Stage Facts)
end R
namespace W
export CampusTCPTwoProgressWire (DataFields)
end W
namespace V
export CampusTCPTwoProgressSenderWindow (Reserved)
end V

variable {input : Input} {complete : H.Completed input.active input.passive}
  {cut current : Cut input complete} {sender actor : Actor} {gateway : Gateway} {lower upper : List UInt8}
  {initial : TwoWriteInitial cut sender gateway lower upper}

structure SendFacts (current : Cut input complete) (actor : Actor) (count : Nat) (actual : Step input) where
  move : Move current actual
  event : actual.event = .send actor count true
  localStep : T.Step
  made : localStep = ApplicationTrace.Step.make (endpoint current.endpoints actor) (endpoint_valid current.endpoints actor)
    (.send count true) current.report.final.time
  application : actual.result.application = some (actor, localStep)
  accepted : localStep.result.decision = .accepted (.send count)
  packet : EstablishedReceive.Input
  origin : ApplicationTrace.OutputOrigin localStep packet
  produced : Produced input.active input.passive
  output : actual.result.output = some produced
  production : produced = .application actor localStep packet origin
  encoded : Endpoint.emit (endpoint current.endpoints actor)
    ((endpoint current.endpoints actor).pending.take count) = .ok packet
  localBefore : localStep.before = endpoint current.endpoints actor
  localEvent : localStep.event = .send count true
  localStamp : localStep.stamp = current.report.final.time
  localState : localStep.result.state = Endpoint.sendState (endpoint current.endpoints actor) count
  selected : endpoint move.after.endpoints actor = localStep.result.state
  peer : endpoint move.after.endpoints actor.other = endpoint current.endpoints actor.other
  selectedSteps : applicationSteps move.after.endpoints actor = applicationSteps current.endpoints actor ++ [localStep]
  peerSteps : applicationSteps move.after.endpoints actor.other = applicationSteps current.endpoints actor.other
  serviceFrame : ∀ selected, beforeService input move.after.report.final selected = beforeService input current.report.final selected
  environment : CampusTCPRoundEnvironment.environment current.report.final =
    CampusTCPRoundEnvironment.environment move.after.report.final
  work : move.after.report.final.work = current.report.final.work
  services : move.after.report.final.services = current.report.final.services
  receipts : move.after.report.final.receipts = current.report.final.receipts
  source : move.after.report.final.outputs[current.report.final.outputs.length]? = some produced
  pending : IngressPending move.after.report.final current.report.final.outputs.length
  minted : ∃ item ∈ move.after.report.final.custody.pending,
    item.value.parent = none ∧ item.value.payload = .ingress current.report.final.outputs.length produced
  packetID : Nat
  custody : move.after.report.final.custody.pendingID (Transit.ingressAt current.report.final.outputs.length) = some packetID

theorem Report.send_enabled (current : Cut input complete) (actor : Actor) (count : Nat)
    (ready : Endpoint.SendReady (endpoint current.endpoints actor) count)
    (prepared : Endpoint.AckPrepared (endpoint current.endpoints actor)) :
    ∃ actual : Step input, Nonempty (SendFacts current actor count actual) := by
  have chronology := CampusTCPChronology.Report.application_before current.report complete current.endpoints current.connection
  have earlier : ∀ old ∈ applicationSteps current.endpoints actor, old.stamp < current.report.final.time := by
    cases actor
    · exact chronology.1
    · exact chronology.2
  obtain ⟨effect, produced, computed, supported, output, _, payload, application⟩ :=
    CampusTCPEnabled.send_enabled current.report.final complete current.endpoints current.connection actor count earlier ready prepared
  let actual : Step input := ⟨current.report.final, .send actor count true, effect, computed⟩
  let localStep := ApplicationTrace.Step.make (endpoint current.endpoints actor) (endpoint_valid current.endpoints actor)
    (.send count true) current.report.final.time
  have recorded : actual.result.application = some (actor, localStep) := application
  have emitted : actual.result.output = some produced := output
  obtain ⟨packet, origin, production⟩ := CampusTCPRoundLocal.step_application_output actual complete current.endpoints
    current.connection actor (.send count true) (.send count true) localStep recorded produced emitted
  obtain ⟨wire, result⟩ := Endpoint.send_success_enabled (endpoint current.endpoints actor) count
    (endpoint_valid current.endpoints actor) ready prepared
  have accepted : localStep.result.decision = .accepted (.send count) := by
    change (Endpoint.send (endpoint current.endpoints actor) count true).decision = _
    rw [result]
  have localState : localStep.result.state = Endpoint.sendState (endpoint current.endpoints actor) count := by
    change (Endpoint.send (endpoint current.endpoints actor) count true).state = _
    rw [result]
  have noRetry : ApplicationTrace.NoRetry localStep := by intro policy event; cases event
  obtain ⟨bytes, encodedBytes⟩ := CampusTCPRoundLocal.original_encoded origin noRetry
  have packetPayload : packet.packet.segment.payload = (endpoint current.endpoints actor).pending.take count := by
    simpa only [production, Produced.output] using payload
  have sameBytes : bytes = (endpoint current.endpoints actor).pending.take count :=
    (Endpoint.emit_payload _ _ _ encodedBytes).symm.trans packetPayload
  have encoded : Endpoint.emit (endpoint current.endpoints actor)
      ((endpoint current.endpoints actor).pending.take count) = .ok packet := by
    simpa only [localStep, ApplicationTrace.Step.make, sameBytes] using encodedBytes
  obtain ⟨after, connected, selected, peer, selectedSteps, peerSteps, localBefore, localEvent, localStamp⟩ :=
    CampusTCPEnabled.Step.application_frame actual complete current.endpoints current.connection actor (.send count true)
      (.send count true) localStep recorded
  let report := CampusTCPSchedule.Report.appendStep current.report current.supported current.finished actual rfl supported
  let next : Cut input complete := ⟨_, report, CampusTCPSchedule.Report.appendStep_supported _ _ _ _ _ _, rfl, after, connected⟩
  have passed : actual.result.passed = true := CampusTCPRoundLocal.step_local_passed actual actor (.send count true) (.send count true)
  let move : Move current actual := ⟨next, rfl, supported, passed, rfl, rfl⟩
  have serviceFrame : ∀ selected, beforeService input move.after.report.final selected =
      beforeService input current.report.final selected := by
    intro selected
    exact CampusTCPRoundLocal.step_service_nonservice actual trivial selected
  have environment : CampusTCPRoundEnvironment.environment current.report.final =
      CampusTCPRoundEnvironment.environment move.after.report.final :=
    CampusTCPRoundEnvironment.Step.environment actual trivial
  have stateFrames : actual.result.state.work = current.report.final.work ∧
      actual.result.state.services = current.report.final.services ∧ actual.result.state.receipts = current.report.final.receipts := by
    obtain ⟨coreEffect, custody, core, final⟩ := actual.processed
    have frames := CampusTCPTimedTimeout.application_frames actual.before actor (.send count true) coreEffect core
    simpa only [final] using frames
  have source : move.after.report.final.outputs[current.report.final.outputs.length]? = some produced := by
    change actual.result.state.outputs[current.report.final.outputs.length]? = some produced
    rw [CampusTCPOrigins.output_history actual, emitted]
    change (current.report.final.outputs ++ [produced])[current.report.final.outputs.length]? = some produced
    simp
  obtain ⟨item, member, parent, minted⟩ := CampusTCPCustodyFacts.Step.output_packet actual produced emitted
  have pending : IngressPending move.after.report.final current.report.final.outputs.length := by
    refine ⟨item, member, ?_⟩
    rw [minted]
    change (current.report.final.outputs.length == current.report.final.outputs.length) = true
    exact beq_self_eq_true _
  obtain ⟨id, custody⟩ := CampusTCPRoundMonitorFacts.output_pending actual produced emitted
  exact ⟨actual, ⟨⟨move, rfl, localStep, rfl, recorded, accepted, packet, origin, produced, emitted, production,
    encoded, localBefore, localEvent, localStamp, localState, selected, peer, selectedSteps, peerSteps,
    serviceFrame, environment, stateFrames.1, stateFrames.2.1, stateFrames.2.2, source, pending,
    ⟨item, member, parent, minted⟩, id, custody⟩⟩⟩

variable {count : Nat} {actual : Step input}

def SendFacts.attempt (facts : SendFacts current actor count actual) :
    ApplicationTrace.OutputAt (applicationSteps facts.move.after.endpoints actor) :=
  ⟨applicationSteps current.endpoints actor, facts.localStep, [], facts.selectedSteps, facts.packet, facts.origin⟩

theorem SendFacts.local_member (facts : SendFacts current actor count actual) :
    facts.localStep ∈ applicationSteps facts.move.after.endpoints actor := facts.attempt.member

theorem SendFacts.sendState (facts : SendFacts current actor count actual) :
    endpoint facts.move.after.endpoints actor = Endpoint.sendState (endpoint current.endpoints actor) count :=
  facts.selected.trans facts.localState

variable {sent : S.Stage initial} {timeouts : Nat} {received : R.Stage}

private theorem original_packet (facts : SendFacts current sender count actual) (original : S.Original initial part)
    (same : original.operation = facts.localStep) : facts.packet = original.packet := by
  have present : facts.localStep.result.output = some original.packet := by
    rw [← same]
    exact original.origin.actual
  exact Option.some.inj (facts.origin.actual.symm.trans present)

private theorem application_eq (actor : Actor) (first second : T.Step) (packet output : EstablishedReceive.Input)
    (origin : ApplicationTrace.OutputOrigin first packet) (other : ApplicationTrace.OutputOrigin second output)
    (sameStep : first = second) (samePacket : packet = output) :
    (Produced.application actor first packet origin : Produced input.active input.passive) =
      .application actor second output other := by
  cases sameStep
  cases samePacket
  rfl

private theorem original_production (facts : SendFacts current sender count actual) (original : S.Original initial part)
    (same : original.operation = facts.localStep) :
    facts.produced = .application sender original.operation original.packet original.origin := by
  have packet := original_packet facts original same
  rw [facts.production]
  exact application_eq sender facts.localStep original.operation facts.packet original.packet facts.origin original.origin same.symm packet

private theorem data_fields (live : Live initial current sent timeouts received) (original : S.Original initial part)
    (facts : SendFacts current sender count actual) (same : original.operation = facts.localStep) :
    W.DataFields initial (part.offset lower) (part.bytes lower upper) facts.produced := by
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

private def after_live (live : Live initial current sent timeouts received) (facts : SendFacts current sender count actual)
    (flight : S.Flight initial (endpoint facts.move.after.endpoints sender) next timeouts) :
    Live initial facts.move.after next timeouts received := by
  let receiver : R.Facts initial (endpoint facts.move.after.endpoints sender.other) received := by
    rw [facts.peer]
    exact live.receiverFacts
  exact ⟨⟨CampusTCPTwoProgressState.endpoint_guards flight receiver, live.anchor.retained.trans facts.move.retained,
    live.anchor.environment.trans facts.environment⟩, flight, receiver,
    live.gatewayState.reframe (facts.serviceFrame gateway), live.gatewayWindow, live.history.same facts.peerSteps⟩

private theorem after_reserve (space : V.Reserved initial (endpoint current.endpoints sender) sent)
    (facts : SendFacts current sender count actual) (retired : sent.retiredBytes ≤ next.retiredBytes) :
    V.Reserved initial (endpoint facts.move.after.endpoints sender) next := by
  apply CampusTCPTwoProgressSenderWindow.congr space (next := next)
  · rw [facts.sendState]
    rfl
  · exact retired

structure FirstSent (_live : Live initial current .written timeouts received) (actual : Step input) where
  facts : SendFacts current sender lower.length actual
  original : S.Original initial .lower
  sameStep : original.operation = facts.localStep
  production : facts.produced = .application sender original.operation original.packet original.origin
  fields : W.DataFields initial 0 lower facts.produced
  next : Live initial facts.move.after (.lower original) timeouts received
  reserve : V.Reserved initial (endpoint facts.move.after.endpoints sender) (.lower original)

structure SecondSent (_live : Live initial current (.lower first) timeouts received) (actual : Step input) where
  facts : SendFacts current sender upper.length actual
  original : S.Original initial .upper
  sameStep : original.operation = facts.localStep
  production : facts.produced = .application sender original.operation original.packet original.origin
  fields : W.DataFields initial lower.length upper facts.produced
  next : Live initial facts.move.after (.both first original first.entry) timeouts received
  reserve : V.Reserved initial (endpoint facts.move.after.endpoints sender) (.both first original first.entry)

theorem first_at (live : Live initial current .written timeouts received)
    (space : V.Reserved initial (endpoint current.endpoints sender) .written) :
    ∃ actual : Step input, Nonempty (FirstSent live actual) := by
  obtain ⟨first, operation, result, ⟨flight⟩⟩ := live.senderFlight.first_send current.report.final.time
  obtain ⟨actual, ⟨facts⟩⟩ := Report.send_enabled current sender lower.length
    live.senderFlight.first_send_ready live.senderFlight.prepared
  have same : first.operation = facts.localStep := by rw [operation, facts.made]
  have selected : endpoint facts.move.after.endpoints sender = first.operation.result.state :=
    facts.selected.trans (congrArg (fun step : T.Step => step.result.state) same.symm)
  have nextFlight : S.Flight initial (endpoint facts.move.after.endpoints sender) (.lower first) timeouts := by
    rw [selected]
    exact flight
  exact ⟨actual, ⟨⟨facts, first, same, original_production facts first same,
    data_fields live first facts same, after_live live facts nextFlight, after_reserve space facts (Nat.le_refl _)⟩⟩⟩

theorem second_at (live : Live initial current (.lower first) timeouts received)
    (space : V.Reserved initial (endpoint current.endpoints sender) (.lower first)) :
    ∃ actual : Step input, Nonempty (SecondSent live actual) := by
  obtain ⟨second, operation, result, ⟨flight⟩⟩ := live.senderFlight.second_send current.report.final.time
  obtain ⟨actual, ⟨facts⟩⟩ := Report.send_enabled current sender upper.length
    live.senderFlight.second_send_ready live.senderFlight.prepared
  have same : second.operation = facts.localStep := by rw [operation, facts.made]
  have selected : endpoint facts.move.after.endpoints sender = second.operation.result.state :=
    facts.selected.trans (congrArg (fun step : T.Step => step.result.state) same.symm)
  have nextFlight : S.Flight initial (endpoint facts.move.after.endpoints sender) (.both first second first.entry) timeouts := by
    rw [selected]
    exact flight
  exact ⟨actual, ⟨⟨facts, second, same, original_production facts second same,
    data_fields live second facts same, after_live live facts nextFlight, after_reserve space facts (Nat.le_refl _)⟩⟩⟩

def FirstSent.attempt {live : Live initial current .written timeouts received} (value : FirstSent live actual) :
    ApplicationTrace.OutputAt (applicationSteps value.facts.move.after.endpoints sender) :=
  ⟨applicationSteps current.endpoints sender, value.original.operation, [],
    by rw [value.sameStep]; exact value.facts.selectedSteps, value.original.packet, value.original.origin⟩

def SecondSent.attempt {first : S.Original initial .lower}
    {live : Live initial current (.lower first) timeouts received} (value : SecondSent live actual) :
    ApplicationTrace.OutputAt (applicationSteps value.facts.move.after.endpoints sender) :=
  ⟨applicationSteps current.endpoints sender, value.original.operation, [],
    by rw [value.sameStep]; exact value.facts.selectedSteps, value.original.packet, value.original.origin⟩

theorem Step.first (actual : Step input) (live : Live initial current .written timeouts received)
    (space : V.Reserved initial (endpoint current.endpoints sender) .written)
    (before : actual.before = current.report.final) (event : actual.event = .send sender lower.length true) :
    Nonempty (FirstSent live actual) := by
  obtain ⟨enabled, ⟨facts⟩⟩ := first_at live space
  have same := CampusTCPRoundPhaseBase.Step.eq_of_before_event enabled actual
    (facts.facts.move.beforeEq.trans before.symm) (facts.facts.event.trans event.symm)
  exact ⟨same ▸ facts⟩

theorem Step.second {first : S.Original initial .lower} (actual : Step input) (live : Live initial current (.lower first) timeouts received)
    (space : V.Reserved initial (endpoint current.endpoints sender) (.lower first))
    (before : actual.before = current.report.final) (event : actual.event = .send sender upper.length true) :
    Nonempty (SecondSent live actual) := by
  obtain ⟨enabled, ⟨facts⟩⟩ := second_at live space
  have same := CampusTCPRoundPhaseBase.Step.eq_of_before_event enabled actual
    (facts.facts.move.beforeEq.trans before.symm) (facts.facts.event.trans event.symm)
  exact ⟨same ▸ facts⟩

end Netlib.Check.CampusTCPTwoProgressSend
