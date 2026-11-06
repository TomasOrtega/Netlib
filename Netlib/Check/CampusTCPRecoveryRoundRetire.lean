import Netlib.Check.CampusTCPRecoveryRoundPhaseBase
import Netlib.Check.CampusTCPRecoveryRoundSender
import Netlib.Check.CampusTCPRecoveryRoundReceiver
import Netlib.Check.CampusTCPRoundDelivery

namespace Netlib.Check.CampusTCPRecoveryRoundRetire

open Protocol.TCP CampusTCPModel CampusTCPEnabled CampusTCPRoundStart
open CampusTCPRound (Cut)
open CampusTCPRoundPhaseBase (Move)

namespace Sender
export CampusTCPRecoveryRoundSender (Flight)
end Sender
namespace Receiver
export CampusTCPRecoveryRoundReceiver (Facts)
end Receiver

variable {input : Input} {events : List Event} {report : Report input events}
variable {complete : H.Completed input.active input.passive} {request : Request input}
variable {initial : Initial report complete request}

structure Retirement (retries : Nat) (state : Endpoint.State) where
  recovery : Recovery.State
  runtime : state.recovery = some recovery
  sent : state.core.sent = []
  cursor : state.core.sendUna = state.core.sendNext
  outstanding : recovery.outstanding = []
  deadline : recovery.deadline = none
  lastTimedOut : recovery.lastTimedOut = none
  timeoutCount : recovery.timeoutCount = 0
  valid : state.Valid
  coherent : Endpoint.RecoveryCoherent state
  prepared : Endpoint.AckPrepared state
  storage : Endpoint.StorageCoherent state
  karn : 0 < retries → recovery.rto = 2 ^ retries * 1000 ∧ recovery.estimator = none ∧ recovery.lastSample = none

def Retirement.clock (retired : Retirement retries state) (frame : Endpoint.ClockFrame state after)
    (timely : Endpoint.AckTimeReady state after.now) : Retirement retries after := by
  refine {
    recovery := { retired.recovery with now := after.now }
    runtime := frame.runtime retired.runtime
    sent := ?_, cursor := ?_, outstanding := retired.outstanding, deadline := retired.deadline
    lastTimedOut := retired.lastTimedOut, timeoutCount := retired.timeoutCount
    valid := frame.valid retired.valid, coherent := frame.recovery_coherent retired.coherent
    prepared := frame.ack_prepared retired.prepared timely, storage := frame.storage_coherent retired.storage
    karn := retired.karn }
  · rw [frame.core]; exact retired.sent
  · rw [frame.core]; exact retired.cursor

structure AckMove (initial : Initial report complete request) (current : Cut input complete) (retries : Nat)
    (index : Nat) (served : Served input)
    (emission : WireForwarding.Emission served.ticket.value.source.packet)
    (emitted : served.evidence.output = some emission) (actual : Step input) where
  move : Move current actual
  delivery : CampusTCPRoundDelivery.AckDelivered current.report complete current.endpoints index served emission emitted
  actualEq : delivery.step = actual
  sender : endpoint move.after.endpoints .client = delivery.after
  receiver : Receiver.Facts initial (endpoint move.after.endpoints .server) true
  retirement : Retirement retries (endpoint move.after.endpoints .client)
  accepted : delivery.localStep.result.decision = .accepted (.receive request.bytes.length 0)
  gateway : ∀ selected, beforeService input move.after.report.final selected = beforeService input current.report.final selected
  environment : CampusTCPRoundEnvironment.environment current.report.final =
    CampusTCPRoundEnvironment.environment move.after.report.final
  anchor : CampusTCPRecoveryRoundPhaseBase.Anchor initial move.after

theorem deliver_ack_at (initial : Initial report complete request) (current : Cut input complete)
    (anchor : CampusTCPRecoveryRoundPhaseBase.Anchor initial current) (sentAt retries : Nat)
    (flight : Sender.Flight initial sentAt (endpoint current.endpoints .client) retries)
    (receiver : Receiver.Facts initial (endpoint current.endpoints .server) true)
    (index : Nat) (served : Served input) (found : current.report.final.services[index]? = some served)
    (emission : WireForwarding.Emission served.ticket.value.source.packet) (emitted : served.evidence.output = some emission)
    (actor : served.ticket.value.produced.actor = .server)
    (application : CampusTCPDeliveryEnabled.ApplicationSource served.ticket.value.produced)
    (pending : CampusTCPDeliveryEnabled.LinkPending current.report.final index)
    (tuple : emission.asInput.packet.header = complete.certificate.activeSeed.core.inbound)
    (controls : EstablishedReceive.control emission.asInput.packet.segment = none)
    (ack : Flags.ack emission.asInput.packet.segment.flags = true)
    (sequence : emission.asInput.packet.segment.sequence = input.passive.iss.add 1)
    (acknowledgment : emission.asInput.packet.segment.acknowledgment = (input.active.iss.add 1).add request.bytes.length)
    (empty : emission.asInput.packet.segment.payload = []) :
    ∃ actual : Step input, Nonempty (AckMove initial current retries index served emission emitted actual) := by
  obtain ⟨reaction, ready⟩ := flight.full_ack_ready emission.asInput tuple controls ack sequence acknowledgment empty
  have selectedReady : CampusTCPDeliveryEnabled.FullAckReady
      (endpoint current.endpoints served.ticket.value.produced.actor.other) emission.asInput flight.recovery reaction := by
    simpa only [actor, Actor.other] using ready
  obtain ⟨delivery⟩ := CampusTCPRoundDelivery.Report.deliver_full_ack current.report complete current.endpoints
    current.connection index served found emission emitted application pending flight.recovery reaction selectedReady
  let next : Cut input complete := ⟨_, delivery.toDelivery.append current.supported current.finished,
    delivery.toDelivery.append_supported _ _, rfl, delivery.updated, delivery.connection⟩
  let move : Move current delivery.step := ⟨next, delivery.beforeEq, delivery.supported, delivery.passed, rfl, rfl⟩
  have sender : endpoint move.after.endpoints .client = delivery.after := by
    simpa only [actor, Actor.other] using delivery.selected
  have peer : endpoint move.after.endpoints .server = endpoint current.endpoints .server := by
    simpa only [actor, Actor.other] using delivery.peer
  obtain ⟨after, recovery, received, runtime, sent, cursor, valid, prepared, coherent, storage,
      outstanding, deadline, timedOut, count, karn⟩ :=
    flight.receive_full_ack emission.asInput tuple controls ack sequence acknowledgment empty
  have evaluated : delivery.localStep.result =
      ⟨after, .accepted (.receive request.bytes.length 0), none, [], none⟩ := by
    rw [delivery.localStep.computed, delivery.localBefore, delivery.localEvent]
    simpa only [ApplicationTrace.evaluate, actor, Actor.other] using received
  have afterEq : delivery.after = after := delivery.resultState.symm.trans (congrArg Endpoint.Result.state evaluated)
  have retired : Retirement retries (endpoint move.after.endpoints .client) := by
    rw [sender, afterEq]
    refine ⟨recovery, runtime, sent, ?_, outstanding, deadline, timedOut, count, valid, coherent, prepared, storage, ?_⟩
    · have bounded := valid.1.2.2.2.2.1
      simpa only [sent, List.length_nil, Seq.add_zero] using bounded
    · intro repeated
      obtain ⟨rto, estimator, sample⟩ := karn repeated
      exact ⟨rto.trans flight.rto, estimator, sample⟩
  have environment : CampusTCPRoundEnvironment.environment current.report.final =
      CampusTCPRoundEnvironment.environment move.after.report.final := delivery.environment
  refine ⟨delivery.step, ⟨⟨move, delivery, rfl, sender, ?_, retired,
    congrArg Endpoint.Result.decision evaluated, ?_, environment,
    ⟨CampusTCPRoundGuards.AckDelivered.guards delivery anchor.guards,
      anchor.retained.trans move.retained, anchor.environment.trans environment⟩⟩⟩⟩
  · rw [peer]; exact receiver
  · intro selected
    rw [move.final, CampusTCPRoundLocal.step_service_nonservice delivery.step (by rw [delivery.event]; trivial), delivery.beforeEq]

structure ReadMove (initial : Initial report complete request) (current : Cut input complete)
    (retries : Nat) (actual : Step input) where
  move : Move current actual
  event : actual.event = .read .server request.bytes.length
  operation : T.Step
  recorded : actual.result.application = some (.server, operation)
  localBefore : operation.before = endpoint current.endpoints .server
  localEvent : operation.event = .read request.bytes.length
  localStamp : operation.stamp = current.report.final.time
  accepted : operation.result.decision = .accepted (.read request.bytes.length)
  returned : actual.result.read = request.bytes
  localRead : operation.result.read = request.bytes
  selected : endpoint move.after.endpoints .server = Endpoint.readState (endpoint current.endpoints .server) request.bytes.length
  peer : endpoint move.after.endpoints .client = endpoint current.endpoints .client
  empty : (endpoint move.after.endpoints .server).core.received = []
  held : (endpoint move.after.endpoints .server).receiveStore.held = []
  retirement : Retirement retries (endpoint move.after.endpoints .client)
  gateway : ∀ selected, beforeService input move.after.report.final selected = beforeService input current.report.final selected
  environment : CampusTCPRoundEnvironment.environment current.report.final =
    CampusTCPRoundEnvironment.environment move.after.report.final
  anchor : CampusTCPRecoveryRoundPhaseBase.Anchor initial move.after

theorem read_at (initial : Initial report complete request) (current : Cut input complete)
    (anchor : CampusTCPRecoveryRoundPhaseBase.Anchor initial current) (retries : Nat)
    (retired : Retirement retries (endpoint current.endpoints .client))
    (receiver : Receiver.Facts initial (endpoint current.endpoints .server) true) :
    ∃ actual : Step input, Nonempty (ReadMove initial current retries actual) := by
  have payload : (endpoint current.endpoints .server).core.received = request.bytes := by simpa only [ite_true] using receiver.received
  have fits : request.bytes.length ≤ (endpoint current.endpoints .server).core.received.length := by rw [payload]; exact Nat.le_refl _
  have earlier := (CampusTCPChronology.Report.application_before current.report complete current.endpoints current.connection).2
  obtain ⟨effect, computed, supported, _, returned, application⟩ := read_enabled current.report.final complete
    current.endpoints current.connection .server request.bytes.length earlier fits
  let actual : Step input := ⟨_, _, effect, computed⟩
  let operation := ApplicationTrace.Step.make (endpoint current.endpoints .server) (endpoint_valid current.endpoints .server)
    (.read request.bytes.length) current.report.final.time
  have recorded : actual.result.application = some (.server, operation) := application
  obtain ⟨appended⟩ := current.appendLocal actual rfl supported .server (.read request.bytes.length)
    (.read request.bytes.length) operation recorded
  have passed := CampusTCPRoundLocal.step_local_passed actual .server (.read request.bytes.length) (.read _)
  let move : Move current actual := ⟨appended.next, rfl, supported, passed, appended.history, appended.final⟩
  have evaluated : operation.result =
      ⟨Endpoint.readState (endpoint current.endpoints .server) request.bytes.length,
        .accepted (.read request.bytes.length), none, request.bytes, none⟩ := by
    change Endpoint.read (endpoint current.endpoints .server) request.bytes.length = _
    simpa only [payload, List.take_length] using Endpoint.read_of_fits _ _ (endpoint_valid _ _) fits
  have selected : endpoint move.after.endpoints .server =
      Endpoint.readState (endpoint current.endpoints .server) request.bytes.length :=
    appended.selected.trans (congrArg Endpoint.Result.state evaluated)
  have peer : endpoint move.after.endpoints .client = endpoint current.endpoints .client := appended.peer
  have read : actual.result.read = request.bytes := by simpa only [payload, List.take_length] using returned
  have environment : CampusTCPRoundEnvironment.environment current.report.final =
      CampusTCPRoundEnvironment.environment move.after.report.final := by
    rw [move.final]
    exact CampusTCPRoundEnvironment.Step.environment actual trivial
  have guards : CampusTCPRoundGuards.Guards move.after.endpoints :=
    CampusTCPRoundGuards.guards_frame current.endpoints appended.next.endpoints .server
      (CampusTCPRoundGuards.read_step_guarded operation request.bytes.length rfl fits (anchor.guards .server))
      appended.selected appended.peer anchor.guards
  refine ⟨actual, ⟨⟨move, rfl, operation, recorded, rfl, rfl, rfl, congrArg Endpoint.Result.decision evaluated,
    read, congrArg Endpoint.Result.read evaluated, selected, peer, ?_, ?_, ?_, ?_, environment,
    ⟨guards, anchor.retained.trans move.retained, anchor.environment.trans environment⟩⟩⟩⟩
  · rw [selected]
    simp only [Endpoint.readState, payload, List.drop_length]
  · rw [selected]
    exact receiver.held
  · rw [peer]; exact retired
  · intro gateway
    rw [move.final]
    exact CampusTCPRoundLocal.step_service_nonservice actual trivial gateway

theorem Step.deliver_ack (actual : Step input) (initial : Initial report complete request) (current : Cut input complete)
    (anchor : CampusTCPRecoveryRoundPhaseBase.Anchor initial current) (sentAt retries : Nat)
    (flight : Sender.Flight initial sentAt (endpoint current.endpoints .client) retries)
    (receiver : Receiver.Facts initial (endpoint current.endpoints .server) true)
    (index : Nat) (served : Served input) (found : current.report.final.services[index]? = some served)
    (emission : WireForwarding.Emission served.ticket.value.source.packet) (emitted : served.evidence.output = some emission)
    (actor : served.ticket.value.produced.actor = .server)
    (application : CampusTCPDeliveryEnabled.ApplicationSource served.ticket.value.produced)
    (pending : CampusTCPDeliveryEnabled.LinkPending current.report.final index)
    (tuple : emission.asInput.packet.header = complete.certificate.activeSeed.core.inbound)
    (controls : EstablishedReceive.control emission.asInput.packet.segment = none)
    (ack : Flags.ack emission.asInput.packet.segment.flags = true)
    (sequence : emission.asInput.packet.segment.sequence = input.passive.iss.add 1)
    (acknowledgment : emission.asInput.packet.segment.acknowledgment = (input.active.iss.add 1).add request.bytes.length)
    (empty : emission.asInput.packet.segment.payload = [])
    (before : actual.before = current.report.final) (event : actual.event = .deliver index emission.bytes true) :
    Nonempty (AckMove initial current retries index served emission emitted actual) := by
  obtain ⟨enabled, ⟨facts⟩⟩ := deliver_ack_at initial current anchor sentAt retries flight receiver index served found
    emission emitted actor application pending tuple controls ack sequence acknowledgment empty
  have same := CampusTCPRoundPhaseBase.Step.eq_of_before_event enabled actual
    (facts.move.beforeEq.trans before.symm) (facts.actualEq.symm ▸ facts.delivery.event.trans event.symm)
  exact ⟨same ▸ facts⟩

theorem Step.read (actual : Step input) (initial : Initial report complete request) (current : Cut input complete)
    (anchor : CampusTCPRecoveryRoundPhaseBase.Anchor initial current) (retries : Nat)
    (retired : Retirement retries (endpoint current.endpoints .client))
    (receiver : Receiver.Facts initial (endpoint current.endpoints .server) true)
    (before : actual.before = current.report.final) (event : actual.event = .read .server request.bytes.length) :
    Nonempty (ReadMove initial current retries actual) := by
  obtain ⟨enabled, ⟨facts⟩⟩ := read_at initial current anchor retries retired receiver
  have same := CampusTCPRoundPhaseBase.Step.eq_of_before_event enabled actual
    (facts.move.beforeEq.trans before.symm) (facts.event.trans event.symm)
  exact ⟨same ▸ facts⟩

end Netlib.Check.CampusTCPRecoveryRoundRetire
