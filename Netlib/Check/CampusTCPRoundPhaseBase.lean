import Netlib.Check.CampusTCPRound
import Netlib.Check.CampusTCPRoundMonitor
import Netlib.Check.CampusTCPRoundStutter
import Netlib.Check.CampusTCPRoundEndpointGuards

/-!
# Actual phase records and their current cuts

Past packet operations keep their original states and stamps.
Each current cut can extend its last packet operation through clock slots.
-/

namespace Netlib.Check.CampusTCPRoundPhaseBase

open Protocol.TCP CampusTCPModel CampusTCPEnabled CampusTCPRoundStart
open CampusTCPRound (Cut)
open CampusTCPRoundMonitor CampusTCPRoundGuards

abbrev MonitorConfig := CampusTCPRoundMonitor.Config
abbrev MonitorAction := CampusTCPRoundMonitor.Action

variable {input : Input} {events : List Event} {report : Report input events}
variable {complete : H.Completed input.active input.passive} {request : Request input}
variable {initial : Initial report complete request} {native : NativeEnv initial}

def config (initial : Initial report complete request) (native : NativeEnv initial) : MonitorConfig :=
  ⟨request.bytes, native.dataIngress, native.ackIngress⟩

structure At (anchor current : Cut input complete) : Prop where
  retained : anchor.report.steps <+: current.report.steps
  frame : CampusTCPRoundStutter.Frame anchor.report.final anchor.endpoints current.report.final current.endpoints
  clocks : ∃ extra, current.report.steps = anchor.report.steps ++ extra ∧
    ∀ actual ∈ extra, ∃ actor now, actual.event = .advanceClock actor now

theorem At.refl (cut : Cut input complete) : At cut cut :=
  ⟨List.prefix_refl _, CampusTCPRoundStutter.Frame.refl _ _ cut.connection,
    [], by simp, by simp⟩

theorem At.trans (first : At left middle) (second : At middle right) : At left right :=
  ⟨first.retained.trans second.retained, first.frame.trans second.frame, by
    obtain ⟨before, earlier, firstClocks⟩ := first.clocks
    obtain ⟨after, later, lastClocks⟩ := second.clocks
    refine ⟨before ++ after, ?_, ?_⟩
    · rw [later, earlier, List.append_assoc]
    · intro actual member
      rcases List.mem_append.mp member with old | next
      · exact firstClocks actual old
      · exact lastClocks actual next⟩

theorem At.member (placement : At anchor current) (member : actual ∈ anchor.report.steps) : actual ∈ current.report.steps :=
  placement.retained.subset member

theorem Frame.nextAction (frame : CampusTCPRoundStutter.Frame before endpoints after updated)
    (config : MonitorConfig) (monitor : Monitor) : CampusTCPRoundMonitor.nextAction config after monitor = CampusTCPRoundMonitor.nextAction config before monitor :=
  (congrArg (fun state => CampusTCPRoundMonitor.nextAction config state monitor) frame.fixed).symm

theorem Frame.nextEvent (frame : CampusTCPRoundStutter.Frame before endpoints after updated)
    (config : MonitorConfig) (monitor : Monitor) : CampusTCPRoundMonitor.nextEvent config after monitor = CampusTCPRoundMonitor.nextEvent config before monitor :=
  congrArg (Option.map CampusTCPRoundMonitor.Action.event) (Frame.nextAction frame config monitor)

theorem Frame.sameClock (frame : CampusTCPRoundStutter.Frame before endpoints after updated) (event : Event) :
    CampusTCPRoundMonitor.sameClock after event = CampusTCPRoundMonitor.sameClock before event := by
  cases event <;> simp only [CampusTCPRoundMonitor.sameClock, frame.beforeConnection, frame.afterConnection, frame.endpointEq]

theorem Frame.guards (frame : CampusTCPRoundStutter.Frame before endpoints after updated) (guards : Guards endpoints) :
    Guards updated := by
  intro actor
  rw [frame.endpointEq actor]
  exact guards actor

structure Move (before : Cut input complete) (actual : Step input) where
  after : Cut input complete
  beforeEq : actual.before = before.report.final
  supported : actual.result.supported = true
  passed : actual.result.passed = true
  history : after.report.steps = before.report.steps ++ [actual]
  final : after.report.final = actual.result.state

theorem Move.retained (move : Move before actual) : before.report.steps <+: move.after.report.steps := by
  rw [move.history]
  exact List.prefix_append _ _

theorem Move.member (move : Move before actual) : actual ∈ move.after.report.steps := by
  rw [move.history]
  simp only [List.mem_append, List.mem_singleton, or_true]

theorem At.clock {anchor current : Cut input complete} (placement : At anchor current) (actual : Step input)
    (before : actual.before = current.report.final) (actor : Actor)
    (event : actual.event = .advanceClock actor (endpoint current.endpoints actor).now)
    (guards : Guards current.endpoints) : ∃ move : Move current actual, At anchor move.after := by
  obtain ⟨appended⟩ := CampusTCPRoundStutter.Report.append_clock current.report current.supported current.finished
    complete current.endpoints current.connection actual before actor event
    (guards actor).recoveryCoherent (guards actor).prepared (guards actor).runtime
  let next : Cut input complete := ⟨_, appended.next, appended.supported, appended.finished,
    appended.updated, appended.frame.afterConnection⟩
  have supported : actual.result.supported = true := by
    have member : actual ∈ appended.next.steps := by
      rw [appended.history]
      simp only [List.mem_append, List.mem_singleton, or_true]
    exact List.all_eq_true.mp appended.supported actual member
  have localAction : LocalAction actor actual.event (.advanceClock (endpoint current.endpoints actor).now) := by
    rw [event]
    exact .advanceClock _
  have passed : actual.result.passed = true := CampusTCPRoundLocal.step_local_passed actual actor _ localAction
  let move : Move current actual := ⟨next, before, supported, passed, appended.history, appended.final⟩
  refine ⟨move, placement.retained.trans move.retained, placement.frame.trans appended.frame, ?_⟩
  obtain ⟨extra, history, clocks⟩ := placement.clocks
  refine ⟨extra ++ [actual], ?_, ?_⟩
  · rw [move.history, history, List.append_assoc]
  · intro selected member
    rcases List.mem_append.mp member with old | fresh
    · exact clocks selected old
    · have same : selected = actual := List.mem_singleton.mp fresh
      exact ⟨actor, _, same ▸ event⟩

structure Hop (prior : Cut input complete) (monitor : Monitor) where
  before : Cut input complete
  placement : At prior before
  actual : Step input
  move : Move before actual

def Hop.post {prior : Cut input complete} {priorMonitor : Monitor} (hop : Hop prior priorMonitor) :
    Cut input complete := hop.move.after
def Hop.monitor {prior : Cut input complete} {priorMonitor : Monitor}
    (hop : Hop prior priorMonitor) (config : MonitorConfig) : Monitor :=
  CampusTCPRoundMonitor.observe config priorMonitor hop.actual

theorem Hop.retained {prior : Cut input complete} {priorMonitor : Monitor} (hop : Hop prior priorMonitor) :
    prior.report.steps <+: hop.post.report.steps :=
  hop.placement.retained.trans hop.move.retained

structure Anchor (initial : Initial report complete request) (native : NativeEnv initial)
    (cut : Cut input complete) (monitor : Monitor) (phase : Phase) (offered : Option MonitorAction) : Prop where
  phaseEq : monitor.phase = phase
  next : CampusTCPRoundMonitor.nextAction (config initial native) cut.report.final monitor = offered
  guards : Guards cut.endpoints
  retained : initial.start.next.report.steps <+: cut.report.steps
  environment : CampusTCPRoundEnvironment.environment initial.state =
    CampusTCPRoundEnvironment.environment cut.report.final

structure Current (anchor : Cut input complete) (anchorMonitor : Monitor)
    (cut : Cut input complete) (monitor : Monitor) : Prop where
  placement : At anchor cut
  monitorEq : monitor = anchorMonitor

theorem Current.refl (cut : Cut input complete) (monitor : Monitor) : Current cut monitor cut monitor :=
  ⟨At.refl cut, rfl⟩

theorem Current.next (current : Current anchor anchorMonitor cut monitor) (config : MonitorConfig)
    (next : CampusTCPRoundMonitor.nextAction config anchor.report.final anchorMonitor = offered) :
    CampusTCPRoundMonitor.nextAction config cut.report.final monitor = offered := by
  rw [current.monitorEq, Frame.nextAction current.placement.frame]
  exact next

theorem Current.clock {anchor cut : Cut input complete} (current : Current anchor anchorMonitor cut monitor)
    (config : MonitorConfig) (actual : Step input) (before : actual.before = cut.report.final)
    (actor : Actor) (event : actual.event = .advanceClock actor (endpoint cut.endpoints actor).now)
    (guards : Guards cut.endpoints) :
    ∃ move : Move cut actual, Current anchor anchorMonitor move.after (CampusTCPRoundMonitor.observe config monitor actual) := by
  obtain ⟨move, placement⟩ := At.clock current.placement actual before actor event guards
  have clock : CampusTCPRoundMonitor.sameClock actual.before actual.event = true := by
    simp only [CampusTCPRoundMonitor.sameClock, before, event, cut.connection, (guards actor).runtime,
      beq_self_eq_true, Bool.and_self]
  refine ⟨move, placement, ?_⟩
  rw [CampusTCPRoundMonitor.observe_clock config monitor actual move.supported move.passed clock]
  exact current.monitorEq

theorem Step.eq_of_before_event (left right : Step input) (before : left.before = right.before)
    (event : left.event = right.event) : left = right := by
  have computed := left.computed
  rw [before, event, right.computed] at computed
  have result : left.result = right.result := (Except.ok.inj computed).symm
  cases left
  cases right
  simp_all only

structure ApplicationOutput (before : Cut input complete) (actual : Step input) (actor : Actor) where
  operation : T.Step
  recorded : actual.result.application = some (actor, operation)
  packet : EstablishedReceive.Input
  origin : T.OutputOrigin operation packet
  produced : Produced input.active input.passive
  output : actual.result.output = some produced
  production : produced = .application actor operation packet origin
  localBefore : operation.before = endpoint before.endpoints actor
  localStamp : operation.stamp = before.report.final.time

structure OriginalFields (produced : Produced input.active input.passive) : Prop where
  header : produced.source.packet.header = Output.reverse complete.certificate.activeSeed.core.inbound
  sequence : produced.source.packet.segment.sequence = input.active.iss.add 1
  acknowledgment : produced.source.packet.segment.acknowledgment = input.passive.iss.add 1
  payload : produced.source.packet.segment.payload = request.bytes
  profile : Admission.DataProfile produced.source.packet.segment
  ttl : 1 < produced.source.packet.ip.packet.ttl.toNat

structure AckFields (produced : Produced input.active input.passive) : Prop where
  header : produced.source.packet.header = Output.reverse complete.certificate.passiveSeed.core.inbound
  sequence : produced.source.packet.segment.sequence = input.passive.iss.add 1
  acknowledgment : produced.source.packet.segment.acknowledgment = (input.active.iss.add 1).add request.bytes.length
  payload : produced.source.packet.segment.payload = []
  profile : Admission.DataProfile produced.source.packet.segment
  ttl : 1 < produced.source.packet.ip.packet.ttl.toNat

structure Started (initial : Initial report complete request) (native : NativeEnv initial) where
  anchor : Anchor initial native (Cut.ofPrepared initial.start) Monitor.initial .needSend
    (some (.send .client request.bytes.length true))

theorem started (initial : Initial report complete request) (native : NativeEnv initial) : Started initial native :=
  ⟨⟨rfl, rfl, CampusTCPRoundGuards.PreparedStart.guards initial.start, List.prefix_refl _, rfl⟩⟩

structure Sent (initial : Initial report complete request) (native : NativeEnv initial) where
  hop : Hop (Cut.ofPrepared initial.start) Monitor.initial
  event : hop.actual.event = .send .client request.bytes.length true
  application : ApplicationOutput hop.before hop.actual .client
  sendEvent : application.operation.event = .send request.bytes.length true
  fields : OriginalFields (complete := complete) (request := request) application.produced
  sender : endpoint hop.post.endpoints .client =
    Endpoint.sendState (endpoint initial.start.next.endpoints .client) request.bytes.length
  receiver : endpoint hop.post.endpoints .server = endpoint initial.start.next.endpoints .server
  gateway : beforeService input hop.post.report.final .primary = initial.beforeService
  source : hop.post.report.final.outputs[hop.actual.before.outputs.length]? = some application.produced
  pending : IngressPending hop.post.report.final hop.actual.before.outputs.length
  anchor : Anchor initial native hop.post (hop.monitor (config initial native)) .dataIngress
    (some (.assign hop.actual.before.outputs.length native.dataIngress))

def Sent.index (sent : Sent initial native) : Nat := sent.hop.actual.before.outputs.length

variable {sent : Sent initial native}

structure Assigned (sent : Sent initial native) where
  hop : Hop sent.hop.post (sent.hop.monitor (config initial native))
  facts : CampusTCPRoundAssignment.AssignmentFacts hop.before.report.final sent.index
    native.dataIngress sent.application.produced hop.actual
  ticket : Work.Item (Ticket input.active input.passive)
  ticketEq : ticket = CampusTCPRoundAssignment.ticket hop.before.report.final sent.index native.dataIngress sent.application.produced
  sender : endpoint hop.post.endpoints .client =
    Endpoint.sendState (endpoint initial.start.next.endpoints .client) request.bytes.length
  receiver : endpoint hop.post.endpoints .server = endpoint initial.start.next.endpoints .server
  gateway : beforeService input hop.post.report.final .primary = initial.beforeService
  pending : ticket ∈ hop.post.report.final.work.pending
  anchor : Anchor initial native hop.post (hop.monitor (config initial native)) .dataTicket (some (.serve ticket.id))

variable {assigned : Assigned sent}

structure DataServed (assigned : Assigned sent) where
  hop : Hop assigned.hop.post (assigned.hop.monitor (config initial native))
  served : Served input
  emission : WireForwarding.Emission served.ticket.value.source.packet
  emitted : served.evidence.output = some emission
  facts : CampusTCPRoundService.ServiceFacts hop.before.report.final assigned.ticket
    ⟨initial.entry.flow, .original⟩ initial.session hop.actual served emission emitted
  sourceFields : OriginalFields (complete := complete) (request := request) served.ticket.value.produced
  session : Admission.Session
  phase : (beforeService input hop.post.report.final .primary).admission.phase = .data session
  geometry : CampusTCPRoundAdmission.DataGeometry initial.session session served.ticket.value.source.packet.segment
    served.before.admission.observations.length
  trackerValid : (beforeService input hop.post.report.final .primary).tracker.Valid
  records : (beforeService input hop.post.report.final .primary).tracker.records = [⟨initial.entry, true⟩]
  sender : endpoint hop.post.endpoints .client =
    Endpoint.sendState (endpoint initial.start.next.endpoints .client) request.bytes.length
  receiver : endpoint hop.post.endpoints .server = endpoint initial.start.next.endpoints .server
  stored : hop.post.report.final.services[hop.actual.before.services.length]? = some served
  pending : CampusTCPDeliveryEnabled.LinkPending hop.post.report.final hop.actual.before.services.length
  anchor : Anchor initial native hop.post (hop.monitor (config initial native)) .dataLink
    (some (.deliver hop.actual.before.services.length emission.bytes true))

def DataServed.index (service : DataServed assigned) : Nat := service.hop.actual.before.services.length

variable {service : DataServed assigned}

structure Released (service : DataServed assigned) where
  hop : Hop service.hop.post (service.hop.monitor (config initial native))
  delivery : CampusTCPRoundDelivery.DataDelivered hop.before.report complete hop.before.endpoints
    service.index service.served service.emission service.emitted
  actual : delivery.step = hop.actual
  server : endpoint hop.post.endpoints .server = delivery.after
  sender : endpoint hop.post.endpoints .client =
    Endpoint.sendState (endpoint initial.start.next.endpoints .client) request.bytes.length
  payload : (endpoint hop.post.endpoints .server).core.received = request.bytes
  receiveNext : (endpoint hop.post.endpoints .server).core.receiveNext = (input.active.iss.add 1).add request.bytes.length
  sendNext : (endpoint hop.post.endpoints .server).core.sendNext = input.passive.iss.add 1
  inbound : (endpoint hop.post.endpoints .server).core.inbound = complete.certificate.passiveSeed.core.inbound
  gateway : beforeService input hop.post.report.final .primary = beforeService input service.hop.post.report.final .primary
  anchor : Anchor initial native hop.post (hop.monitor (config initial native)) .needAck (some (.emitAck .server true))

variable {released : Released service}

structure Acked (released : Released service) where
  hop : Hop released.hop.post (released.hop.monitor (config initial native))
  facts : CampusTCPRoundAck.AckFacts hop.before.report.final complete hop.before.endpoints .server hop.actual
  fields : AckFields (complete := complete) (request := request) facts.produced
  sender : endpoint hop.post.endpoints .client =
    Endpoint.sendState (endpoint initial.start.next.endpoints .client) request.bytes.length
  payload : (endpoint hop.post.endpoints .server).core.received = request.bytes
  gateway : beforeService input hop.post.report.final .primary = beforeService input service.hop.post.report.final .primary
  source : hop.post.report.final.outputs[hop.actual.before.outputs.length]? = some facts.produced
  pending : IngressPending hop.post.report.final hop.actual.before.outputs.length
  anchor : Anchor initial native hop.post (hop.monitor (config initial native)) .ackIngress
    (some (.assign hop.actual.before.outputs.length native.ackIngress))

def Acked.index (ack : Acked released) : Nat := ack.hop.actual.before.outputs.length

variable {ack : Acked released}

structure AckAssigned (ack : Acked released) where
  hop : Hop ack.hop.post (ack.hop.monitor (config initial native))
  facts : CampusTCPRoundAssignment.AssignmentFacts hop.before.report.final ack.index
    native.ackIngress ack.facts.produced hop.actual
  ticket : Work.Item (Ticket input.active input.passive)
  ticketEq : ticket = CampusTCPRoundAssignment.ticket hop.before.report.final ack.index native.ackIngress ack.facts.produced
  sender : endpoint hop.post.endpoints .client =
    Endpoint.sendState (endpoint initial.start.next.endpoints .client) request.bytes.length
  payload : (endpoint hop.post.endpoints .server).core.received = request.bytes
  gateway : beforeService input hop.post.report.final .primary = beforeService input service.hop.post.report.final .primary
  pending : ticket ∈ hop.post.report.final.work.pending
  anchor : Anchor initial native hop.post (hop.monitor (config initial native)) .ackTicket (some (.serve ticket.id))

variable {assignment : AckAssigned ack}

structure AckServed (assignment : AckAssigned ack) where
  hop : Hop assignment.hop.post (assignment.hop.monitor (config initial native))
  served : Served input
  emission : WireForwarding.Emission served.ticket.value.source.packet
  emitted : served.evidence.output = some emission
  facts : CampusTCPRoundService.ServiceFacts hop.before.report.final assignment.ticket
    ⟨initial.entry.flow, .reply⟩ service.session hop.actual served emission emitted
  sourceFields : AckFields (complete := complete) (request := request) served.ticket.value.produced
  sender : endpoint hop.post.endpoints .client =
    Endpoint.sendState (endpoint initial.start.next.endpoints .client) request.bytes.length
  payload : (endpoint hop.post.endpoints .server).core.received = request.bytes
  stored : hop.post.report.final.services[hop.actual.before.services.length]? = some served
  pending : CampusTCPDeliveryEnabled.LinkPending hop.post.report.final hop.actual.before.services.length
  anchor : Anchor initial native hop.post (hop.monitor (config initial native)) .ackLink
    (some (.deliver hop.actual.before.services.length emission.bytes true))

def AckServed.index (service : AckServed assignment) : Nat := service.hop.actual.before.services.length

variable {ackService : AckServed assignment}

structure Retired (service : AckServed assignment) where
  hop : Hop service.hop.post (service.hop.monitor (config initial native))
  delivery : CampusTCPRoundDelivery.AckDelivered hop.before.report complete hop.before.endpoints
    service.index service.served service.emission service.emitted
  actual : delivery.step = hop.actual
  sender : endpoint hop.post.endpoints .client = delivery.after
  payload : (endpoint hop.post.endpoints .server).core.received = request.bytes
  anchor : Anchor initial native hop.post (hop.monitor (config initial native)) .needRead
    (some (.read .server request.bytes.length))

structure Read (retired : Retired ackService) where
  hop : Hop retired.hop.post (retired.hop.monitor (config initial native))
  event : hop.actual.event = .read .server request.bytes.length
  operation : T.Step
  recorded : hop.actual.result.application = some (.server, operation)
  localBefore : operation.before = endpoint hop.before.endpoints .server
  localEvent : operation.event = .read request.bytes.length
  localStamp : operation.stamp = hop.before.report.final.time
  returned : hop.actual.result.read = request.bytes
  localRead : operation.result.read = request.bytes
  sender : endpoint hop.post.endpoints .client = retired.delivery.after
  anchor : Anchor initial native hop.post (hop.monitor (config initial native)) .done none

inductive Evidence (initial : Initial report complete request) (native : NativeEnv initial)
    (current : Cut input complete) (monitor : Monitor) : Type where
  | started (record : Started initial native)
      (placement : Current (Cut.ofPrepared initial.start) Monitor.initial current monitor)
  | sent (record : Sent initial native)
      (placement : Current record.hop.post (record.hop.monitor (config initial native)) current monitor)
  | assigned (sent : Sent initial native) (record : Assigned sent)
      (placement : Current record.hop.post (record.hop.monitor (config initial native)) current monitor)
  | dataServed (sent : Sent initial native) (assigned : Assigned sent) (record : DataServed assigned)
      (placement : Current record.hop.post (record.hop.monitor (config initial native)) current monitor)
  | released (sent : Sent initial native) (assigned : Assigned sent) (service : DataServed assigned) (record : Released service)
      (placement : Current record.hop.post (record.hop.monitor (config initial native)) current monitor)
  | acked (sent : Sent initial native) (assigned : Assigned sent) (service : DataServed assigned)
      (released : Released service) (record : Acked released)
      (placement : Current record.hop.post (record.hop.monitor (config initial native)) current monitor)
  | ackAssigned (sent : Sent initial native) (assigned : Assigned sent) (service : DataServed assigned)
      (released : Released service) (ack : Acked released) (record : AckAssigned ack)
      (placement : Current record.hop.post (record.hop.monitor (config initial native)) current monitor)
  | ackServed (sent : Sent initial native) (assigned : Assigned sent) (service : DataServed assigned)
      (released : Released service) (ack : Acked released) (assignedAck : AckAssigned ack) (record : AckServed assignedAck)
      (placement : Current record.hop.post (record.hop.monitor (config initial native)) current monitor)
  | retired (sent : Sent initial native) (assigned : Assigned sent) (service : DataServed assigned)
      (released : Released service) (ack : Acked released) (assignedAck : AckAssigned ack)
      (ackService : AckServed assignedAck) (record : Retired ackService)
      (placement : Current record.hop.post (record.hop.monitor (config initial native)) current monitor)
  | read (sent : Sent initial native) (assigned : Assigned sent) (service : DataServed assigned)
      (released : Released service) (ack : Acked released) (assignedAck : AckAssigned ack)
      (ackService : AckServed assignedAck) (retired : Retired ackService) (record : Read retired)
      (placement : Current record.hop.post (record.hop.monitor (config initial native)) current monitor)

theorem initial_evidence (initial : Initial report complete request) (native : NativeEnv initial) :
    Nonempty (Evidence initial native (Cut.ofPrepared initial.start) Monitor.initial) :=
  ⟨.started (started initial native) (Current.refl _ _)⟩

theorem Evidence.guards (evidence : Evidence initial native current monitor) : Guards current.endpoints := by
  cases evidence <;> rename_i record placement
  all_goals exact Frame.guards placement.placement.frame record.anchor.guards

theorem Evidence.retained (evidence : Evidence initial native current monitor) :
    initial.start.next.report.steps <+: current.report.steps := by
  cases evidence <;> rename_i record placement
  all_goals exact record.anchor.retained.trans placement.placement.retained

theorem Evidence.environment (evidence : Evidence initial native current monitor) :
    CampusTCPRoundEnvironment.environment initial.state = CampusTCPRoundEnvironment.environment current.report.final := by
  cases evidence <;> rename_i record placement
  all_goals exact record.anchor.environment.trans placement.placement.frame.environment.symm

theorem Evidence.pending (evidence : Evidence initial native current monitor) (positive : 0 < monitor.rank) :
    ∃ action, CampusTCPRoundMonitor.nextAction (config initial native) current.report.final monitor = some action := by
  cases evidence <;> rename_i record placement
  all_goals first
    | exact ⟨_, placement.next _ record.anchor.next⟩
    | have zero : monitor.rank = 0 := by
        simp only [Monitor.rank, placement.monitorEq, record.anchor.phaseEq, Phase.rank]
      omega

end Netlib.Check.CampusTCPRoundPhaseBase
