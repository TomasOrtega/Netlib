import Netlib.Check.CampusTCPRoundProgress
import Netlib.Check.CampusTCPRoundPhaseHistory
import Netlib.Check.CampusTCPGapFacts
import Netlib.Check.CampusTCPStartupOrigins

/-!
# Origins in the completed campus round

The stored receipt links the application read to its actual write.
Compliance extends through the actual packet and clock operations.
-/

namespace Netlib.Check.CampusTCPRoundOrigins

open Packet Protocol Protocol.TCP CampusTCPModel CampusTCPEnabled CampusTCPRoundStart
open CampusTCPRoundPhaseBase CampusTCPRoundProgress
open CampusTCPRound (Cut)
open CampusTCPRoundPhaseHistory (isReceive)

variable {input : Input} {events : List CampusTCPModel.Event} {report : Report input events}
variable {complete : H.Completed input.active input.passive} {request : Request input}
variable {initial : Initial report complete request} {native : NativeEnv initial}
variable {current : Cut input complete} {monitor : CampusTCPRoundMonitor.Monitor}

theorem At.compliant (placement : At anchor current) (prior : anchor.report.compliant = true) :
    current.report.compliant = true := by
  obtain ⟨extra, history, clocks⟩ := placement.clocks
  simp only [Report.compliant, Bool.and_eq_true]
  refine ⟨current.supported, List.all_eq_true.mpr ?_⟩
  intro actual member
  rw [history] at member
  rcases List.mem_append.mp member with old | fresh
  · exact anchor.report.step_passed prior actual old
  · obtain ⟨actor, now, event⟩ := clocks actual fresh
    exact CampusTCPRoundLocal.step_local_passed actual actor (.advanceClock now)
      (by rw [event]; exact .advanceClock _)

theorem Move.compliant (move : Move before actual) (prior : before.report.compliant = true) :
    move.after.report.compliant = true := by
  simp only [Report.compliant, Bool.and_eq_true]
  refine ⟨move.after.supported, List.all_eq_true.mpr ?_⟩
  intro step member
  rw [move.history] at member
  rcases List.mem_append.mp member with old | fresh
  · exact before.report.step_passed prior step old
  · exact List.mem_singleton.mp fresh ▸ move.passed

theorem Hop.compliant {prior : Cut input complete} {priorMonitor : CampusTCPRoundMonitor.Monitor}
    (hop : Hop prior priorMonitor) (passed : prior.report.compliant = true) :
    hop.post.report.compliant = true :=
  Move.compliant hop.move (At.compliant hop.placement passed)

theorem Completion.compliant (done : Completion initial native current monitor)
    (prior : initial.start.next.report.compliant = true) : current.report.compliant = true := by
  apply At.compliant done.placement.placement
  exact Hop.compliant done.read.hop (Hop.compliant done.retired.hop
    (Hop.compliant done.ackService.hop (Hop.compliant done.assignedAck.hop
    (Hop.compliant done.ack.hop (Hop.compliant done.released.hop
    (Hop.compliant done.service.hop (Hop.compliant done.assigned.hop
    (Hop.compliant done.sent.hop prior))))))))

theorem At.application_prefix (placement : At anchor current) (actor : Actor) :
    applicationSteps anchor.endpoints actor <+: applicationSteps current.endpoints actor := by
  obtain ⟨extra, history, _⟩ := CampusTCPRoundPhaseHistory.At.application_history placement actor
  exact ⟨extra, history.symm⟩

private theorem Move.network_prefix (move : Move before actual)
    (network : CampusTCPRoundClock.NetworkAction actual.event) (actor : Actor) :
    applicationSteps before.endpoints actor <+: applicationSteps move.after.endpoints actor := by
  rw [CampusTCPRoundPhaseHistory.Move.network_history move network actor]
  exact List.prefix_refl _

private theorem Move.local_prefix (move : Move before actual) (actor : Actor) (event : T.Event)
    (action : LocalAction actor actual.event event) (operation : T.Step)
    (recorded : actual.result.application = some (actor, operation)) (receiver : Actor) :
    applicationSteps before.endpoints receiver <+: applicationSteps move.after.endpoints receiver := by
  rw [CampusTCPRoundPhaseHistory.Move.local_history move actor event action operation recorded receiver]
  exact List.prefix_append _ _

private theorem Move.delivery_prefix (move : Move before actual)
    (delivery : CampusTCPRoundDelivery.Delivery before.report complete before.endpoints index served emission emitted)
    (same : delivery.step = actual) (actor : Actor) :
    applicationSteps before.endpoints actor <+: applicationSteps move.after.endpoints actor := by
  rw [CampusTCPRoundPhaseHistory.Move.delivery_history move delivery same actor]
  exact List.prefix_append _ _

theorem Completion.sent_application_prefix (done : Completion initial native current monitor) (actor : Actor) :
    applicationSteps done.sent.hop.post.endpoints actor <+: applicationSteps current.endpoints actor := by
  have assigned := (At.application_prefix done.assigned.hop.placement actor).trans
    (Move.network_prefix done.assigned.hop.move (by rw [done.assigned.facts.event]; exact .assign _ _) actor)
  have service := (At.application_prefix done.service.hop.placement actor).trans
    (Move.network_prefix done.service.hop.move (by rw [done.service.facts.event]; exact .serve _ _) actor)
  have released := (At.application_prefix done.released.hop.placement actor).trans
    (Move.delivery_prefix done.released.hop.move done.released.delivery.toDelivery done.released.actual actor)
  have ack := (At.application_prefix done.ack.hop.placement actor).trans
    (Move.local_prefix done.ack.hop.move .server (.emitAck true)
      (by rw [done.ack.facts.event]; exact .emitAck _) done.ack.facts.localStep done.ack.facts.application actor)
  have assignedAck := (At.application_prefix done.assignedAck.hop.placement actor).trans
    (Move.network_prefix done.assignedAck.hop.move (by rw [done.assignedAck.facts.event]; exact .assign _ _) actor)
  have ackService := (At.application_prefix done.ackService.hop.placement actor).trans
    (Move.network_prefix done.ackService.hop.move (by rw [done.ackService.facts.event]; exact .serve _ _) actor)
  have retired := (At.application_prefix done.retired.hop.placement actor).trans
    (Move.delivery_prefix done.retired.hop.move done.retired.delivery.toDelivery done.retired.actual actor)
  have read := (At.application_prefix done.read.hop.placement actor).trans
    (Move.local_prefix done.read.hop.move .server (.read request.bytes.length)
      (by rw [done.read.event]; exact .read _) done.read.operation done.read.recorded actor)
  exact assigned.trans (service.trans (released.trans (ack.trans (assignedAck.trans
    (ackService.trans (retired.trans (read.trans (At.application_prefix done.placement.placement actor))))))))

theorem Completion.send_member (done : Completion initial native current monitor) :
    done.sent.application.operation ∈ applicationSteps current.endpoints .client := by
  have history := CampusTCPRoundPhaseHistory.Move.local_history done.sent.hop.move .client
    (.send request.bytes.length true) (by rw [done.sent.event]; exact .send _ _)
    done.sent.application.operation done.sent.application.recorded .client
  have member : done.sent.application.operation ∈ applicationSteps done.sent.hop.post.endpoints .client := by
    change done.sent.application.operation ∈ applicationSteps done.sent.hop.move.after.endpoints .client
    rw [history]
    simp only [ite_true, List.mem_append, List.mem_singleton, or_true]
  exact (Completion.sent_application_prefix done .client).subset member

theorem Completion.released_retained (done : Completion initial native current monitor) :
    done.released.hop.post.report.steps <+: current.report.steps :=
  done.ack.hop.retained.trans (done.assignedAck.hop.retained.trans
    (done.ackService.hop.retained.trans (done.retired.hop.retained.trans
    (done.read.hop.retained.trans done.placement.placement.retained))))

theorem Completion.data_service_member (done : Completion initial native current monitor) :
    done.service.hop.actual ∈ current.report.steps :=
  (done.released.hop.retained.trans (Completion.released_retained done)).subset done.service.hop.move.member

theorem Completion.ack_service_member (done : Completion initial native current monitor) :
    done.ackService.hop.actual ∈ current.report.steps :=
  (done.retired.hop.retained.trans (done.read.hop.retained.trans done.placement.placement.retained)).subset
    done.ackService.hop.move.member

private theorem data_production (done : Completion initial native current monitor) :
    done.service.served.ticket.value.produced = .application .client done.sent.application.operation
      done.sent.application.packet done.sent.application.origin := by
  rw [done.service.facts.ticket, done.assigned.ticketEq]
  exact done.sent.application.production

theorem Completion.data_delivery (done : Completion initial native current monitor) :
    Nonempty (CampusTCPFacts.ApplicationDelivery current.report (applicationSteps current.endpoints .client)
      .server done.released.delivery.localStep) := by
  have actor : done.service.served.ticket.value.produced.actor = .client := by rw [data_production done]; rfl
  have member : done.released.delivery.step ∈ current.report.steps :=
    (Completion.released_retained done).subset (done.released.actual.symm ▸ done.released.hop.move.member)
  let receive : CampusTCPFacts.ReceiveAt current.report .server done.released.delivery.localStep := {
    joint := ⟨done.released.delivery.step, member,
      (done.released.delivery.stamp.trans (congrArg State.time done.released.delivery.beforeEq.symm)).symm⟩
    service := done.service.index
    raw := done.service.emission.bytes
    policy := true
    delivered := done.released.delivery.event
    receipt := done.released.delivery.receipt
    recorded := done.released.delivery.receiptAt
    applied := by simpa only [actor, Actor.other] using done.released.delivery.recorded
    received := done.service.emission.asInput
    event := done.released.delivery.localEvent
    same := done.released.delivery.receiptPacket
    receiver := by rw [done.released.delivery.receipt.receiver, done.released.delivery.receiptService, actor]; rfl }
  obtain ⟨service⟩ := CampusTCPStartupOrigins.DeliveryAt.service_exists receive.delivery
  let lineage := CampusTCPFacts.gateway_lineage receive.delivery service
  obtain ⟨prior, later, history⟩ := List.mem_iff_append.mp (Completion.send_member done)
  let source : ApplicationTrace.OutputAt (applicationSteps current.endpoints .client) :=
    ⟨prior, done.sent.application.operation, later, history, done.sent.application.packet, done.sent.application.origin⟩
  have production : receive.receipt.served.ticket.value.produced =
      .application .client done.sent.application.operation done.sent.application.packet done.sent.application.origin := by
    change done.released.delivery.receipt.served.ticket.value.produced = _
    rw [done.released.delivery.receiptService]
    exact data_production done
  have path : ApplicationTrace.BytePath source.output receive.received := by
    rw [← receive.same]
    have actual := receive.receipt.bytePath
    simpa only [production, Produced.output] using actual
  have earlier : source.step.stamp < done.released.delivery.localStep.stamp := by
    have ordered := CampusTCPFacts.GatewayLineage.source_earlier lineage
    change receive.receipt.served.ticket.value.produced.time < receive.receipt.time at ordered
    simp only [production, Produced.time] at ordered
    have time := (CampusTCPFacts.deliver_origin receive.joint.step receive.service receive.raw receive.policy
      receive.delivered receive.receipt receive.recorded).1.trans receive.joint.time
    change done.sent.application.operation.stamp < _
    omega
  exact ⟨⟨receive, service, lineage, source,
    ⟨.client, done.sent.application.operation, done.sent.application.packet, done.sent.application.origin,
      production, rfl, rfl, rfl⟩, path, earlier⟩⟩

private theorem receives_of_filter (steps : List T.Step)
    (selected : steps.filter isReceive = [operation])
    (delivery : CampusTCPFacts.ApplicationDelivery report peer actor operation) :
    Nonempty (CampusTCPFacts.Receives report peer actor steps) := by
  induction steps with
  | nil => simp at selected
  | cons head tail ih =>
    cases event : head.event with
    | receive packet =>
      simp only [List.filter_cons, isReceive, event, ↓reduceIte, List.cons.injEq] at selected
      have same := selected.1
      have empty := selected.2
      have other : ∀ step ∈ tail, ∀ packet, step.event ≠ .receive packet := by
        intro step member packet received
        have absent : step ∉ tail.filter isReceive := by rw [empty]; simp
        exact absent (List.mem_filter.mpr ⟨member, by simp only [isReceive, received]⟩)
      have others : Nonempty (CampusTCPFacts.Receives report peer actor tail) := by
        clear ih selected empty
        induction tail with
        | nil => exact ⟨.nil⟩
        | cons first rest ih =>
          obtain ⟨remaining⟩ := ih (by intro step member; exact other step (List.mem_cons_of_mem _ member))
          exact ⟨.other first (other first (by simp)) remaining⟩
      obtain ⟨remaining⟩ := others
      exact ⟨.receive head packet event (same.symm ▸ delivery) remaining⟩
    | _ =>
      have notReceive : ∀ packet, head.event ≠ .receive packet := by intro packet same; rw [event] at same; cases same
      have filtered : tail.filter isReceive = [operation] := by
        simpa only [List.filter_cons, isReceive, event, Bool.false_eq_true, ↓reduceIte] using selected
      obtain ⟨remaining⟩ := ih filtered
      exact ⟨.other head notReceive remaining⟩

theorem Completion.server_receives (done : Completion initial native current monitor) :
    Nonempty (CampusTCPFacts.Receives current.report (applicationSteps current.endpoints .client) .server
      (applicationSteps current.endpoints .server)) := by
  obtain ⟨delivery⟩ := Completion.data_delivery done
  exact receives_of_filter _ (CampusTCPRoundPhaseHistory.Completion.server_receives done) delivery

theorem Completion.server_read_origin (done : Completion initial native current monitor)
    (index : Nat) (byte : UInt8) (selected : request.bytes[index]? = some byte) :
    Nonempty (CampusTCPGapFacts.ReadOrigin current.report complete.certificate.activeSeed
      (applicationSteps current.endpoints .client) .server (applicationSteps current.endpoints .server)
      done.read.operation index byte) := by
  obtain ⟨receives⟩ := Completion.server_receives done
  have history : ApplicationTrace.DeliveryHistory (applicationSteps current.endpoints .client)
      (applicationSteps current.endpoints .server) :=
    ⟨current.endpoints.client.ordered, current.endpoints.server.ordered, receives.delivered⟩
  have reader : done.read.operation ∈ applicationSteps current.endpoints .server := by
    have all := CampusTCPRoundPhaseHistory.Completion.server_nonempty_reads done
    have member : done.read.operation ∈ (applicationSteps current.endpoints .server).filter
        CampusTCPRoundPhaseHistory.nonemptyRead := by rw [all]; simp
    exact (List.mem_filter.mp member).1
  have empty := complete.certificate.empty
  apply CampusTCPGapFacts.read_origin current.endpoints.server.chain current.endpoints.client.chain history receives
    empty.2.2.2.2.2 complete.certificate.empty_receiveStore.2 empty.2.1 empty.1
    done.read.operation reader request.bytes.length done.read.localEvent index byte
  change done.read.operation.result.read[index]? = some byte
  rw [done.read.localRead]
  exact selected

structure ServicePermissions (step : Step input) (served : Served input) : Prop where
  current : ∃ processing, served.evidence.processing = some processing ∧
    ∃ requirement ∈ input.context.requirements, requirement.test.Holds processing.outcome.afterDestination ∧
      Session.Valid input.context.authentication.context
        (Check.SessionFirewall.stateAt input.context.authentication step.before.authentication).session input.application ∧
      EAPAuth.State.Ready (EAPSession.authContext input.context.authentication.context)
        (Check.SessionFirewall.stateAt input.context.authentication step.before.authentication).auth
  ingress : ∃ attachment ∈ (step.before.resident served.ticket.value.gateway).attachments.map (·.value),
    IngressAttachment.allows (CampusTCPService.current (input.contextFor served.ticket.value.gateway)
      (beforeService input step.before served.ticket.value.gateway))
      attachment ⟨served.ticket.value.ingress, served.ticket.value.source.packet.header⟩ = true ∧
    Session.Valid input.context.authentication.context
      (Check.SessionFirewall.stateAt input.context.authentication step.before.authentication).session attachment.scope ∧
    EAPAuth.State.Ready (EAPSession.authContext input.context.authentication.context)
      (Check.SessionFirewall.stateAt input.context.authentication step.before.authentication).auth ∧
    served.ticket.value.ingress = attachment.ingress ∧
      attachment.origin.principal = input.context.authentication.context.consumer
  route : ∃ processing, served.evidence.processing = some processing ∧
    processing.outcome.nextHop = some served.ticket.value.produced.actor.nextHop
  walk : Network.Walk (Examples.CampusDirect.network input.context.authentication.context
    (Check.SessionFirewall.stateAt input.context.authentication step.before.authentication) input.application step.before.primaryFenced)
    (Examples.CampusDirect.source served.ticket.value.produced.actor.direction)
    (Examples.CampusDirect.target served.ticket.value.produced.actor.direction)
    (Examples.CampusDirect.routeTrace served.ticket.value.gateway served.ticket.value.produced.actor.direction)
  isolated : (Examples.CampusDirect.network input.context.authentication.context
    (Check.SessionFirewall.stateAt input.context.authentication step.before.authentication) input.application step.before.primaryFenced).Isolated
    Examples.CampusDirect.endpoints Examples.CampusDirect.managers

theorem service_permissions (report : Report input events) (compliant : report.compliant = true)
    (step : Step input) (member : step ∈ report.steps) (served : Served input)
    (present : step.result.service = some served) (emission : WireForwarding.Emission served.ticket.value.source.packet)
    (emitted : served.evidence.output = some emission) : ServicePermissions step served := by
  have topology := CampusTCPFacts.service_topology report compliant step member served present emission emitted
  exact ⟨CampusTCPFacts.service_current_permission report compliant step member served present emission emitted,
    CampusTCPFacts.service_ingress_permission report compliant step member served present emission emitted,
    topology.1, topology.2.1, topology.2.2⟩

theorem Completion.data_permissions (done : Completion initial native current monitor)
    (prior : initial.start.next.report.compliant = true) :
    ServicePermissions done.service.hop.actual done.service.served :=
  service_permissions current.report (Completion.compliant done prior) done.service.hop.actual
    (Completion.data_service_member done) done.service.served done.service.facts.recorded
    done.service.emission done.service.emitted

theorem Completion.ack_permissions (done : Completion initial native current monitor)
    (prior : initial.start.next.report.compliant = true) :
    ServicePermissions done.ackService.hop.actual done.ackService.served :=
  service_permissions current.report (Completion.compliant done prior) done.ackService.hop.actual
    (Completion.ack_service_member done) done.ackService.served done.ackService.facts.recorded
    done.ackService.emission done.ackService.emitted

end Netlib.Check.CampusTCPRoundOrigins
