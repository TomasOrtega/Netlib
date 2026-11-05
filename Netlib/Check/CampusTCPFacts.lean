import Netlib.Check.CampusTCPModel
import Netlib.Check.CampusTCPOrigins

/-!
# Checked campus TCP history and application results

History evidence refers to actual operations in one joint replay.
Each receive path retains endpoint output, assignment, gateway service, and delivery references.
-/

namespace Netlib.Check.CampusTCPFacts

open Packet Protocol
namespace M
export Check.CampusTCPModel
  (Input State Step Trace Report Actor Produced Ticket Served Receipt Applications Connection)
end M

abbrev PacketInput := TCP.EstablishedReceive.Input
abbrev AppStep := TCP.ApplicationTrace.Step

namespace Trace

theorem preceding (trace : M.Trace input initial events steps final remaining) (head : M.Step input) (member : head ∈ steps) :
    ∃ prior later, steps = prior ++ head :: later ∧
      M.Trace input initial (prior.map (·.event)) prior head.before [] := by
  induction trace with
  | done state => simp at member
  | stop step blocked tail =>
    have same : head = step := by simpa using member
    subst head
    exact ⟨[], [], rfl, .done _⟩
  | next step supported rest ih =>
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨[], _, rfl, .done _⟩
    · obtain ⟨prior, later, same, preceding⟩ := ih member
      exact ⟨step :: prior, later, by simp [same], .next step supported preceding⟩

end Trace

theorem step_origin (report : M.Report input events) (step : M.Step input) (member : step ∈ report.steps) :
    ∃ prior later, report.steps = prior ++ step :: later ∧
      M.Trace input input.initial (prior.map (·.event)) prior step.before [] ∧
      events = prior.map (·.event) ++ step.event :: (later.map (·.event) ++ report.remaining) ∧
      Check.CampusTCPModel.step input step.before step.event = .ok step.result := by
  obtain ⟨prior, later, same, preceding⟩ := Trace.preceding report.trace step member
  refine ⟨prior, later, same, preceding, ?_, step.computed⟩
  have covered := report.trace.covered
  rw [same, List.map_append] at covered
  simpa only [List.map_cons, List.append_assoc, List.cons_append] using covered.symm

structure At (report : M.Report input events) (time : Nat) where
  step : M.Step input
  member : step ∈ report.steps
  time : step.before.time = time

def findStep (report : M.Report input events) (time : Nat) : Except String (At report time) :=
  match found : report.steps.find? (fun step => decide (step.before.time = time)) with
  | none => .error "The referenced joint operation is absent from this replay."
  | some step => .ok ⟨step, List.mem_of_find?_eq_some found,
      of_decide_eq_true (List.find?_some (p := fun step : M.Step input => decide (step.before.time = time)) found)⟩

theorem serve_origin (step : M.Step input) (id : Nat) (observed : Option (List UInt8 × Option (List UInt8)))
    (event : step.event = .serve id observed) (served : M.Served input) (present : step.result.service = some served) :
    ∃ completed : Theory.Outstanding.Completed step.before.work id,
      Theory.Outstanding.complete step.before.work id = .ok completed ∧ served.ticket = completed.item ∧
      served.before = Check.CampusTCPModel.beforeService input step.before ∧ served.time = step.before.time ∧
      step.result.passed = served.passed := by
  obtain ⟨effect, computed, result⟩ := step.processed
  have selected : effect.service = some served := by simpa only [result] using present
  rw [event] at computed
  simp only [Check.CampusTCPModel.process] at computed
  cases completed : Theory.Outstanding.complete step.before.work id with
  | error reason => simp [completed, Except.mapError, bind, Except.bind] at computed
  | ok work =>
    simp only [completed, Except.mapError, bind, Except.bind] at computed
    split at computed
    · simp only [throw] at computed
      cases computed
    · simp only [pure, Except.pure, Except.ok.injEq] at computed
      subst effect
      cases selected
    · rename_i evidence accepted
      simp only [pure, Except.pure, Except.ok.injEq] at computed
      subst effect
      simp only at selected
      cases selected
      exact ⟨work, rfl, rfl, rfl, rfl, by rw [result]⟩

theorem assign_origin (step : M.Step input) (index : Nat) (ingress : IngressAttachment.InterfaceRef)
    (event : step.event = .assign index ingress) :
    ∃ produced, step.before.outputs[index]? = some produced ∧
      step.result.state.work = Theory.Outstanding.enqueue step.before.work ⟨index, produced, ingress⟩ := by
  obtain ⟨effect, computed, result⟩ := step.processed
  rw [event] at computed
  simp only [Check.CampusTCPModel.process] at computed
  cases found : step.before.outputs[index]? with
  | none => simp [Check.CampusTCPModel.get, found, bind, Except.bind] at computed
  | some produced =>
    simp only [Check.CampusTCPModel.get, found, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at computed
    subst effect
    exact ⟨produced, rfl, by rw [result]⟩

private theorem input_bytes (packet : PacketInput) (accepted : TCP.EstablishedReceive.input bytes = .ok packet) :
    packet.bytes = bytes := by
  unfold TCP.EstablishedReceive.input at accepted
  split at accepted
  · cases accepted
  · cases accepted
    rfl


theorem deliver_origin (step : M.Step input) (index : Nat) (bytes : List UInt8) (policy : Bool)
    (event : step.event = .deliver index bytes policy) (receipt : M.Receipt input)
    (present : step.result.receipt = some receipt) :
    receipt.time = step.before.time ∧ receipt.serviceIndex = index ∧
      step.before.services[index]? = some receipt.served := by
  obtain ⟨effect, computed, result⟩ := step.processed
  have selected : effect.receipt = some receipt := by simpa only [result] using present
  rw [event] at computed
  simp only [Check.CampusTCPModel.process] at computed
  cases found : step.before.services[index]? with
  | none => simp [Check.CampusTCPModel.get, found, bind, Except.bind] at computed
  | some served =>
    simp only [Check.CampusTCPModel.get, found, bind, Except.bind] at computed
    repeat' first
      | (cases computed <;> simp only at selected <;> cases selected <;> exact ⟨rfl, rfl, rfl⟩)
      | (split at computed)
      | (dsimp only [Check.CampusTCPModel.parsed, Except.mapError, bind, Except.bind, pure, Except.pure, throw] at computed)



private theorem eq_of_distinct_keys (key : α → Nat) (steps : List α)
    (distinct : steps.Pairwise (fun first second => key first ≠ key second))
    (first second : α) (firstMember : first ∈ steps) (secondMember : second ∈ steps)
    (same : key first = key second) : first = second := by
  induction steps with
  | nil => simp at firstMember
  | cons head tail ih =>
    have pair := List.pairwise_cons.mp distinct
    rcases List.mem_cons.mp firstMember with rfl | memberFirst
    · rcases List.mem_cons.mp secondMember with rfl | memberSecond
      · rfl
      · exact False.elim (pair.1 second memberSecond same)
    · rcases List.mem_cons.mp secondMember with rfl | memberSecond
      · exact False.elim (pair.1 first memberFirst same.symm)
      · exact ih pair.2 memberFirst memberSecond

theorem At.unique {input : M.Input} {events : List Check.CampusTCPModel.Event}
    {report : M.Report input events} {time : Nat} (first second : At report time) : first.step = second.step := by
  have unique : (report.steps.map (·.before.time)).Nodup := by
    rw [report.indices]
    exact List.nodup_range'
  have distinct := List.pairwise_map.mp (List.nodup_iff_pairwise_ne.mp unique)
  exact eq_of_distinct_keys (fun step : M.Step input => step.before.time) report.steps distinct
    first.step second.step first.member second.member (first.time.trans second.time.symm)

private theorem packet_eq (first second : PacketInput) (same : first.bytes = second.bytes) : first = second := by
  have checked := first.checked
  rw [same, second.checked] at checked
  have packet := (Except.ok.inj checked).symm
  cases first
  cases second
  dsimp only at same packet
  cases same
  cases packet
  rfl

private theorem app_step_eq (first second : AppStep) (before : first.before = second.before)
    (event : first.event = second.event) (stamp : first.stamp = second.stamp) : first = second := by
  cases first with
  | mk firstBefore firstEvent firstResult firstStamp firstValid firstComputed =>
    cases second with
    | mk secondBefore secondEvent secondResult secondStamp secondValid secondComputed =>
      dsimp only at before event stamp
      subst secondBefore
      subst secondEvent
      subst secondStamp
      cases firstComputed
      cases secondComputed
      rfl

structure ReceiveAt (report : M.Report input events) (actor : M.Actor) (step : AppStep) where
  joint : At report step.stamp
  service : Nat
  raw : List UInt8
  policy : Bool
  delivered : joint.step.event = .deliver service raw policy
  receipt : M.Receipt input
  recorded : joint.step.result.receipt = some receipt
  applied : joint.step.result.application = some (actor, step)
  received : PacketInput
  event : step.event = .receive received
  same : receipt.received = received
  receiver : receipt.actor = actor

def receiveAt (report : M.Report input events) (actor : M.Actor) (step : AppStep) : Except String (ReceiveAt report actor step) := do
  let joint ← findStep report step.stamp
  match delivered : joint.step.event with
  | .deliver service raw policy =>
    match recorded : joint.step.result.receipt with
    | none => throw "The joint delivery has no stored gateway receipt."
    | some receipt =>
      match applied : joint.step.result.application with
      | none => throw "The joint delivery has no application operation."
      | some (actualActor, actualStep) =>
        if actorEq : actualActor = actor then
          if receiver : receipt.actor = actor then
            match actualEvent : actualStep.event, event : step.event with
            | .receive actual, .receive received =>
              if before : actualStep.before = step.before then
                if stamp : actualStep.stamp = step.stamp then
                  if bytes : actual.bytes = received.bytes then
                    if same : receipt.received.bytes = received.bytes then
                      have packet := packet_eq actual received bytes
                      have equal : actualStep = step := app_step_eq actualStep step before
                        (by rw [actualEvent, event, packet]) stamp
                      return ⟨joint, service, raw, policy, delivered, receipt, recorded,
                        by simpa only [actorEq, equal] using applied, received, event,
                        packet_eq _ _ same, receiver⟩
                    else throw "The application input differs from the actual gateway receipt."
                  else throw "The application input differs from its actual joint operation."
                else throw "The application stamp differs from its actual joint operation."
              else throw "The application state differs from its actual joint operation."
            | _, _ => throw "The selected application operation is not a receive."
          else throw "The gateway receipt names a different receiving endpoint."
        else throw "The joint operation names a different receiving endpoint."
  | _ => throw "The application receive has no actual joint delivery event."


structure DeliveryAt (report : M.Report input events) (time : Nat) (actor : M.Actor) where
  joint : At report time
  service : Nat
  raw : List UInt8
  policy : Bool
  delivered : joint.step.event = .deliver service raw policy
  receipt : M.Receipt input
  recorded : joint.step.result.receipt = some receipt
  received : PacketInput
  same : receipt.received = received
  receiver : receipt.actor = actor

def ReceiveAt.delivery (value : ReceiveAt report actor step) : DeliveryAt report step.stamp actor :=
  ⟨value.joint, value.service, value.raw, value.policy, value.delivered, value.receipt, value.recorded,
    value.received, value.same, value.receiver⟩

def deliveryAt (report : M.Report input events) (time : Nat) (actor : M.Actor) (packet : PacketInput) :
    Except String { value : DeliveryAt report time actor // value.received = packet } := do
  let joint ← findStep report time
  match delivered : joint.step.event with
  | .deliver service raw policy =>
    match recorded : joint.step.result.receipt with
    | none => throw "The startup delivery has no actual gateway receipt."
    | some receipt =>
      if receiver : receipt.actor = actor then
        if bytes : receipt.received.bytes = packet.bytes then
          return ⟨⟨joint, service, raw, policy, delivered, receipt, recorded, packet, packet_eq _ _ bytes, receiver⟩, rfl⟩
        else throw "The startup input differs from its actual gateway receipt."
      else throw "The startup delivery names a different receiving endpoint."
  | _ => throw "The startup input has no actual joint delivery event."

private theorem earlier_gateway (value : DeliveryAt report time actor) :
    ∃ service, service ∈ report.steps ∧ service.result.service = some value.receipt.served ∧
      value.receipt.served.time = service.before.time ∧ service.before.time < value.joint.step.before.time := by
  have selected := (deliver_origin value.joint.step value.service value.raw value.policy value.delivered
    value.receipt value.recorded).2.2
  obtain ⟨prior, later, same, preceding, _, _⟩ := step_origin report value.joint.step value.joint.member
  rcases CampusTCPOrigins.Trace.services_origin preceding value.receipt.served (List.mem_of_getElem? selected) with old | created
  · simp only [Check.CampusTCPModel.Input.initial, List.mem_nil_iff] at old
  · obtain ⟨service, member, present, time, earlier⟩ := created
    exact ⟨service, by rw [same]; simp [member], present, time, earlier⟩

structure GatewayService {input : M.Input} {events : List Check.CampusTCPModel.Event}
    {report : M.Report input events} {actor : M.Actor} {time : Nat}
    (value : DeliveryAt report time actor) where
  joint : At report value.receipt.served.time
  present : joint.step.result.service = some value.receipt.served
  id : Nat
  observed : Option (List UInt8 × Option (List UInt8))
  event : joint.step.event = .serve id observed
  completed : Theory.Outstanding.Completed joint.step.before.work id
  computed : Theory.Outstanding.complete joint.step.before.work id = .ok completed
  ticket : value.receipt.served.ticket = completed.item
  before : value.receipt.served.before = Check.CampusTCPModel.beforeService input joint.step.before
  passed : joint.step.result.passed = value.receipt.served.passed
  earlier : value.receipt.served.time < value.receipt.time

def gatewayService (value : DeliveryAt report time actor) : Except String (GatewayService value) := do
  let joint ← findStep report value.receipt.served.time
  have actual : joint.step.result.service = some value.receipt.served := by
    obtain ⟨service, member, present, time, _⟩ := earlier_gateway value
    have same := joint.unique ⟨service, member, time.symm⟩
    rw [same]
    exact present
  match event : joint.step.event with
  | .serve id observed =>
    match computed : Theory.Outstanding.complete joint.step.before.work id with
    | .error _ => throw "The referenced service has no actual completed work item."
    | .ok completed =>
      have facts : value.receipt.served.ticket = completed.item ∧
          value.receipt.served.before = Check.CampusTCPModel.beforeService _ joint.step.before ∧
          joint.step.result.passed = value.receipt.served.passed := by
        obtain ⟨work, accepted, ticket, before, time, passed⟩ :=
          serve_origin joint.step id observed event value.receipt.served actual
        have same : work = completed := Except.ok.inj (accepted.symm.trans computed)
        exact ⟨by rw [← same]; exact ticket, before, passed⟩
      have earlier : value.receipt.served.time < value.receipt.time := by
        obtain ⟨service, member, present, time, earlier⟩ := earlier_gateway value
        have received := (deliver_origin value.joint.step value.service value.raw value.policy value.delivered
          value.receipt value.recorded).1
        omega
      return ⟨joint, actual, id, observed, event, completed, computed, facts.1, facts.2.1, facts.2.2, earlier⟩
  | _ => throw "The referenced gateway output has no actual service operation."

def GatewayLineage (report : M.Report input events) (value : DeliveryAt report time actor) : Prop :=
  ∃ producer assignment index ingress,
    producer ∈ report.steps ∧ assignment ∈ report.steps ∧
      producer.result.output = some value.receipt.served.ticket.value.produced ∧
      assignment.event = .assign index ingress ∧
      assignment.before.outputs[index]? = some value.receipt.served.ticket.value.produced ∧
      value.receipt.served.ticket = Theory.Outstanding.newItem assignment.before.work
        ⟨index, value.receipt.served.ticket.value.produced, ingress⟩ ∧
      value.receipt.served.ticket.value.produced.time = producer.before.time ∧
      producer.before.time < assignment.before.time ∧
      assignment.before.time < value.receipt.served.time ∧ value.receipt.served.time < value.receipt.time

theorem gateway_lineage (value : DeliveryAt report time actor) (service : GatewayService value) : GatewayLineage report value := by
  obtain ⟨prior, later, same, preceding, _, _⟩ := step_origin report service.joint.step service.joint.member
  have pending : value.receipt.served.ticket ∈ service.joint.step.before.work.pending := by
    rw [service.ticket]
    exact service.completed.member
  rcases CampusTCPOrigins.Trace.pending_origin preceding value.receipt.served.ticket pending with old | created
  · simp only [Check.CampusTCPModel.Input.initial, Theory.Outstanding.State.initial, List.mem_nil_iff] at old
  · obtain ⟨assignment, index, ingress, produced, member, event, selected, exactItem, earlier⟩ := created
    have assigned : assignment ∈ report.steps := by rw [same]; simp [member]
    obtain ⟨first, rest, split, prefixTrace, _, _⟩ := step_origin report assignment assigned
    rcases CampusTCPOrigins.Trace.outputs_origin prefixTrace produced (List.mem_of_getElem? selected) with old | output
    · simp only [Check.CampusTCPModel.Input.initial, List.mem_nil_iff] at old
    · obtain ⟨producer, sourceMember, emitted, stamped, sourceEarlier⟩ := output
      have source : producer ∈ report.steps := by rw [split]; simp [sourceMember]
      have exactProduced : value.receipt.served.ticket.value.produced = produced := by rw [exactItem]; rfl
      have serviceTime := service.joint.time
      refine ⟨producer, assignment, index, ingress, source, assigned, ?_, event, ?_, ?_, ?_, sourceEarlier, ?_, service.earlier⟩
      · rw [exactProduced]
        exact emitted
      · rw [exactProduced]
        exact selected
      · rw [exactProduced]
        exact exactItem
      · rw [exactProduced]
        exact stamped
      · omega

theorem GatewayLineage.source_earlier (lineage : GatewayLineage report value) :
    value.receipt.served.ticket.value.produced.time < value.receipt.time := by
  obtain ⟨producer, assignment, index, ingress, _, _, _, _, _, _, stamped, first, second, third⟩ := lineage
  omega


abbrev ServiceAt (value : ReceiveAt report actor step) : Type := GatewayService value.delivery

def serviceAt (value : ReceiveAt report actor step) : Except String (ServiceAt value) := gatewayService value.delivery

abbrev Lineage (report : M.Report input events) (value : ReceiveAt report actor step) : Prop :=
  GatewayLineage report value.delivery

theorem service_lineage (value : ReceiveAt report actor step) (service : ServiceAt value) : Lineage report value :=
  gateway_lineage value.delivery service

theorem Lineage.source_earlier (lineage : Lineage report value) :
    value.receipt.served.ticket.value.produced.time < value.receipt.time := GatewayLineage.source_earlier lineage

private theorem origin_output (origin : TCP.ApplicationTrace.OutputOrigin step output) : step.result.output = some output := by
  cases origin <;> assumption

private def sameOutputEvent (first second : AppStep) : Except String { _value : Unit // first.event = second.event } :=
  match firstEvent : first.event, secondEvent : second.event with
  | .send firstCount firstPolicy, .send secondCount secondPolicy =>
    if same : firstCount = secondCount ∧ firstPolicy = secondPolicy then
      .ok ⟨(), by rw [same.1, same.2]⟩
    else .error "The source send differs from its final peer trace."
  | .emitAck firstPolicy, .emitAck secondPolicy =>
    if same : firstPolicy = secondPolicy then .ok ⟨(), by rw [same]⟩
    else .error "The source ACK differs from its final peer trace."
  | _, _ => .error "The source output kind differs from its final peer trace."

structure ApplicationDelivery (report : M.Report input events) (peer : List AppStep) (actor : M.Actor) (step : AppStep) where
  receive : ReceiveAt report actor step
  service : ServiceAt receive
  lineage : Lineage report receive
  source : TCP.ApplicationTrace.OutputAt peer
  applicationSource : ∃ sourceActor sourceStep output origin,
    receive.receipt.served.ticket.value.produced = .application sourceActor sourceStep output origin ∧
      sourceActor = actor.other ∧ source.step = sourceStep ∧ source.output = output
  path : TCP.ApplicationTrace.BytePath source.output receive.received
  earlier : source.step.stamp < step.stamp

def applicationDelivery (report : M.Report input events) (peer : List AppStep) (actor : M.Actor) (step : AppStep) :
    Except String (ApplicationDelivery report peer actor step) := do
  let received ← receiveAt report actor step
  let service ← serviceAt received
  have lineage := service_lineage received service
  match production : received.receipt.served.ticket.value.produced with
  | .startup .. => throw "A startup copy cannot supply an application delivery history."
  | .application sourceActor sourceStep output origin =>
    let source ← TCP.ApplicationTrace.findOutput peer sourceStep.stamp
    if before : source.val.step.before = sourceStep.before then
      let event ← sameOutputEvent source.val.step sourceStep
      have sameStep := app_step_eq source.val.step sourceStep before event.property source.property
      have sameOutput : source.val.output = output := by
        have actual := origin_output source.val.origin
        rw [sameStep] at actual
        exact Option.some.inj (actual.symm.trans (origin_output origin))
      have sourceActorEq : sourceActor = actor.other := by
        have receiver := received.receipt.receiver
        have actorEq := received.receiver
        simp only [production, Check.CampusTCPModel.Produced.actor] at receiver
        cases sourceActor <;> cases actor <;> simp_all [Check.CampusTCPModel.Actor.other]
      have gateway : TCP.ApplicationTrace.BytePath output received.received := by
        rw [← received.same]
        simpa only [production, Check.CampusTCPModel.Produced.output] using received.receipt.bytePath
      have earlier : source.val.step.stamp < step.stamp := by
        have ordered := lineage.source_earlier
        simp only [production, Check.CampusTCPModel.Produced.time] at ordered
        have time := (deliver_origin received.joint.step received.service received.raw received.policy received.delivered
          received.receipt received.recorded).1.trans received.joint.time
        have sourceTime := source.property
        omega
      return ⟨received, service, lineage, source.val,
        ⟨sourceActor, sourceStep, output, origin, production, sourceActorEq, sameStep, sameOutput⟩,
        by rw [sameOutput]; exact gateway, earlier⟩
    else throw "The source state differs from its actual final peer operation."

inductive Receives (report : M.Report input events) (peer : List AppStep) (actor : M.Actor) : List AppStep → Type where
  | nil : Receives report peer actor []
  | receive (head : AppStep) (packet : PacketInput) (event : head.event = .receive packet)
      (delivery : ApplicationDelivery report peer actor head) (tail : Receives report peer actor rest) :
      Receives report peer actor (head :: rest)
  | other (head : AppStep) (absent : ∀ packet, head.event ≠ .receive packet)
      (tail : Receives report peer actor rest) : Receives report peer actor (head :: rest)

def receives (report : M.Report input events) (peer : List AppStep) (actor : M.Actor) :
    (steps : List AppStep) → Except String (Receives report peer actor steps)
  | [] => .ok .nil
  | head :: rest => do
    match event : head.event with
    | .receive packet =>
      let delivery ← applicationDelivery report peer actor head
      let tail ← receives report peer actor rest
      return .receive head packet event delivery tail
    | .write bytes =>
      let tail ← receives report peer actor rest
      return .other head (by intro packet same; rw [event] at same; cases same) tail
    | .send count policy =>
      let tail ← receives report peer actor rest
      return .other head (by intro packet same; rw [event] at same; cases same) tail
    | .read count =>
      let tail ← receives report peer actor rest
      return .other head (by intro packet same; rw [event] at same; cases same) tail
    | .emitAck policy =>
      let tail ← receives report peer actor rest
      return .other head (by intro packet same; rw [event] at same; cases same) tail

theorem Receives.delivered (value : Receives report peer actor steps) :
    ∀ step ∈ steps, ∀ packet, step.event = .receive packet →
      ∃ source : TCP.ApplicationTrace.OutputAt peer,
        source.step.stamp < step.stamp ∧ TCP.ApplicationTrace.BytePath source.output packet := by
  induction value with
  | nil => intro step member; simp at member
  | receive head packet event delivery tail ih =>
    intro step member received actual
    rcases List.mem_cons.mp member with rfl | member
    · have same : delivery.receive.received = received :=
        TCP.ApplicationTrace.Event.receive.inj (delivery.receive.event.symm.trans actual)
      exact ⟨delivery.source, delivery.earlier, by rw [← same]; exact delivery.path⟩
    · exact ih step member received actual
  | other head absent tail ih =>
    intro step member packet actual
    rcases List.mem_cons.mp member with rfl | member
    · exact False.elim (absent packet actual)
    · exact ih step member packet actual


inductive StartupKind where
  | syn | synAck | ack
  deriving Repr, BEq, DecidableEq

def startupKind : M.Produced active passive → Option StartupKind
  | .application .. => none
  | .startup step _ _ => match step.event with
    | .activeOpen .. => some .syn
    | .listenSyn .. => some .synAck
    | .synSentSynAck .. => some .ack
    | .synReceivedAck .. => none

structure StartupDelivery (report : M.Report input events) (time : Nat) (actor : M.Actor)
    (packet : PacketInput) (kind : StartupKind) where
  receive : DeliveryAt report time actor
  packet : receive.received = packet
  service : GatewayService receive
  lineage : GatewayLineage report receive
  sourceKind : startupKind receive.receipt.served.ticket.value.produced = some kind

def startupDelivery (report : M.Report input events) (time : Nat) (actor : M.Actor) (packet : PacketInput)
    (kind : StartupKind) : Except String (StartupDelivery report time actor packet kind) := do
  let delivery ← deliveryAt report time actor packet
  let service ← gatewayService delivery.val
  if sourceKind : startupKind delivery.val.receipt.served.ticket.value.produced = some kind then
    return ⟨delivery.val, delivery.property, service, gateway_lineage delivery.val service, sourceKind⟩
  else throw "The startup input names a different earlier control-output kind."

structure StartupHistory (report : M.Report input events)
    (complete : TCPHandshake.Completed input.active input.passive) where
  syn : StartupDelivery report complete.input.times.synReceived .server complete.certificate.syn.input .syn
  synAck : StartupDelivery report complete.input.times.synAckReceived .client complete.certificate.synAck.input .synAck
  ack : StartupDelivery report complete.input.times.ackReceived .server complete.certificate.ack.input .ack

def startupHistory (report : M.Report input events) (complete : TCPHandshake.Completed input.active input.passive) :
    Except String (StartupHistory report complete) := do
  let syn ← startupDelivery report complete.input.times.synReceived .server complete.certificate.syn.input .syn
  let synAck ← startupDelivery report complete.input.times.synAckReceived .client complete.certificate.synAck.input .synAck
  let ack ← startupDelivery report complete.input.times.ackReceived .server complete.certificate.ack.input .ack
  return ⟨syn, synAck, ack⟩


structure Assurance (report : M.Report input events) where
  compliant : report.compliant = true
  complete : TCPHandshake.Completed input.active input.passive
  endpoints : M.Applications complete
  selected : report.final.connection = .application complete endpoints
  startup : StartupHistory report complete
  clientReceives : Receives report endpoints.server.steps .client endpoints.client.steps
  serverReceives : Receives report endpoints.client.steps .server endpoints.server.steps
  clientSupported : endpoints.client.steps.all TCP.ApplicationTrace.Step.supported = true
  serverSupported : endpoints.server.steps.all TCP.ApplicationTrace.Step.supported = true
  clientEpoch : (endpoints.client.steps.flatMap TCP.ApplicationTrace.Step.emitted).length < TCP.Seq.halfSpace
  serverEpoch : (endpoints.server.steps.flatMap TCP.ApplicationTrace.Step.emitted).length < TCP.Seq.halfSpace
  quiet : TCP.HandshakeExchange.QuietBoundary complete.certificate endpoints.client.steps endpoints.server.steps

theorem Assurance.forward (value : Assurance report) :
    TCP.ApplicationTrace.DeliveryHistory value.endpoints.client.steps value.endpoints.server.steps :=
  ⟨value.endpoints.client.ordered, value.endpoints.server.ordered, value.serverReceives.delivered⟩

theorem Assurance.backward (value : Assurance report) :
    TCP.ApplicationTrace.DeliveryHistory value.endpoints.server.steps value.endpoints.client.steps :=
  ⟨value.endpoints.server.ordered, value.endpoints.client.ordered, value.clientReceives.delivered⟩

theorem Assurance.application_prefix (value : Assurance report) :
    value.endpoints.server.steps.flatMap TCP.ApplicationTrace.Step.readBytes <+:
        value.endpoints.client.steps.flatMap TCP.ApplicationTrace.Step.written ∧
      value.endpoints.client.steps.flatMap TCP.ApplicationTrace.Step.readBytes <+:
        value.endpoints.server.steps.flatMap TCP.ApplicationTrace.Step.written :=
  value.complete.certificate.application_prefix value.endpoints.client.chain value.endpoints.server.chain
    value.forward value.backward value.clientEpoch value.serverEpoch

theorem Assurance.with_environment (value : Assurance report)
    (environment : TCP.HandshakeExchange.Environment value.complete.certificate currentInstance)
    (clientInputs : ∀ step ∈ value.endpoints.client.steps, ∀ packet,
      step.event = .receive packet → currentInstance step.stamp packet)
    (serverInputs : ∀ step ∈ value.endpoints.server.steps, ∀ packet,
      step.event = .receive packet → currentInstance step.stamp packet) :
    TCP.HandshakeExchange.ApplicationAssurance value.complete.certificate currentInstance
      value.endpoints.client.steps value.endpoints.server.steps :=
  value.complete.certificate.startup_to_application value.endpoints.client.chain value.endpoints.server.chain
    value.forward value.backward value.clientEpoch value.serverEpoch environment value.quiet
    value.clientSupported value.serverSupported clientInputs serverInputs

def assure (report : M.Report input events) : Except String (Assurance report) := do
  if compliant : report.compliant = true then
    match selected : report.final.connection with
    | .startup .. => throw "The startup exchange is pending."
    | .application complete endpoints =>
      let startup ← startupHistory report complete
      let client ← receives report endpoints.server.steps .client endpoints.client.steps
      let server ← receives report endpoints.client.steps .server endpoints.server.steps
      if clientSupported : endpoints.client.steps.all TCP.ApplicationTrace.Step.supported = true then
        if serverSupported : endpoints.server.steps.all TCP.ApplicationTrace.Step.supported = true then
          if epoch : (endpoints.client.steps.flatMap TCP.ApplicationTrace.Step.emitted).length < TCP.Seq.halfSpace ∧
              (endpoints.server.steps.flatMap TCP.ApplicationTrace.Step.emitted).length < TCP.Seq.halfSpace then
            if quiet : (endpoints.client.steps.all (fun step => decide (complete.input.times.ackReceived < step.stamp)) &&
                endpoints.server.steps.all (fun step => decide (complete.input.times.ackReceived < step.stamp))) = true then
              have boundary : TCP.HandshakeExchange.QuietBoundary complete.certificate endpoints.client.steps endpoints.server.steps := by
                have parts : endpoints.client.steps.all (fun step => decide (complete.input.times.ackReceived < step.stamp)) = true ∧
                    endpoints.server.steps.all (fun step => decide (complete.input.times.ackReceived < step.stamp)) = true := by
                  simpa only [Bool.and_eq_true] using quiet
                constructor
                · simpa only [List.all_eq_true, decide_eq_true_eq] using parts.1
                · simpa only [List.all_eq_true, decide_eq_true_eq] using parts.2
              return ⟨compliant, complete, endpoints, selected, startup, client, server,
                clientSupported, serverSupported, epoch.1, epoch.2, boundary⟩
            else throw "The application trace does not have a quiet boundary after final ACK receipt."
          else throw "The application byte epoch reaches half the sequence space."
        else throw "The server application trace contains unsupported processing."
      else throw "The client application trace contains unsupported processing."
  else throw "The actual joint replay is not compliant."


theorem service_passed (report : M.Report input events) (compliant : report.compliant = true)
    (step : M.Step input) (member : step ∈ report.steps) (served : M.Served input)
    (present : step.result.service = some served) : served.passed = true := by
  obtain ⟨id, observed, completed, event, _, _, _, _⟩ := CampusTCPOrigins.service_origin step served present
  have actual := serve_origin step id observed event served present
  rw [← actual.choose_spec.2.2.2.2]
  exact report.step_passed compliant step member

theorem service_evidence_passed (report : M.Report input events) (compliant : report.compliant = true)
    (step : M.Step input) (member : step ∈ report.steps) (served : M.Served input)
    (present : step.result.service = some served) : served.evidence.passed = true := by
  have passed := service_passed report compliant step member served present
  simpa only [Check.CampusTCPModel.Served.passed, Bool.and_eq_true, and_assoc] using
    And.left (show served.evidence.passed = true ∧ served.routeMatched = true ∧ served.observed = true from by
      simpa only [Check.CampusTCPModel.Served.passed, Bool.and_eq_true, and_assoc] using passed)

theorem service_current_permission (report : M.Report input events) (compliant : report.compliant = true)
    (step : M.Step input) (member : step ∈ report.steps) (served : M.Served input)
    (present : step.result.service = some served) (emission : TCP.WireForwarding.Emission served.ticket.value.source.packet)
    (emitted : served.evidence.output = some emission) :
    ∃ processing, served.evidence.processing = some processing ∧
      ∃ requirement ∈ input.context.requirements, requirement.test.Holds processing.outcome.afterDestination ∧
        Session.Valid input.context.authentication.context
          (Check.SessionFirewall.stateAt input.context.authentication step.before.authentication).session input.application ∧
        EAPAuth.State.Ready (EAPSession.authContext input.context.authentication.context)
          (Check.SessionFirewall.stateAt input.context.authentication step.before.authentication).auth := by
  have passed := service_evidence_passed report compliant step member served present
  obtain ⟨processing, selected, requirement, source, matched, valid, ready⟩ := served.evidence.current_permission passed emission emitted
  obtain ⟨id, observed, completed, event, _, _, before, _⟩ := CampusTCPOrigins.service_origin step served present
  rw [input.scopes requirement source] at valid
  rw [before] at valid ready
  exact ⟨processing, selected, requirement, source, matched, valid, ready⟩

theorem service_ingress_permission (report : M.Report input events) (compliant : report.compliant = true)
    (step : M.Step input) (member : step ∈ report.steps) (served : M.Served input)
    (present : step.result.service = some served) (emission : TCP.WireForwarding.Emission served.ticket.value.source.packet)
    (emitted : served.evidence.output = some emission) :
    ∃ attachment ∈ step.before.attachments.map (·.value),
      IngressAttachment.allows (CampusTCPService.current input.context (Check.CampusTCPModel.beforeService input step.before))
        attachment ⟨served.ticket.value.ingress, served.ticket.value.source.packet.header⟩ = true ∧
      Session.Valid input.context.authentication.context
        (Check.SessionFirewall.stateAt input.context.authentication step.before.authentication).session attachment.scope ∧
      EAPAuth.State.Ready (EAPSession.authContext input.context.authentication.context)
        (Check.SessionFirewall.stateAt input.context.authentication step.before.authentication).auth ∧
      served.ticket.value.ingress = attachment.ingress ∧ attachment.origin.principal = input.context.authentication.context.consumer := by
  have passed := service_evidence_passed report compliant step member served present
  have permission := served.evidence.ingress_permission passed emission emitted
  obtain ⟨id, observed, completed, event, _, _, before, _⟩ := CampusTCPOrigins.service_origin step served present
  rw [before] at permission
  exact permission

theorem service_route (report : M.Report input events) (compliant : report.compliant = true)
    (step : M.Step input) (member : step ∈ report.steps) (served : M.Served input)
    (present : step.result.service = some served) (emission : TCP.WireForwarding.Emission served.ticket.value.source.packet)
    (emitted : served.evidence.output = some emission) :
    ∃ processing, served.evidence.processing = some processing ∧
      processing.outcome.nextHop = some served.ticket.value.produced.actor.nextHop := by
  obtain ⟨processing, selected, output⟩ := served.evidence.processed_of_output emission emitted
  have passed := service_passed report compliant step member served present
  have route : served.routeMatched = true := by
    have parts : (served.evidence.passed = true ∧ served.routeMatched = true) ∧ served.observed = true := by
      simpa only [Check.CampusTCPModel.Served.passed, Bool.and_eq_true] using passed
    exact parts.1.2
  simp only [Check.CampusTCPModel.Served.routeMatched, selected, output, decide_eq_true_eq] at route
  exact ⟨processing, selected, route⟩

theorem service_topology (report : M.Report input events) (compliant : report.compliant = true)
    (step : M.Step input) (member : step ∈ report.steps) (served : M.Served input)
    (present : step.result.service = some served) (emission : TCP.WireForwarding.Emission served.ticket.value.source.packet)
    (emitted : served.evidence.output = some emission) :
    (∃ processing, served.evidence.processing = some processing ∧
      processing.outcome.nextHop = some served.ticket.value.produced.actor.nextHop) ∧
      Network.Walk (Examples.CampusDirect.network input.context.authentication.context
        (Check.SessionFirewall.stateAt input.context.authentication step.before.authentication) input.application false)
        (Examples.CampusDirect.source served.ticket.value.produced.actor.direction)
        (Examples.CampusDirect.target served.ticket.value.produced.actor.direction)
        (Examples.CampusDirect.routeTrace .primary served.ticket.value.produced.actor.direction) ∧
      (Examples.CampusDirect.network input.context.authentication.context
        (Check.SessionFirewall.stateAt input.context.authentication step.before.authentication) input.application false).Isolated
        Examples.CampusDirect.endpoints Examples.CampusDirect.managers := by
  obtain ⟨processing, selected, requirement, source, matched, valid, ready⟩ :=
    service_current_permission report compliant step member served present emission emitted
  have permitted := (Session.permits_iff _ _ _).mpr valid
  exact ⟨service_route report compliant step member served present emission emitted,
    Examples.CampusDirect.selected_route _ _ _ false .primary _ permitted (.inl rfl),
    Examples.CampusDirect.management_isolated _ _ _ false⟩

theorem service_output_none_of_unauthorized (report : M.Report input events) (compliant : report.compliant = true)
    (step : M.Step input) (member : step ∈ report.steps) (served : M.Served input)
    (present : step.result.service = some served)
    (unauthorized : (Check.SessionFirewall.stateAt input.context.authentication step.before.authentication).auth.authorized = false) :
    served.evidence.output = none := by
  have passed := service_evidence_passed report compliant step member served present
  apply served.evidence.output_none_of_unauthorized passed
  obtain ⟨id, observed, completed, event, _, _, before, _⟩ := CampusTCPOrigins.service_origin step served present
  rw [before]
  exact unauthorized

theorem stale_permit_not_compliant (report : M.Report input events) (step : M.Step input)
    (member : step ∈ report.steps) (served : M.Served input) (present : step.result.service = some served)
    (emission : TCP.WireForwarding.Emission served.ticket.value.source.packet) (emitted : served.evidence.output = some emission)
    (unauthorized : (Check.SessionFirewall.stateAt input.context.authentication step.before.authentication).auth.authorized = false) :
    report.compliant = false := by
  cases passed : report.compliant with
  | false => rfl
  | true =>
    have none := service_output_none_of_unauthorized report passed step member served present unauthorized
    rw [none] at emitted
    cases emitted

end Netlib.Check.CampusTCPFacts
