import Netlib.Check.CampusTCPFacts
import Netlib.Check.CampusTCPStartupOrigins
import Netlib.Check.TCPHandshakeRecoveryInvariant
import Netlib.Check.TCPHandshakeRecoveryApplicationHistory
import Netlib.Check.TCPHandshakeRecoveryReceiptFacts

/-!
# Recovery controls in the campus receipt history

Recovery event stamps identify control occurrences.
Campus output and service positions remain separate references.
-/

namespace Netlib.Check.CampusTCPRecoveryReceipts

open CampusTCPModel

namespace C
export TCPHandshakeRecovery (Step State Emission Receipt Event)
end C

variable {input : Input}
variable {before : State input} {event : C.Event} {effect : Effect input}
variable {control : C.Step input.active input.passive}

inductive RecoveryEvent : Event → C.Event → Prop where
  | opened (remote policy) : RecoveryEvent (.openRecovering remote policy) (.activeOpen remote policy)
  | clock (actor : Actor) (millis) : RecoveryEvent (.startupClock actor millis) (.advanceClock actor.recoverySide millis)
  | timeout (actor : Actor) (generation policy) :
      RecoveryEvent (.startupTimeout actor generation policy) (.timeout actor.recoverySide generation policy)
  | delivered (service source bytes policy) :
      RecoveryEvent (.deliver service bytes policy) (.receive source bytes .rewrite policy)

private structure RunFields (before : State input) (event : C.Event) (effect : Effect input)
    (control : C.Step input.active input.passive) : Prop where
  index : control.index = before.time
  eventEq : control.event = event
  connected : before.connection = .recovering control.before
  after : effect.state.connection = .recovering control.result.state
  application : effect.application = control.result.application.map (fun pair => (Actor.ofRecovery pair.1, pair.2))
  receipt : effect.receipt = none
  output : ∀ produced, effect.output = some produced →
    ∃ emission, ∃ present : control.result.output = some emission, produced = .recovery control emission present

private theorem run_fields (computed : runRecovery input before event = .ok effect)
    (recorded : effect.recovery = some control) : RunFields before event effect control := by
  unfold runRecovery at computed
  split at computed
  · cases computed
    cases recorded
  · cases computed
    cases recorded
  · split at computed
    · cases computed
    · rename_i current connected result evaluated
      cases result with
      | mk state decision output receipt application =>
        cases output <;> simp only [pure, Except.pure, Except.ok.injEq] at computed
        all_goals
          subst effect
          dsimp only at recorded
          cases recorded
          refine ⟨rfl, rfl, connected, rfl, rfl, rfl, ?_⟩
          intro produced selected
          cases selected <;> exact ⟨_, rfl, rfl⟩

private theorem startup_none (computed : startup input before joint = .ok effect) : effect.recovery = none := by
  unfold startup at computed
  repeat' first
    | (solve | cases computed; rfl)
    | (solve | cases computed)
    | (split at computed)
    | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)

private theorem application_none (computed : applyApplication input before actor applied = .ok effect) : effect.recovery = none := by
  unfold applyApplication at computed
  repeat' first
    | (solve | cases computed; rfl)
    | (solve | cases computed)
    | (split at computed)
    | (dsimp only [parsed, Except.mapError, bind, Except.bind, pure, Except.pure] at computed)

private theorem get_lookup (computed : CampusTCPModel.get values index message = .ok selected) : values[index]? = some selected := by
  unfold CampusTCPModel.get at computed
  split at computed
  · cases computed
  · cases computed
    assumption

private theorem input_bytes {packet : Protocol.TCP.EstablishedReceive.Input}
    (computed : Protocol.TCP.EstablishedReceive.input bytes = .ok packet) : packet.bytes = bytes := by
  unfold Protocol.TCP.EstablishedReceive.input at computed
  split at computed <;> cases computed
  rfl

private theorem parsed_input_bytes {packet : Protocol.TCP.EstablishedReceive.Input}
    (computed : parsed (Protocol.TCP.EstablishedReceive.input bytes) = .ok packet) : packet.bytes = bytes := by
  cases decoded : Protocol.TCP.EstablishedReceive.input bytes with
  | error reason => simp [parsed, decoded, Except.mapError] at computed
  | ok received =>
    simp only [parsed, decoded, Except.mapError, Except.ok.injEq] at computed
    subst packet
    exact input_bytes decoded

private theorem input_unique (first second : Protocol.TCP.EstablishedReceive.Input)
    (same : first.bytes = second.bytes) : first = second := by
  cases first with
  | mk bytes packet checked =>
    cases second with
    | mk other decoded verified =>
      dsimp only at same
      subst other
      have equal : packet = decoded := Except.ok.inj (checked.symm.trans verified)
      subst decoded
      rfl

private structure DeliveryFields (before : State input) (service : Nat) (bytes : List UInt8) (policy : Bool)
    (effect : Effect input) (control : C.Step input.active input.passive) where
  receipt : CampusTCPModel.Receipt input
  recorded : effect.receipt = some receipt
  raw : receipt.received.bytes = bytes
  serviceAt : before.services[service]? = some receipt.served
  sourceStep : C.Step input.active input.passive
  occurrence : C.Emission
  present : sourceStep.result.output = some occurrence
  production : receipt.served.ticket.value.produced = .recovery sourceStep occurrence present
  event : control.event = .receive occurrence.index bytes .rewrite policy
  stamp : control.index = before.time
  beforeEq : before.connection = .recovering control.before
  afterEq : effect.state.connection = .recovering control.result.state
  receiptEq : receipt.recovery = control.result.receipt
  application : effect.application = control.result.application.map (fun pair => (Actor.ofRecovery pair.1, pair.2))
  localRecord : receipt.application = effect.application.map (·.2)

private theorem delivery_fields (computed : processCore input before (.deliver service bytes policy) = .ok effect)
    (recorded : effect.recovery = some control) : Nonempty (DeliveryFields before service bytes policy effect control) := by
  simp only [processCore] at computed
  repeat' first
    | (solve | cases computed)
    | (split at computed)
    | (dsimp only [CampusTCPModel.get, parsed, Except.mapError, bind, Except.bind, pure, Except.pure] at computed)
  all_goals
    simp only [Except.ok.injEq] at computed
    subst effect
    dsimp only at recorded
    first
      | (solve | have absent := startup_none (input := input) (before := before) (by assumption); rw [absent] at recorded; cases recorded)
      | (solve | have absent := application_none (input := input) (before := before) (by assumption); rw [absent] at recorded; cases recorded)
      | (solve |
        rename_i sourceValue sourceStep occurrence present production resultCase result runComputed
        have fields := run_fields runComputed recorded
        refine ⟨⟨_, rfl, ?_, ?_, sourceStep, occurrence, present, production,
          fields.eventEq, fields.index, fields.connected, fields.after, ?_, fields.application, rfl⟩⟩
        · exact parsed_input_bytes (bytes := bytes) (by assumption)
        · exact get_lookup (values := before.services) (index := service)
            (message := "The gateway service reference is missing.") (by assumption)
        · rw [recorded]
          rfl)

structure Delivery (joint : Step input) (control : C.Step input.active input.passive) where
  service : Nat
  bytes : List UInt8
  policy : Bool
  event : joint.event = .deliver service bytes policy
  receipt : CampusTCPModel.Receipt input
  recorded : joint.result.receipt = some receipt
  serviceAt : joint.before.services[service]? = some receipt.served
  sourceStep : C.Step input.active input.passive
  occurrence : C.Emission
  present : sourceStep.result.output = some occurrence
  production : receipt.served.ticket.value.produced = .recovery sourceStep occurrence present
  controlEvent : control.event = .receive occurrence.index bytes .rewrite policy
  stamp : control.index = joint.before.time
  beforeEq : joint.before.connection = .recovering control.before
  afterEq : joint.result.state.connection = .recovering control.result.state
  application : joint.result.application = control.result.application.map (fun pair => (Actor.ofRecovery pair.1, pair.2))
  received : C.Receipt
  receivedAt : control.result.receipt = some received
  receiptEq : receipt.recovery = some received
  selected : control.before.source occurrence.index = some received.source
  sourceIndex : received.source.index = occurrence.index
  raw : received.delivery.input.bytes = bytes
  sameInput : receipt.received = received.delivery.input
  localRecord : receipt.application = joint.result.application.map (·.2)

theorem Step.recovery_delivery (joint : Step input) (recorded : joint.result.recovery = some control)
    (event : joint.event = .deliver service bytes policy) : Nonempty (Delivery joint control) := by
  obtain ⟨effect, custody, computed, result⟩ := joint.processed
  have present : effect.recovery = some control := by simpa only [result] using recorded
  rw [event] at computed
  obtain ⟨fields⟩ := delivery_fields computed present
  obtain ⟨received, receivedAt, selected, index, raw, _⟩ := control.receive_receipt fields.event
  exact ⟨⟨service, bytes, policy, event, fields.receipt, by simpa only [result] using fields.recorded,
    fields.serviceAt, fields.sourceStep, fields.occurrence, fields.present, fields.production, fields.event, fields.stamp,
    fields.beforeEq, by simpa only [result] using fields.afterEq, by simpa only [result] using fields.application,
    received, receivedAt, fields.receiptEq.trans receivedAt, selected, index, raw,
    input_unique _ _ (fields.raw.trans raw.symm), by simpa only [result] using fields.localRecord⟩⟩

structure LocalAck (delivery : Delivery joint control) (actor : Actor) (operation : T.Step) where
  side : TCPHandshakeRecovery.Side
  recorded : control.result.application = some (side, operation)
  actorEq : actor = Actor.ofRecovery side
  receiver : delivery.received.actor = side
  ack : TCPHandshakeRecovery.AckOperation delivery.receipt.received joint.before.time operation
  localRecord : delivery.receipt.application = some operation

theorem Delivery.local_ack (delivery : Delivery joint control)
    (recorded : joint.result.application = some (actor, operation)) : Nonempty (LocalAck delivery actor operation) := by
  have mapped := delivery.application.symm.trans recorded
  obtain ⟨⟨side, applied⟩, selected, same⟩ := Option.map_eq_some_iff.mp mapped
  have actorEq : Actor.ofRecovery side = actor := congrArg Prod.fst same
  have sameOperation : applied = operation := congrArg Prod.snd same
  subst applied
  obtain ⟨receipt, present, receiver, ack⟩ := control.application_receipt selected
  have equal : receipt = delivery.received := Option.some.inj (present.symm.trans delivery.receivedAt)
  subst receipt
  refine ⟨⟨side, selected, actorEq.symm, receiver, ?_, ?_⟩⟩
  · rw [delivery.sameInput, ← delivery.stamp]
    exact ack
  · rw [delivery.localRecord, recorded]
    rfl

private def Recorded (effect : Effect input) : Prop :=
  ∀ actual output present, effect.output = some (.recovery actual output present) → effect.recovery = some actual

private theorem startup_recorded (computed : startup input before startupEvent = .ok effect) : Recorded effect := by
  unfold startup at computed
  split at computed
  · cases computed
    intro actual output present selected
    cases selected
  · cases computed
    intro actual output present selected
    cases selected
  · split at computed
    · cases computed
    · rename_i result evaluated
      cases result with
      | mk state decision decoded output delivery =>
        cases output <;> simp only [pure, Except.pure, Except.ok.injEq] at computed
        all_goals
          subst effect
          intro actual output present selected
          cases selected

private theorem application_recorded (computed : applyApplication input before actor applicationEvent = .ok effect) : Recorded effect := by
  unfold applyApplication at computed
  repeat' first
    | (solve | cases computed; intro actual output present selected; cases selected)
    | (solve | cases computed)
    | (split at computed)
    | (dsimp only [parsed, Except.mapError, bind, Except.bind, pure, Except.pure] at computed)

private theorem recovery_recorded (computed : runRecovery input before event = .ok effect) : Recorded effect := by
  unfold runRecovery at computed
  split at computed
  · cases computed
    intro actual output present selected
    cases selected
  · cases computed
    intro actual output present selected
    cases selected
  · split at computed
    · cases computed
    · rename_i current connected result evaluated
      cases result with
      | mk state decision output receipt application =>
        cases output <;> simp only [pure, Except.pure, Except.ok.injEq] at computed
        all_goals
          subst effect
          intro actual output present selected
          cases selected <;> rfl

private theorem openRecovery_recorded (computed : openRecovering input before remote policy = .ok effect) : Recorded effect := by
  unfold openRecovering at computed
  repeat' first
    | (solve | exact recovery_recorded computed)
    | (solve | cases computed; intro actual output present selected; cases selected)
    | (solve | cases computed)
    | (split at computed)
    | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)

private theorem finish_recorded (computed : finishStartup input before = .ok effect) : Recorded effect := by
  unfold finishStartup at computed
  repeat' first
    | (solve | cases computed; intro actual output present selected; cases selected)
    | (solve | cases computed)
    | (split at computed)
    | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)

private theorem enableAck_recorded (computed : enableAck input before actor = .ok effect) : Recorded effect := by
  unfold enableAck at computed
  repeat' first
    | (solve | exact application_recorded computed)
    | (solve | cases computed)
    | (split at computed)
    | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)

private theorem enableStartup_recorded (computed : enableStartupRecovery input before actor = .ok effect) : Recorded effect := by
  unfold enableStartupRecovery at computed
  split at computed
  · cases computed
    intro actual output present selected
    cases selected
  · exact application_recorded computed

private theorem process_recorded (computed : processCore input before jointEvent = .ok effect) : Recorded effect := by
  cases jointEvent with
  | «open» remote policy => exact startup_recorded computed
  | openRecovering remote policy => exact openRecovery_recorded computed
  | startupClock actor millis | startupTimeout actor generation policy => exact recovery_recorded computed
  | finishStartup => exact finish_recorded computed
  | write actor bytes | send actor count policy | read actor count | emitAck actor policy
  | enableRecovery actor | advanceClock actor millis | timeout actor policy | dispatchAck actor policy =>
    exact application_recorded computed
  | enableAck actor => exact enableAck_recorded computed
  | enableStartupRecovery actor => exact enableStartup_recorded computed
  | copyPacket id | dropPacket id =>
    cases computed
    intro actual output present selected
    cases selected
  | authentication index =>
    simp only [processCore] at computed
    repeat' first
      | (solve | cases computed; intro actual output present selected; cases selected)
      | (solve | cases computed)
      | (split at computed)
      | (dsimp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at computed)
  | install id | stage id | installGuard id | installAt gateway id | stageAt gateway id | installGuardAt gateway id =>
    simp only [processCore, installConfiguration, stageAttachment, installIngress] at computed
    repeat' first
      | (solve | cases computed; intro actual output present selected; cases selected)
      | (solve | cases computed)
      | (split at computed)
      | (dsimp only [parsed, Except.mapError, bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at computed)
  | pause | stageCheckpoint | installCheckpoint ns | switchRoute actor gateway | fencePrimary | resume =>
    simp only [processCore, transferControl] at computed
    repeat' first
      | (solve | cases computed; intro actual output present selected; cases selected)
      | (solve | cases computed)
      | (split at computed)
      | (dsimp only [Except.mapError, bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at computed)
  | assign index ingress | serve id observed =>
    simp only [processCore] at computed
    repeat' first
      | (solve | cases computed; intro actual output present selected; cases selected)
      | (solve | cases computed)
      | (split at computed)
      | (dsimp only [CampusTCPModel.get, Except.mapError, bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at computed)
  | deliver index bytes policy =>
    simp only [processCore] at computed
    repeat' first
      | (solve | cases computed; have fields := startup_recorded (input := input) (before := before) (by assumption); exact fields)
      | (solve | cases computed; have fields := application_recorded (input := input) (before := before) (by assumption); exact fields)
      | (solve | cases computed; have fields := recovery_recorded (input := input) (before := before) (by assumption); exact fields)
      | (solve | cases computed)
      | (split at computed)
      | (dsimp only [CampusTCPModel.get, parsed, Except.mapError, bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at computed)

theorem Step.recovery_output_recorded (joint : Step input) (actual : C.Step input.active input.passive)
    (output : C.Emission) (present : actual.result.output = some output)
    (selected : joint.result.output = some (.recovery actual output present)) : joint.result.recovery = some actual := by
  obtain ⟨effect, custody, computed, result⟩ := joint.processed
  have emitted : effect.output = some (.recovery actual output present) := by simpa only [result] using selected
  simpa only [result] using process_recorded computed actual output present emitted

private theorem time_before (trace : Trace input initial selected steps final remaining) :
    ∀ actual ∈ steps, initial.time ≤ actual.before.time := by
  induction trace with
  | done => intro actual member; cases member
  | stop head blocked tail =>
    intro actual member
    have same := List.mem_singleton.mp member
    subst actual
    exact Nat.le_refl _
  | next head supported rest ih =>
    intro actual member
    rcases List.mem_cons.mp member with same | member
    · subst actual; exact Nat.le_refl _
    · have bound := ih actual member
      rw [head.clock] at bound
      omega

private theorem time_order (trace : Trace input initial selected steps final remaining) :
    steps.Pairwise (fun a b => a.before.time < b.before.time) := by
  induction trace with
  | done => exact .nil
  | stop => simp
  | next head supported rest ih =>
    refine .cons ?_ ih
    intro actual member
    have bound := time_before rest actual member
    rw [head.clock] at bound
    omega

private theorem prior_member (trace : Trace input initial selected steps final remaining)
    (history : steps = prior ++ joint :: later) (member : producer ∈ steps)
    (earlier : producer.before.time < joint.before.time) : producer ∈ prior := by
  have ordered := time_order trace
  rw [history] at member ordered
  rcases List.mem_append.mp member with member | member
  · exact member
  · rcases List.mem_cons.mp member with same | member
    · subst producer; omega
    · have suffix := (List.pairwise_append.mp ordered).2.1
      have bound := (List.pairwise_cons.mp suffix).1 producer member
      omega

def Delivery.at (delivery : Delivery joint control) (report : Report input events) (member : joint ∈ report.steps) :
    CampusTCPFacts.DeliveryAt report joint.before.time delivery.receipt.actor :=
  ⟨⟨joint, member, rfl⟩, delivery.service, delivery.bytes, delivery.policy, delivery.event,
    delivery.receipt, delivery.recorded, delivery.receipt.received, rfl, rfl⟩

structure Source (report : Report input events) (delivery : Delivery joint control) where
  producer : Step input
  producerMember : producer ∈ report.steps
  produced : producer.result.output = some (.recovery delivery.sourceStep delivery.occurrence delivery.present)
  recorded : producer.result.recovery = some delivery.sourceStep
  earlier : producer.before.time < joint.before.time
  assignment : Step input
  assignmentMember : assignment ∈ report.steps
  outputIndex : Nat
  ingress : I.InterfaceRef
  assigned : assignment.event = .assign outputIndex ingress
  lookup : assignment.before.outputs[outputIndex]? = some delivery.receipt.served.ticket.value.produced
  sourceEq : delivery.received.source = delivery.occurrence

theorem Delivery.report_source (delivery : Delivery joint control) (report : Report input events)
    (member : joint ∈ report.steps) : Nonempty (Source report delivery) := by
  let gatewayDelivery := delivery.at report member
  obtain ⟨service⟩ := CampusTCPStartupOrigins.DeliveryAt.service_exists gatewayDelivery
  obtain ⟨producer, assignment, outputIndex, ingress, producerMember, assignmentMember, produced,
      assigned, lookup, _, _, first, second, third⟩ := CampusTCPFacts.gateway_lineage gatewayDelivery service
  have output : producer.result.output = some (.recovery delivery.sourceStep delivery.occurrence delivery.present) := by
    rw [← delivery.production]
    exact produced
  have recorded := Step.recovery_output_recorded producer delivery.sourceStep delivery.occurrence delivery.present output
  have receiptTime := (CampusTCPFacts.deliver_origin joint delivery.service delivery.bytes delivery.policy
    delivery.event delivery.receipt delivery.recorded).1
  have earlier : producer.before.time < joint.before.time := by
    change producer.before.time < assignment.before.time at first
    change assignment.before.time < delivery.receipt.served.time at second
    change delivery.receipt.served.time < delivery.receipt.time at third
    omega
  obtain ⟨prior, later, history, preceding, _, _⟩ := CampusTCPFacts.step_origin report joint member
  have retained := prior_member report.trace history producerMember earlier
  let beforeReport : Report input (prior.map (·.event)) := ⟨joint.before, prior, [], preceding⟩
  have projected := CampusTCPRecoveryStartupOrigins.Report.recovery_trace beforeReport delivery.beforeEq
  have occurrenceMember : delivery.occurrence ∈ control.before.emissions := by
    rw [projected.emissions]
    change delivery.occurrence ∈ [] ++ (prior.filterMap (·.result.recovery)).filterMap (·.result.output)
    exact List.mem_append_right _ (List.mem_filterMap.mpr
      ⟨delivery.sourceStep, List.mem_filterMap.mpr ⟨producer, retained, recorded⟩, delivery.present⟩)
  have found := (projected.history TCPHandshakeRecovery.History.initial).source_of_member occurrenceMember
  have sourceEq := Option.some.inj (delivery.selected.symm.trans found)
  exact ⟨⟨producer, producerMember, output, recorded, earlier, assignment, assignmentMember,
    outputIndex, ingress, assigned, lookup, sourceEq⟩⟩

theorem Source.receiver (source : Source report delivery) :
    delivery.receipt.actor = Actor.ofRecovery delivery.received.actor := by
  rw [delivery.receipt.receiver, delivery.production]
  simp only [Produced.actor, TCPHandshakeRecovery.Receipt.actor, source.sourceEq]
  cases delivery.occurrence.actor <;> rfl

theorem Source.local_actor (source : Source report delivery) (ack : LocalAck delivery actor operation) :
    delivery.receipt.actor = actor := by
  rw [source.receiver, ack.receiver]
  exact ack.actorEq.symm

private theorem stage_recovering (connection : Connection active passive)
    (same : CampusTCPRecoveryStartupOrigins.stage connection = .recovering current) : connection = .recovering current := by
  cases connection with
  | startup => cases same
  | application => cases same
  | recovering selected => cases same; rfl

private theorem stage_idle (connection : Connection active passive)
    (same : CampusTCPRecoveryStartupOrigins.stage connection = .ordinary .idle) :
    ∃ pending, connection = .startup .idle pending := by
  cases connection with
  | recovering => cases same
  | application => cases same
  | startup selected pending =>
    cases selected <;> cases same
    exact ⟨_, rfl⟩

theorem Step.recovery_state (joint : Step input) (recorded : joint.result.recovery = some control) :
    control.index = joint.before.time ∧
      (joint.before.connection = .recovering control.before ∨
        ∃ pending, joint.before.connection = .startup .idle pending ∧ control.before = .initial) ∧
      joint.result.state.connection = .recovering control.result.state := by
  cases CampusTCPRecoveryStartupOrigins.Step.linked joint with
  | quiet ordinary absent same | ordinary selected ordinary absent prior after stamp pending supported
  | drain archive ordinary absent event prior after retained stamp => rw [absent] at recorded; cases recorded
  | recovery selected present ordinary prior after stamp =>
    have equal := Option.some.inj (present.symm.trans recorded)
    subst selected
    refine ⟨stamp, ?_, stage_recovering _ after⟩
    rcases prior with current | ⟨idle, seeded⟩
    · exact Or.inl (stage_recovering _ current)
    · obtain ⟨pending, connected⟩ := stage_idle _ idle
      exact Or.inr ⟨pending, connected, seeded⟩

theorem Step.recovery_clock (joint : Step input) (recorded : joint.result.recovery = some control)
    (event : joint.event = .startupClock actor millis) : control.event = .advanceClock actor.recoverySide millis := by
  obtain ⟨effect, custody, computed, result⟩ := joint.processed
  have present : effect.recovery = some control := by simpa only [result] using recorded
  rw [event] at computed
  exact (run_fields computed present).eventEq

theorem Step.recovery_timeout (joint : Step input) (recorded : joint.result.recovery = some control)
    (event : joint.event = .startupTimeout actor generation policy) :
    control.event = .timeout actor.recoverySide generation policy := by
  obtain ⟨effect, custody, computed, result⟩ := joint.processed
  have present : effect.recovery = some control := by simpa only [result] using recorded
  rw [event] at computed
  exact (run_fields computed present).eventEq

private theorem open_event (computed : openRecovering input before remote policy = .ok effect)
    (recorded : effect.recovery = some control) : control.event = .activeOpen remote policy := by
  unfold openRecovering at computed
  repeat' first
    | (solve |
      exact (run_fields (before := { before with connection := .recovering .initial })
        (event := .activeOpen remote policy) computed recorded).eventEq)
    | (solve | cases computed; cases recorded)
    | (solve | cases computed)
    | (split at computed)
    | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)

theorem Step.recovery_open (joint : Step input) (recorded : joint.result.recovery = some control)
    (event : joint.event = .openRecovering remote policy) : control.event = .activeOpen remote policy := by
  obtain ⟨effect, custody, computed, result⟩ := joint.processed
  have present : effect.recovery = some control := by simpa only [result] using recorded
  rw [event] at computed
  exact open_event computed present

theorem Delivery.event_relation (delivery : Delivery joint control) : RecoveryEvent joint.event control.event := by
  rw [delivery.event, delivery.controlEvent]
  exact .delivered _ _ _ _

end Netlib.Check.CampusTCPRecoveryReceipts
