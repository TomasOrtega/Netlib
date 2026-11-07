import Netlib.Check.CampusTCPRecoveryRoundEvidence
import Netlib.Check.CampusTCPGapFacts
import Netlib.Check.CampusTCPRoundOrigins
import Netlib.Check.CampusTCPApplicationHistory
import Netlib.Check.CampusTCPApplicationProductionFacts
import Netlib.Check.CampusTCPGapPayloadFacts

namespace Netlib.Check.CampusTCPRecoveryRoundOrigins

open Protocol.TCP CampusTCPModel CampusTCPEnabled CampusTCPRoundStart
open CampusTCPRoundPhaseHistory (connectionSteps)

variable {input : Input}

def localSteps (application : Option (Actor × T.Step)) (actor : Actor) : List T.Step :=
  match application with
  | some (selected, operation) => if selected = actor then [operation] else []
  | none => []

theorem Step.application_history (actual : Step input) (actor : Actor) :
    connectionSteps actual.result.state.connection actor =
      connectionSteps actual.before.connection actor ++ localSteps actual.result.application actor :=
  CampusTCPApplicationHistory.Step.application_history actual actor

theorem mem_localSteps (application : Option (Actor × T.Step)) (actor : Actor) (operation : T.Step) :
    operation ∈ localSteps application actor ↔ application = some (actor, operation) := by
  cases application with
  | none => simp [localSteps]
  | some pair =>
    rcases pair with ⟨selected, actual⟩
    cases selected <;> cases actor <;> simp [localSteps, eq_comm]

theorem Trace.application_prefix (trace : Trace input before events steps after remaining) (actor : Actor) :
    connectionSteps before.connection actor <+: connectionSteps after.connection actor := by
  induction trace with
  | done state => exact List.prefix_refl _
  | stop head blocked rest => rw [Step.application_history head]; exact List.prefix_append _ _
  | next head supported rest ih =>
    apply List.IsPrefix.trans _ ih
    rw [Step.application_history head]
    exact List.prefix_append _ _

theorem Trace.application_origin (trace : Trace input before events steps after remaining) (actor : Actor)
    (operation : T.Step) (member : operation ∈ connectionSteps after.connection actor) :
    operation ∈ connectionSteps before.connection actor ∨
      ∃ actual ∈ steps, actual.result.application = some (actor, operation) := by
  induction trace with
  | done state => exact .inl member
  | stop head blocked rest =>
    rw [Step.application_history head] at member
    rcases List.mem_append.mp member with old | fresh
    · exact .inl old
    · exact .inr ⟨head, List.mem_cons_self, (mem_localSteps _ _ _).mp fresh⟩
  | next head supported rest ih =>
    rcases ih member with member | later
    · rw [Step.application_history head] at member
      rcases List.mem_append.mp member with old | fresh
      · exact .inl old
      · exact .inr ⟨head, List.mem_cons_self, (mem_localSteps _ _ _).mp fresh⟩
    · obtain ⟨actual, inside, recorded⟩ := later
      exact .inr ⟨actual, List.mem_cons_of_mem _ inside, recorded⟩

theorem Trace.application_member (trace : Trace input before events steps after remaining)
    (actual : Step input) (member : actual ∈ steps) (actor : Actor) (operation : T.Step)
    (recorded : actual.result.application = some (actor, operation)) : operation ∈ connectionSteps after.connection actor := by
  induction trace with
  | done state => simp at member
  | stop head blocked rest =>
    have same : actual = head := by simpa using member
    subst actual
    rw [Step.application_history head]
    exact List.mem_append_right _ ((mem_localSteps _ _ _).mpr recorded)
  | next head supported rest ih =>
    rcases List.mem_cons.mp member with same | later
    · subst actual
      apply (Trace.application_prefix rest actor).subset
      rw [Step.application_history head]
      exact List.mem_append_right _ ((mem_localSteps _ _ _).mpr recorded)
    · exact ih later

theorem Report.application_origin (report : Report input events) (actor : Actor) (operation : T.Step)
    (member : operation ∈ connectionSteps report.final.connection actor) :
    ∃ actual ∈ report.steps, actual.result.application = some (actor, operation) := by
  rcases Trace.application_origin report.trace actor operation member with old | created
  · simp only [Input.initial, connectionSteps, List.not_mem_nil] at old
  · exact created

theorem Report.application_member (report : Report input events) (actual : Step input) (member : actual ∈ report.steps)
    (actor : Actor) (operation : T.Step) (recorded : actual.result.application = some (actor, operation)) :
    operation ∈ connectionSteps report.final.connection actor :=
  Trace.application_member report.trace actual member actor operation recorded

theorem Step.output_application (actual : Step input) (actor : Actor) (operation : T.Step) (packet : EstablishedReceive.Input)
    (origin : ApplicationTrace.OutputOrigin operation packet)
    (output : actual.result.output = some (.application actor operation packet origin)) :
    actual.result.application = some (actor, operation) :=
  CampusTCPApplicationProductionFacts.Step.application_output_recorded actual actor operation packet origin output

theorem Step.receive_stamp (actual : Step input) (actor : Actor) (operation : T.Step)
    (recorded : actual.result.application = some (actor, operation)) (packet : EstablishedReceive.Input)
    (received : operation.event = .receive packet) : operation.stamp = actual.before.time := by
  obtain ⟨cases⟩ := CampusTCPReceiveCases.Step.receive_cases actual actor operation recorded packet received
  cases cases with
  | application value => exact value.stamp
  | recovery control present delivery ack same => exact ack.ack.2.2.2.2.2.2.2.2

theorem Step.payload_receive_origin (actual : Step input) (actor : Actor) (operation : T.Step)
    (recorded : actual.result.application = some (actor, operation)) (packet : EstablishedReceive.Input)
    (received : operation.event = .receive packet) (nonempty : operation.acceptedPayload ≠ []) :
    ∃ index raw policy receipt, actual.event = .deliver index raw policy ∧ actual.result.receipt = some receipt ∧
      receipt.received = packet ∧ receipt.actor = actor ∧ operation.stamp = actual.before.time ∧
      receipt.application = some operation ∧ ∃ sourceActor sourceStep output origin,
        receipt.served.ticket.value.produced = .application sourceActor sourceStep output origin := by
  obtain ⟨cases⟩ := CampusTCPReceiveCases.Step.receive_cases actual actor operation recorded packet received
  cases cases with
  | application value =>
    exact ⟨value.service, value.raw, value.policy, value.receipt, value.event, value.recorded,
      value.same, value.receiver, value.stamp, value.localRecord,
      value.sourceActor, value.sourceStep, value.output, value.origin, value.production⟩
  | recovery control present delivery ack same =>
    apply False.elim
    apply nonempty
    simp only [ApplicationTrace.Step.acceptedPayload, ApplicationTrace.acceptedPayload,
      ack.ack.2.1, ack.ack.2.2.2.2.2.1]
    exact ack.ack.1.2.2

theorem Report.application_delivery (report : Report input events) (complete : H.Completed input.active input.passive)
    (endpoints : Applications complete) (connection : report.final.connection = .application complete endpoints)
    (actor : Actor) (operation : T.Step) (member : operation ∈ applicationSteps endpoints actor)
    (nonempty : operation.acceptedPayload ≠ []) :
    Nonempty (CampusTCPFacts.ApplicationDelivery report (applicationSteps endpoints actor.other) actor operation) := by
  have inside : operation ∈ CampusTCPApplicationHistory.connectionSteps report.final.connection actor := by
    rw [connection]
    exact member
  simpa only [connection, CampusTCPApplicationHistory.connectionSteps] using
    CampusTCPReceiveHistory.Report.payload_application_delivery report actor operation inside nonempty

theorem Report.receives (report : Report input events) (complete : H.Completed input.active input.passive)
    (endpoints : Applications complete) (connection : report.final.connection = .application complete endpoints) (actor : Actor) :
    CampusTCPReceiveHistory.PayloadReceives report (applicationSteps endpoints actor.other) actor (applicationSteps endpoints actor) := by
  simpa only [connection, CampusTCPApplicationHistory.connectionSteps] using
    CampusTCPReceiveHistory.Report.payload_receives report actor

open CampusTCPRound (Cut)
open CampusTCPRecoveryRoundState (Completed)
open CampusTCPRecoveryRoundEvidence (Done)

variable {events : List Event} {report : Report input events}
variable {complete : H.Completed input.active input.passive} {request : Request input}
variable {initial : Initial report complete request} {current : Cut input complete} {retries : Nat}

theorem Completed.server_receives (_done : Completed initial current retries) :
    CampusTCPReceiveHistory.PayloadReceives current.report (applicationSteps current.endpoints .client) .server
      (applicationSteps current.endpoints .server) :=
  Report.receives current.report complete current.endpoints current.connection .server

theorem Completed.server_read_origin (done : Completed initial current retries)
    (index : Nat) (byte : UInt8) (selected : request.bytes[index]? = some byte) :
    Nonempty (CampusTCPGapFacts.ReadOrigin current.report complete.certificate.activeSeed
      (applicationSteps current.endpoints .client) .server (applicationSteps current.endpoints .server)
      done.operation index byte) := by
  have receives := Completed.server_receives done
  have history : ApplicationTrace.PayloadDeliveryHistory (applicationSteps current.endpoints .client)
      (applicationSteps current.endpoints .server) := by
    simpa only [current.connection, CampusTCPApplicationHistory.connectionSteps, Actor.other] using
      CampusTCPReceiveHistory.Report.payload_history current.report .server
  obtain ⟨member, _, event, read⟩ := done.history.exact_read
  have empty := complete.certificate.empty
  apply CampusTCPGapFacts.payload_read_origin current.endpoints.server.chain current.endpoints.client.chain history receives
    empty.2.2.2.2.2 complete.certificate.empty_receiveStore.2 empty.2.1 empty.1
    done.operation member request.bytes.length event index byte
  change done.operation.readBytes[index]? = some byte
  rw [read]
  exact selected

theorem Done.server_read_origin (done : Done initial current monitor retries)
    (index : Nat) (byte : UInt8) (selected : request.bytes[index]? = some byte) :
    Nonempty (CampusTCPGapFacts.ReadOrigin current.report complete.certificate.activeSeed
      (applicationSteps current.endpoints .client) .server (applicationSteps current.endpoints .server)
      done.completed.operation index byte) := Completed.server_read_origin done.completed index byte selected

theorem Done.release_origin (done : Done initial current monitor retries)
    (receipt : CampusTCPRecoveryRoundEvidence.FirstReceipt initial current) (first : done.first = some receipt)
    (index : Nat) (byte : UInt8)
    (origin : CampusTCPGapFacts.ReadOrigin current.report complete.certificate.activeSeed
      (applicationSteps current.endpoints .client) .server (applicationSteps current.endpoints .server)
      done.completed.operation index byte) : origin.read.release = receipt.operation := by
  have selected : done.completed.history.first = some receipt.operation := by
    simpa only [first, Option.map_some] using done.firstOperation
  have member : origin.read.release ∈ applicationSteps current.endpoints .server := by
    have prior : origin.read.release ∈ origin.read.prior := by
      rw [origin.read.releaseSplit]
      simp
    exact (congrArg (fun steps : List T.Step => origin.read.release ∈ steps) origin.read.split).mpr
      (List.mem_append_left _ prior)
  have nonempty : origin.read.release.releasedPayload.isEmpty = false := by
    apply List.isEmpty_eq_false_iff.mpr
    intro empty
    have present := origin.read.releaseByte
    rw [empty] at present
    cases present
  have release : origin.read.release ∈ (applicationSteps current.endpoints .server).filter
      CampusTCPRecoveryRoundHistory.nonemptyRelease :=
    List.mem_filter.mpr ⟨member, by simp only [CampusTCPRecoveryRoundHistory.nonemptyRelease, nonempty, Bool.not_false]⟩
  simpa only [done.completed.history.releases, selected, Option.toList_some, List.mem_singleton] using release

private def ReceiptChanges (before : State input) (effect : Effect input) : Prop :=
  effect.state.receipts = before.receipts ++ effect.receipt.toList ∧
    ∀ receipt, effect.receipt = some receipt → receipt.time = before.time ∧
      receipt.application = effect.application.map (·.2)

private theorem quiet_receipts (before : State input) (effect : Effect input)
    (same : effect.state.receipts = before.receipts) (quiet : effect.receipt = none) : ReceiptChanges before effect := by
  refine ⟨?_, ?_⟩
  · simp only [quiet, Option.toList_none, List.append_nil, same]
  · intro receipt present
    rw [quiet] at present
    cases present

private theorem application_receipts (before : State input) (actor : Actor) (event : T.Event) (effect : Effect input)
    (computed : applyApplication input before actor event = .ok effect) : ReceiptChanges before effect := by
  unfold applyApplication at computed
  repeat' first
    | (solve | cases computed; exact quiet_receipts _ _ rfl rfl)
    | (cases computed)
    | (split at computed)
    | (dsimp only [bind, Except.bind, pure, Except.pure, parsed, Except.mapError] at computed)

private theorem startup_receipts (before : State input) (event : TCPHandshake.Event) (effect : Effect input)
    (computed : startup input before event = .ok effect) : ReceiptChanges before effect := by
  unfold startup at computed
  repeat' first
    | (solve | cases computed; exact quiet_receipts _ _ rfl rfl)
    | (cases computed)
    | (split at computed)
    | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)

private theorem enableAck_receipts (before : State input) (actor : Actor) (effect : Effect input)
    (computed : enableAck input before actor = .ok effect) : ReceiptChanges before effect := by
  unfold enableAck at computed
  repeat' first
    | (solve | exact application_receipts _ _ _ _ computed)
    | (solve | cases computed)
    | (split at computed)
    | (dsimp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at computed)

@[simp] private theorem write_receipts (before : State input) (gateway : Gateway) (resident : Local) :
    (before.write gateway resident).receipts = before.receipts := by cases gateway <;> rfl

private theorem startup_application_none (before : State input) (event : TCPHandshake.Event) (effect : Effect input)
    (computed : startup input before event = .ok effect) : effect.application = none := by
  unfold startup at computed
  repeat' first
    | (solve | cases computed; rfl)
    | (solve | cases computed)
    | (split at computed)
    | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)

private theorem recovery_receipts (before : State input) (event : TCPHandshakeRecovery.Event) (effect : Effect input)
    (computed : runRecovery input before event = .ok effect) : ReceiptChanges before effect := by
  unfold runRecovery at computed
  split at computed
  · cases computed; exact quiet_receipts _ _ rfl rfl
  · cases computed; exact quiet_receipts _ _ rfl rfl
  · split at computed
    · cases computed
    · rename_i current connected result evaluated
      cases result with
      | mk state decision output receipt application =>
        cases output <;> simp only [pure, Except.pure, Except.ok.injEq] at computed
        all_goals subst effect; exact quiet_receipts _ _ rfl rfl

private theorem openRecovery_receipts (before : State input) (remote : Handshake.Socket) (policy : Bool) (effect : Effect input)
    (computed : openRecovering input before remote policy = .ok effect) : ReceiptChanges before effect := by
  unfold openRecovering at computed
  repeat' first
    | (solve | cases computed; exact quiet_receipts _ _ rfl rfl)
    | (solve | simpa only [ReceiptChanges] using recovery_receipts _ _ _ computed)
    | (solve | cases computed)
    | (split at computed)
    | (dsimp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at computed)

private theorem drain_receipts (before : State input) (effect : Effect input)
    (computed : finishStartup input before = .ok effect) : ReceiptChanges before effect := by
  unfold finishStartup at computed
  repeat' first
    | (solve | cases computed; exact quiet_receipts _ _ rfl rfl)
    | (solve | cases computed)
    | (split at computed)
    | (dsimp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at computed)

private theorem handoff_receipts (before : State input) (actor : Actor) (effect : Effect input)
    (computed : enableStartupRecovery input before actor = .ok effect) : ReceiptChanges before effect := by
  unfold enableStartupRecovery at computed
  split at computed
  · cases computed; exact quiet_receipts _ _ rfl rfl
  · exact application_receipts _ _ _ _ computed

private theorem process_receipts (before : State input) (event : Event) (effect : Effect input)
    (computed : processCore input before event = .ok effect) : ReceiptChanges before effect := by
  cases event with
  | «open» remote policy => exact startup_receipts _ _ _ computed
  | openRecovering remote policy => exact openRecovery_receipts _ _ _ _ computed
  | startupClock actor millis | startupTimeout actor generation policy => exact recovery_receipts _ _ _ computed
  | finishStartup => exact drain_receipts _ _ computed
  | enableStartupRecovery actor => exact handoff_receipts _ _ _ computed
  | write actor bytes | send actor count policy | read actor count | emitAck actor policy | enableRecovery actor | advanceClock actor millis | timeout actor policy | dispatchAck actor policy =>
    exact application_receipts _ _ _ _ computed
  | enableAck actor => exact enableAck_receipts _ _ _ computed
  | deliver index bytes policy =>
    simp only [processCore] at computed
    repeat' first
      | (solve
        | cases computed
          refine ⟨rfl, ?_⟩
          intro receipt present
          cases present
          exact ⟨rfl, rfl⟩)
      | (solve
        | cases computed
          refine ⟨rfl, ?_⟩
          intro receipt present
          cases present
          refine ⟨rfl, ?_⟩
          rw [startup_application_none _ _ _ (by assumption)]
          rfl)
      | (cases computed)
      | (split at computed)
      | (dsimp only [CampusTCPModel.get, parsed, Except.mapError, bind, Except.bind, pure, Except.pure,
          throw, throwThe, MonadExceptOf.throw] at computed)
    all_goals
      rename_i startupEffect startupAt
      have absent := startup_application_none before _ startupEffect startupAt
      refine ⟨rfl, ?_⟩
      intro receipt present
      cases present
      refine ⟨rfl, ?_⟩
      change none = startupEffect.application.map (·.2)
      rw [absent]
      rfl
  | authentication index | install id | stage id | installGuard id | installAt gateway id | stageAt gateway id | installGuardAt gateway id | assign index ingress | serve id observed | copyPacket id | dropPacket id | pause | stageCheckpoint | installCheckpoint ns | switchRoute actor gateway | fencePrimary | resume =>
    simp only [processCore, installConfiguration, stageAttachment, installIngress, transferControl] at computed
    repeat' first
      | (solve | cases computed; apply quiet_receipts _ _ _ rfl; simp only [write_receipts, unsupported])
      | (cases computed)
      | (split at computed)
      | (dsimp only [CampusTCPModel.get, parsed, Except.mapError, bind, Except.bind, pure, Except.pure,
          throw, throwThe, MonadExceptOf.throw] at computed)

theorem Step.receipts (actual : Step input) : actual.result.state.receipts = actual.before.receipts ++ actual.result.receipt.toList := by
  obtain ⟨effect, custody, computed, same⟩ := actual.processed
  simpa only [same] using (process_receipts actual.before actual.event effect computed).1

theorem Step.receipt_application (actual : Step input) (receipt : Receipt input) (recorded : actual.result.receipt = some receipt) :
    receipt.time = actual.before.time ∧ receipt.application = actual.result.application.map (·.2) := by
  obtain ⟨effect, custody, computed, same⟩ := actual.processed
  simpa only [same] using (process_receipts actual.before actual.event effect computed).2 receipt (by simpa only [same] using recorded)

theorem Trace.receipt_origin (trace : Trace input before events steps after remaining) (receipt : Receipt input)
    (member : receipt ∈ after.receipts) : receipt ∈ before.receipts ∨ ∃ actual ∈ steps, actual.result.receipt = some receipt := by
  induction trace with
  | done state => exact .inl member
  | stop head blocked rest =>
    rw [Step.receipts head] at member
    rcases List.mem_append.mp member with old | fresh
    · exact .inl old
    · exact .inr ⟨head, List.mem_cons_self, by simpa using fresh⟩
  | next head supported rest ih =>
    rcases ih member with old | later
    · rw [Step.receipts head] at old
      rcases List.mem_append.mp old with old | fresh
      · exact .inl old
      · exact .inr ⟨head, List.mem_cons_self, by simpa using fresh⟩
    · obtain ⟨actual, inside, recorded⟩ := later
      exact .inr ⟨actual, List.mem_cons_of_mem _ inside, recorded⟩

theorem Report.receipt_origin (report : Report input events) (receipt : Receipt input) (member : receipt ∈ report.final.receipts) :
    ∃ actual ∈ report.steps, actual.result.receipt = some receipt := by
  rcases Trace.receipt_origin report.trace receipt member with old | created
  · simp only [Input.initial, List.not_mem_nil] at old
  · exact created

private theorem released_receive (operation : T.Step) (nonempty : operation.releasedPayload ≠ []) :
    ∃ packet, operation.event = .receive packet := by
  cases event : operation.event
  all_goals first
    | exact ⟨_, rfl⟩
    | simp only [ApplicationTrace.Step.releasedPayload, ApplicationTrace.releasedPayload, event, ne_eq, not_true_eq_false] at nonempty

theorem FirstReceipt.application_delivery (first : CampusTCPRecoveryRoundEvidence.FirstReceipt initial current) :
    ∃ delivery : CampusTCPFacts.ApplicationDelivery current.report (applicationSteps current.endpoints .client) .server first.operation,
      delivery.receive.receipt = first.receipt := by
  obtain ⟨packet, received⟩ := released_receive first.operation (by rw [first.released]; exact request.nonempty)
  have payloadNonempty : first.operation.acceptedPayload ≠ [] := by
    cases transition : first.operation.storeTransition with
    | stutter state empty =>
      have nonempty : first.operation.releasedPayload ≠ [] := by rw [first.released]; exact request.nonempty
      exact False.elim (nonempty empty)
    | accepted allocation => exact allocation.accepted_payload_nonempty
  obtain ⟨actual, member, present⟩ := Report.receipt_origin current.report first.receipt (List.mem_of_getElem? first.stored)
  have mapped := ((Step.receipt_application actual first.receipt present).2).symm.trans first.application
  obtain ⟨actor, recorded⟩ : ∃ actor, actual.result.application = some (actor, first.operation) := by
    cases selected : actual.result.application with
    | none => simp only [selected, Option.map_none, reduceCtorEq] at mapped
    | some pair =>
      rcases pair with ⟨actor, operation⟩
      have same : operation = first.operation := by simpa only [selected, Option.map_some, Option.some.injEq] using mapped
      exact ⟨actor, by simp only [same]⟩
  obtain ⟨index, raw, policy, receipt, event, receiptAt, same, receiver, stamp, receiptStep, production⟩ :=
    Step.payload_receive_origin actual actor first.operation recorded packet received payloadNonempty
  have receiptEq : receipt = first.receipt := Option.some.inj (receiptAt.symm.trans present)
  have target : first.receipt.actor = .server := by rw [first.receipt.receiver, first.actor]; rfl
  have actorEq : actor = .server := receiver.symm.trans ((congrArg Receipt.actor receiptEq).trans target)
  have retained := Report.application_member current.report actual member actor first.operation recorded
  have inside : first.operation ∈ applicationSteps current.endpoints .server := by
    simpa only [current.connection, connectionSteps, actorEq] using retained
  obtain ⟨delivery⟩ := Report.application_delivery current.report complete current.endpoints current.connection .server
    first.operation inside payloadNonempty
  let actualAt : CampusTCPFacts.At current.report first.operation.stamp := ⟨actual, member, stamp.symm⟩
  have unique : delivery.receive.joint.step = actual := CampusTCPFacts.At.unique delivery.receive.joint actualAt
  have actualReceipt : actual.result.receipt = some delivery.receive.receipt := by simpa only [unique] using delivery.receive.recorded
  exact ⟨delivery, Option.some.inj (actualReceipt.symm.trans present)⟩

theorem compliant_of_suffix (prior : Report input priorEvents) (after : Report input afterEvents)
    (supported : after.supported = true) (compliant : prior.compliant = true) (suffix : List (Step input))
    (history : after.steps = prior.steps ++ suffix) (passed : ∀ actual ∈ suffix, actual.result.passed = true) :
    after.compliant = true := by
  simp only [Report.compliant, Bool.and_eq_true]
  refine ⟨supported, List.all_eq_true.mpr ?_⟩
  intro actual member
  rw [history] at member
  rcases List.mem_append.mp member with old | fresh
  · exact prior.step_passed compliant actual old
  · exact passed actual fresh

theorem FirstReceipt.service_permissions (first : CampusTCPRecoveryRoundEvidence.FirstReceipt initial current)
    (prior : initial.start.next.report.compliant = true) (suffix : List (Step input))
    (history : current.report.steps = initial.start.next.report.steps ++ suffix)
    (passed : ∀ actual ∈ suffix, actual.result.passed = true) :
    ∃ delivery : CampusTCPFacts.ApplicationDelivery current.report (applicationSteps current.endpoints .client) .server first.operation,
      delivery.receive.receipt = first.receipt ∧
        CampusTCPRoundOrigins.ServicePermissions delivery.service.joint.step delivery.receive.receipt.served := by
  obtain ⟨delivery, same⟩ := FirstReceipt.application_delivery first
  have compliant := compliant_of_suffix initial.start.next.report current.report current.supported prior suffix history passed
  refine ⟨delivery, same, ?_⟩
  exact CampusTCPRoundOrigins.service_permissions current.report compliant delivery.service.joint.step delivery.service.joint.member
    delivery.receive.receipt.served delivery.service.present delivery.receive.receipt.emission delivery.receive.receipt.emitted

end Netlib.Check.CampusTCPRecoveryRoundOrigins
