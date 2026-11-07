import Netlib.Check.CampusTCPRoundProgress
import Netlib.Check.CampusTCPApplicationHistory

/-!
# Actual endpoint history through the scheduled round

Clock suffixes append only clock operations to endpoint histories.
The final server history retains one data receipt and one nonempty read.
-/

namespace Netlib.Check.CampusTCPRoundPhaseHistory

open Protocol.TCP CampusTCPModel CampusTCPEnabled CampusTCPRoundStart CampusTCPRoundPhaseBase CampusTCPRoundProgress
open CampusTCPRound (Cut)

variable {input : Input} {events : List Event} {report : Report input events}
variable {complete : H.Completed input.active input.passive} {request : Request input}
variable {initial : Initial report complete request} {native : NativeEnv initial}

def connectionSteps (connection : Connection active passive) (actor : Actor) : List T.Step :=
  match connection with
  | .startup .. => []
  | .application _ endpoints => applicationSteps endpoints actor
  | .recovering current => current.applicationSteps actor.recoverySide

private theorem stateAt_append (state : State input) (prior later : List (Step input)) :
    CampusTCPSchedule.stateAt state (prior ++ later) prior.length =
      CampusTCPSchedule.stateAt state prior prior.length := by
  induction prior generalizing state with
  | nil => cases later <;> rfl
  | cons head tail ih => exact ih head.result.state

private theorem Trace.drop_complete (trace : Trace input first selected steps final remaining)
    (finished : remaining = []) (supported : ∀ actual ∈ steps, actual.result.supported = true)
    (count : Nat) (within : count ≤ steps.length) :
    Trace input (CampusTCPSchedule.stateAt first steps count) ((steps.drop count).map (·.event))
      (steps.drop count) final [] := by
  induction trace generalizing count with
  | done state =>
    have zero : count = 0 := by simp only [List.length_nil] at within; omega
    subst count
    exact .done state
  | stop head blocked tail =>
    have accepted := supported head (by simp)
    simp only [blocked, Bool.false_eq_true] at accepted
  | next head accepted rest ih =>
    cases count with
    | zero =>
      have covered := (Trace.next head accepted rest).covered
      rw [finished, List.append_nil] at covered
      rw [List.drop_zero]
      have complete := Trace.next head accepted rest
      rw [finished] at complete
      simpa only [CampusTCPSchedule.stateAt_zero, covered] using complete
    | succ count =>
      have bound : count ≤ _ := Nat.le_of_succ_le_succ within
      simpa only [List.drop_succ_cons, CampusTCPSchedule.stateAt] using
        ih finished (fun actual member => supported actual (List.mem_cons_of_mem _ member)) count bound

theorem At.suffix_trace (placement : At anchor current) :
    ∃ extra, current.report.steps = anchor.report.steps ++ extra ∧
      Trace input anchor.report.final (extra.map (·.event)) extra current.report.final [] ∧
      ∀ actual ∈ extra, ∃ actor now, actual.event = .advanceClock actor now := by
  obtain ⟨extra, steps, clocks⟩ := placement.clocks
  have within : anchor.report.steps.length ≤ current.report.steps.length := by rw [steps, List.length_append]; omega
  have trace := Trace.drop_complete current.report.trace current.finished
    (List.all_eq_true.mp current.supported) anchor.report.steps.length within
  have cut : CampusTCPSchedule.stateAt input.initial current.report.steps anchor.report.steps.length = anchor.report.final := by
    rw [steps, stateAt_append]
    exact CampusTCPSchedule.Trace.last_state anchor.report.trace
  rw [cut, steps, List.drop_left] at trace
  exact ⟨extra, steps, trace, clocks⟩

theorem Trace.clock_history (trace : Trace input before selected steps final remaining)
    (connection : before.connection = .application complete endpoints)
    (chronology : CampusTCPChronology.Chronological before)
    (clocks : ∀ actual ∈ steps, ∃ actor now, actual.event = .advanceClock actor now) :
    ∃ updated : Applications complete, final.connection = .application complete updated ∧
      ∀ actor, ∃ extra, applicationSteps updated actor = applicationSteps endpoints actor ++ extra ∧
        ∀ operation ∈ extra, ∃ now, operation.event = .advanceClock now := by
  induction trace generalizing endpoints with
  | done state => exact ⟨endpoints, connection, fun _ => ⟨[], by simp, by simp⟩⟩
  | stop head blocked tail =>
    obtain ⟨actor, now, event⟩ := clocks head (by simp)
    have prior : ∀ old ∈ applicationSteps endpoints actor, old.stamp < head.before.time := by
      have ordered := chronology
      simp only [CampusTCPChronology.Chronological, connection, CampusTCPChronology.Earlier] at ordered
      cases actor
      · exact ordered.1
      · exact ordered.2
    let operation := ApplicationTrace.Step.make (endpoint endpoints actor) (endpoint_valid endpoints actor)
      (.advanceClock now) head.before.time
    have action : LocalAction actor head.event (.advanceClock now) := by rw [event]; exact .advanceClock _
    have recorded := CampusTCPRoundLocal.step_application_recorded head complete endpoints connection actor
      (.advanceClock now) action prior
    obtain ⟨updated, connected, _, _, selectedSteps, peerSteps, _, localEvent, _⟩ :=
      CampusTCPEnabled.Step.application_frame head complete endpoints connection actor (.advanceClock now) action operation recorded
    refine ⟨updated, connected, ?_⟩
    intro receiver
    by_cases same : receiver = actor
    · subst receiver
      exact ⟨[operation], selectedSteps, by intro old member; rw [List.mem_singleton.mp member]; exact ⟨now, localEvent⟩⟩
    · have other : receiver = actor.other := by cases receiver <;> cases actor <;> simp_all [Actor.other]
      rw [other]
      exact ⟨[], by simpa only [List.append_nil] using peerSteps, by simp⟩
  | next head supported rest ih =>
    obtain ⟨actor, now, event⟩ := clocks head (by simp)
    have prior : ∀ old ∈ applicationSteps endpoints actor, old.stamp < head.before.time := by
      have ordered := chronology
      simp only [CampusTCPChronology.Chronological, connection, CampusTCPChronology.Earlier] at ordered
      cases actor
      · exact ordered.1
      · exact ordered.2
    let operation := ApplicationTrace.Step.make (endpoint endpoints actor) (endpoint_valid endpoints actor)
      (.advanceClock now) head.before.time
    have action : LocalAction actor head.event (.advanceClock now) := by rw [event]; exact .advanceClock _
    have recorded := CampusTCPRoundLocal.step_application_recorded head complete endpoints connection actor
      (.advanceClock now) action prior
    obtain ⟨updated, connected, _, _, selectedSteps, peerSteps, _, localEvent, _⟩ :=
      CampusTCPEnabled.Step.application_frame head complete endpoints connection actor (.advanceClock now) action operation recorded
    obtain ⟨last, lastConnection, histories⟩ := ih connected (CampusTCPChronology.Step.chronological head chronology)
      (fun actual member => clocks actual (List.mem_cons_of_mem _ member))
    refine ⟨last, lastConnection, ?_⟩
    intro receiver
    obtain ⟨extra, history, laterClocks⟩ := histories receiver
    by_cases same : receiver = actor
    · subst receiver
      refine ⟨operation :: extra, ?_, ?_⟩
      · rw [history, selectedSteps, List.append_assoc]
        rfl
      · intro old member
        rcases List.mem_cons.mp member with same | later
        · rw [same]
          exact ⟨now, localEvent⟩
        · exact laterClocks old later
    · have other : receiver = actor.other := by cases receiver <;> cases actor <;> simp_all [Actor.other]
      refine ⟨extra, ?_, laterClocks⟩
      rw [history, other, peerSteps]

theorem At.application_history (placement : At anchor current) (actor : Actor) :
    ∃ extra, applicationSteps current.endpoints actor = applicationSteps anchor.endpoints actor ++ extra ∧
      ∀ operation ∈ extra, ∃ now, operation.event = .advanceClock now := by
  obtain ⟨extra, _, trace, clocks⟩ := At.suffix_trace placement
  obtain ⟨updated, connected, histories⟩ := Trace.clock_history trace anchor.connection
    (CampusTCPChronology.Report.chronological anchor.report) clocks
  have same := congrArg (fun connection => connectionSteps connection actor) (current.connection.symm.trans connected)
  change applicationSteps current.endpoints actor = applicationSteps updated actor at same
  rw [same]
  exact histories actor

def isReceive (operation : T.Step) : Bool :=
  match operation.event with | .receive _ => true | _ => false

def nonemptyRead (operation : T.Step) : Bool := !operation.readBytes.isEmpty

structure Summary where
  released : List UInt8
  read : List UInt8
  receives : List T.Step
  reads : List T.Step

def Summary.empty : Summary := ⟨[], [], [], []⟩
def Summary.append (first last : Summary) : Summary :=
  ⟨first.released ++ last.released, first.read ++ last.read, first.receives ++ last.receives, first.reads ++ last.reads⟩

def summary (operations : List T.Step) : Summary :=
  ⟨operations.flatMap Netlib.Protocol.TCP.ApplicationTrace.Step.releasedPayload, operations.flatMap Netlib.Protocol.TCP.ApplicationTrace.Step.readBytes,
    operations.filter isReceive, operations.filter nonemptyRead⟩

theorem summary_append (first last : List T.Step) : summary (first ++ last) = (summary first).append (summary last) := by
  simp only [summary, Summary.append, List.flatMap_append, List.filter_append]

private theorem clock_read_empty (operation : T.Step) (event : operation.event = .advanceClock now) : operation.readBytes = [] := by
  change operation.result.read = []
  rw [operation.computed, event]
  change (Endpoint.advanceClock operation.before now).read = []
  unfold Endpoint.advanceClock
  repeat' first
    | rfl
    | split
    | (simp only [Endpoint.recoveryBlocked, Endpoint.ackBlocked, Endpoint.rejected])

private theorem ack_read_empty (operation : T.Step) (event : operation.event = .emitAck policy) : operation.readBytes = [] := by
  change operation.result.read = []
  rw [operation.computed, event]
  change (Endpoint.emitAck operation.before policy).read = []
  unfold Endpoint.emitAck Endpoint.pureAck
  repeat' first
    | rfl
    | split
    | (simp only [Endpoint.ackBlocked, Endpoint.rejected])

private theorem receive_read_empty (operation : T.Step) (event : operation.event = .receive packet) : operation.readBytes = [] := by
  obtain ⟨_, _, _, _, _, _, _, _, empty⟩ := Endpoint.receive_effects operation.before packet
  simpa only [Netlib.Protocol.TCP.ApplicationTrace.Step.readBytes, operation.computed, event, ApplicationTrace.evaluate] using empty

theorem summary_clock (operation : T.Step) (event : operation.event = .advanceClock now) : summary [operation] = .empty := by
  have read : operation.result.read = [] := clock_read_empty operation event
  simp only [summary, List.flatMap_cons, List.flatMap_nil, List.append_nil, Netlib.Protocol.TCP.ApplicationTrace.Step.releasedPayload,
    ApplicationTrace.releasedPayload, event, read, List.filter_cons, isReceive,
    nonemptyRead, List.isEmpty_nil, Bool.not_true, Bool.false_eq_true, ↓reduceIte, List.filter_nil,
    Summary.empty, Netlib.Protocol.TCP.ApplicationTrace.Step.readBytes]

theorem summary_clocks (operations : List T.Step)
    (clocks : ∀ operation ∈ operations, ∃ now, operation.event = .advanceClock now) : summary operations = .empty := by
  induction operations with
  | nil => rfl
  | cons head tail ih =>
    obtain ⟨now, event⟩ := clocks head (by simp)
    have tailClocks := fun operation member => clocks operation (List.mem_cons_of_mem _ member)
    rw [show head :: tail = [head] ++ tail from rfl, summary_append, summary_clock head event, ih tailClocks]
    rfl

def serverSummary (cut : Cut input complete) : Summary := summary (applicationSteps cut.endpoints .server)

theorem At.summary (placement : At anchor current) (actor : Actor) :
    summary (applicationSteps current.endpoints actor) = summary (applicationSteps anchor.endpoints actor) := by
  obtain ⟨extra, history, clocks⟩ := At.application_history placement actor
  rw [history, summary_append, summary_clocks extra clocks]
  simp only [Summary.append, Summary.empty, List.append_nil]

theorem At.serverSummary (placement : At anchor current) : serverSummary current = serverSummary anchor :=
  At.summary placement .server

private theorem flatMap_nil_of (operations : List T.Step) (f : T.Step → List α)
    (empty : ∀ operation ∈ operations, f operation = []) : operations.flatMap f = [] := by
  induction operations with
  | nil => rfl
  | cons head tail ih =>
    rw [List.flatMap_cons, empty head (by simp), ih (fun operation member => empty operation (List.mem_cons_of_mem _ member))]
    rfl

private theorem flatMap_nil_each (operations : List T.Step) (f : T.Step → List α) (empty : operations.flatMap f = []) :
    ∀ operation ∈ operations, f operation = [] := by
  induction operations with
  | nil => simp
  | cons head tail ih =>
    simp only [List.flatMap_cons, List.append_eq_nil_iff] at empty
    intro operation member
    rcases List.mem_cons.mp member with same | later
    · exact same ▸ empty.1
    · exact ih empty.2 operation later

private theorem filter_nil_of (operations : List T.Step) (f : T.Step → Bool)
    (empty : ∀ operation ∈ operations, f operation = false) : operations.filter f = [] := by
  induction operations with
  | nil => rfl
  | cons head tail ih =>
    rw [List.filter_cons, empty head (by simp)]
    exact ih (fun operation member => empty operation (List.mem_cons_of_mem _ member))

theorem beforeTransport_summary (cursor : Cursor seed) (before : cursor.beforeTransport = true)
    (seedEmpty : seed.core.received = []) : summary cursor.steps = .empty := by
  have noReceive (operation : T.Step) (member : operation ∈ cursor.steps) : isReceive operation = false := by
    cases event : operation.event <;> simp only [isReceive, event]
    exact False.elim (cursor.beforeTransport_no_receive before operation member _ event)
  have noRelease (operation : T.Step) (member : operation ∈ cursor.steps) : operation.releasedPayload = [] := by
    cases event : operation.event <;> simp only [Netlib.Protocol.TCP.ApplicationTrace.Step.releasedPayload,
      Netlib.Protocol.TCP.ApplicationTrace.releasedPayload, event]
    exact False.elim (cursor.beforeTransport_no_receive before operation member _ event)
  have released := flatMap_nil_of cursor.steps Netlib.Protocol.TCP.ApplicationTrace.Step.releasedPayload noRelease
  have balance := Netlib.Protocol.TCP.ApplicationTrace.Chain.received cursor.chain
  rw [seedEmpty, released, List.nil_append] at balance
  have read := (List.append_eq_nil_iff.mp balance.symm).1
  have everyRead := flatMap_nil_each cursor.steps Netlib.Protocol.TCP.ApplicationTrace.Step.readBytes read
  have noRead (operation : T.Step) (member : operation ∈ cursor.steps) : nonemptyRead operation = false := by
    simp only [nonemptyRead, everyRead operation member, List.isEmpty_nil, Bool.not_true]
  simp only [summary, released, read, filter_nil_of cursor.steps isReceive noReceive,
    filter_nil_of cursor.steps nonemptyRead noRead, Summary.empty]

theorem prepared_server_summary : serverSummary (Cut.ofPrepared initial.start) = .empty :=
  beforeTransport_summary initial.start.next.endpoints.server initial.start.next.serverBefore complete.certificate.empty.2.2.2.2.2

theorem Move.application_steps (move : Move before actual) (updated : Applications complete)
    (connection : actual.result.state.connection = .application complete updated) (actor : Actor) :
    applicationSteps move.after.endpoints actor = applicationSteps updated actor := by
  have same := move.after.connection.symm.trans ((congrArg State.connection move.final).trans connection)
  exact congrArg (fun connection => connectionSteps connection actor) same

theorem Move.network_history (move : Move before actual) (network : CampusTCPRoundClock.NetworkAction actual.event)
    (actor : Actor) : applicationSteps move.after.endpoints actor = applicationSteps before.endpoints actor := by
  have connection := CampusTCPRoundClock.Step.connection_frame actual network
  rw [move.beforeEq, before.connection] at connection
  exact Move.application_steps move before.endpoints connection actor

theorem Move.local_history {before : Cut input complete} {actual : Step input}
    (move : Move before actual) (actor : Actor) (event : T.Event)
    (action : LocalAction actor actual.event event) (operation : T.Step)
    (recorded : actual.result.application = some (actor, operation)) (receiver : Actor) :
    applicationSteps move.after.endpoints receiver = applicationSteps before.endpoints receiver ++
      (if receiver = actor then [operation] else []) := by
  have connection : actual.before.connection = .application complete before.endpoints := move.beforeEq ▸ before.connection
  obtain ⟨updated, connected, _, _, selected, peer, _, _, _⟩ :=
    CampusTCPEnabled.Step.application_frame actual complete before.endpoints connection actor event action operation recorded
  rw [Move.application_steps move updated connected receiver]
  by_cases same : receiver = actor
  · subst receiver
    simpa only [ite_true] using selected
  · have other : receiver = actor.other := by cases receiver <;> cases actor <;> simp_all [Actor.other]
    simp only [same, ite_false, List.append_nil]
    rw [other]
    exact peer

theorem Move.delivery_history (move : Move before actual)
    (delivery : CampusTCPRoundDelivery.Delivery before.report complete before.endpoints index served emission emitted)
    (same : delivery.step = actual) (receiver : Actor) :
    applicationSteps move.after.endpoints receiver = applicationSteps before.endpoints receiver ++
      (if receiver = served.ticket.value.produced.actor.other then [delivery.localStep] else []) := by
  have connection : actual.result.state.connection = .application complete delivery.updated := same ▸ delivery.connection
  rw [Move.application_steps move delivery.updated connection receiver]
  by_cases selected : receiver = served.ticket.value.produced.actor.other
  · subst receiver
    simpa only [ite_true] using delivery.selectedSteps
  · have other : receiver = served.ticket.value.produced.actor.other.other := by
      cases sourceActor : served.ticket.value.produced.actor <;> cases receiver <;> simp_all [Actor.other]
    simp only [selected, ite_false, List.append_nil]
    rw [other]
    exact delivery.peerSteps

private theorem summary_single (operation : T.Step) :
    summary [operation] = ⟨operation.releasedPayload, operation.readBytes,
      if isReceive operation then [operation] else [], if nonemptyRead operation then [operation] else []⟩ := by
  simp only [summary, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.filter_cons, List.filter_nil]

theorem summary_ack (operation : T.Step) (event : operation.event = .emitAck policy) : summary [operation] = .empty := by
  have released : operation.releasedPayload = [] := by
    simp only [Netlib.Protocol.TCP.ApplicationTrace.Step.releasedPayload, ApplicationTrace.releasedPayload, event]
  have read := ack_read_empty operation event
  rw [summary_single, released, read]
  simp only [isReceive, event, nonemptyRead, read, List.isEmpty_nil, Bool.not_true, Bool.false_eq_true, ↓reduceIte, Summary.empty]

theorem summary_read (operation : T.Step) (event : operation.event = .read count) (read : operation.readBytes = bytes)
    (nonempty : bytes ≠ []) : summary [operation] = ⟨[], bytes, [], [operation]⟩ := by
  have released : operation.releasedPayload = [] := by
    simp only [Netlib.Protocol.TCP.ApplicationTrace.Step.releasedPayload, ApplicationTrace.releasedPayload, event]
  have populated : bytes.isEmpty = false := List.isEmpty_eq_false_iff.mpr nonempty
  rw [summary_single, released, read]
  simp only [isReceive, event, nonemptyRead, read, populated, Bool.not_false, Bool.false_eq_true, ↓reduceIte]

theorem DataDelivered.summary
    (delivery : CampusTCPRoundDelivery.DataDelivered report complete endpoints index served emission emitted) :
    summary [delivery.localStep] = ⟨emission.asInput.packet.segment.payload, [], [delivery.localStep], []⟩ := by
  have released : delivery.localStep.releasedPayload = emission.asInput.packet.segment.payload := by
    simp only [Netlib.Protocol.TCP.ApplicationTrace.Step.releasedPayload, ApplicationTrace.releasedPayload,
      delivery.localEvent, delivery.resultState, delivery.received, delivery.localBefore, List.drop_append,
      List.drop_length, Nat.sub_self, List.drop_zero, List.nil_append]
  have read := receive_read_empty delivery.localStep delivery.localEvent
  rw [summary_single, released, read]
  simp only [isReceive, delivery.localEvent, nonemptyRead, read, List.isEmpty_nil, Bool.not_true, Bool.false_eq_true, ↓reduceIte]

theorem Move.network_summary (move : Move before actual) (network : CampusTCPRoundClock.NetworkAction actual.event) :
    serverSummary move.after = serverSummary before :=
  congrArg summary (Move.network_history move network .server)

variable {sent : Sent initial native} {assigned : Assigned sent} {service : DataServed assigned}
variable {released : Released service} {ack : Acked released} {assignedAck : AckAssigned ack}
variable {ackService : AckServed assignedAck} {retired : Retired ackService}

theorem Sent.server_summary (sent : Sent initial native) :
    serverSummary sent.hop.post = serverSummary (Cut.ofPrepared initial.start) := by
  have action : LocalAction .client sent.hop.actual.event (.send request.bytes.length true) := by rw [sent.event]; exact .send _ _
  have history := Move.local_history sent.hop.move .client (.send request.bytes.length true) action
    sent.application.operation sent.application.recorded .server
  simp only [reduceCtorEq, ite_false, List.append_nil] at history
  exact (congrArg summary history).trans (At.summary sent.hop.placement .server)

theorem Assigned.server_summary (assigned : Assigned sent) : serverSummary assigned.hop.post = serverSummary sent.hop.post :=
  (Move.network_summary assigned.hop.move (by rw [assigned.facts.event]; exact .assign _ _)).trans
    (At.serverSummary assigned.hop.placement)

theorem DataServed.server_summary (service : DataServed assigned) :
    serverSummary service.hop.post = serverSummary assigned.hop.post :=
  (Move.network_summary service.hop.move (by rw [service.facts.event]; exact .serve _ _)).trans
    (At.serverSummary service.hop.placement)

private theorem data_actor (service : DataServed assigned) : service.served.ticket.value.produced.actor = .client := by
  rw [service.facts.ticket, assigned.ticketEq]
  change sent.application.produced.actor = .client
  rw [sent.application.production]
  rfl

theorem Released.server_summary (released : Released service) :
    serverSummary released.hop.post = (serverSummary service.hop.post).append
      ⟨request.bytes, [], [released.delivery.localStep], []⟩ := by
  have history := Move.delivery_history released.hop.move released.delivery.toDelivery released.actual .server
  simp only [data_actor service, Actor.other, ite_true] at history
  have payload : service.emission.asInput.packet.segment.payload = request.bytes := by
    change service.emission.decoded.segment.payload = _
    rw [service.emission.payload]
    exact service.sourceFields.payload
  change summary (applicationSteps released.hop.move.after.endpoints .server) = _
  rw [history, summary_append, DataDelivered.summary released.delivery, payload, At.summary released.hop.placement .server]
  rfl

theorem Acked.server_summary (ack : Acked released) : serverSummary ack.hop.post = serverSummary released.hop.post := by
  have action : LocalAction .server ack.hop.actual.event (.emitAck true) := by rw [ack.facts.event]; exact .emitAck _
  have history := Move.local_history ack.hop.move .server (.emitAck true) action ack.facts.localStep ack.facts.application .server
  simp only [ite_true] at history
  change summary (applicationSteps ack.hop.move.after.endpoints .server) = _
  rw [history, summary_append, summary_ack ack.facts.localStep ack.facts.localEvent]
  simpa only [Summary.append, Summary.empty, List.append_nil, serverSummary] using At.summary ack.hop.placement .server

theorem AckAssigned.server_summary (assignment : AckAssigned ack) :
    serverSummary assignment.hop.post = serverSummary ack.hop.post :=
  (Move.network_summary assignment.hop.move (by rw [assignment.facts.event]; exact .assign _ _)).trans
    (At.serverSummary assignment.hop.placement)

theorem AckServed.server_summary (service : AckServed assignedAck) :
    serverSummary service.hop.post = serverSummary assignedAck.hop.post :=
  (Move.network_summary service.hop.move (by rw [service.facts.event]; exact .serve _ _)).trans
    (At.serverSummary service.hop.placement)

private theorem ack_actor (service : AckServed assignedAck) : service.served.ticket.value.produced.actor = .server := by
  rw [service.facts.ticket, assignedAck.ticketEq]
  change ack.facts.produced.actor = .server
  rw [ack.facts.production]
  rfl

theorem Retired.server_summary (retired : Retired ackService) :
    serverSummary retired.hop.post = serverSummary ackService.hop.post := by
  have history := Move.delivery_history retired.hop.move retired.delivery.toDelivery retired.actual .server
  simp only [ack_actor ackService, Actor.other, reduceCtorEq, ite_false, List.append_nil] at history
  exact (congrArg summary history).trans (At.summary retired.hop.placement .server)

theorem Read.server_summary (read : Read retired) :
    serverSummary read.hop.post = (serverSummary retired.hop.post).append
      ⟨[], request.bytes, [], [read.operation]⟩ := by
  have action : LocalAction .server read.hop.actual.event (.read request.bytes.length) := by rw [read.event]; exact .read _
  have history := Move.local_history read.hop.move .server (.read request.bytes.length) action read.operation read.recorded .server
  simp only [ite_true] at history
  change summary (applicationSteps read.hop.move.after.endpoints .server) = _
  rw [history, summary_append, summary_read read.operation read.localEvent read.localRead request.nonempty,
    At.summary read.hop.placement .server]
  rfl

theorem Completion.server_summary (done : Completion initial native current monitor) :
    serverSummary current = ⟨request.bytes, request.bytes, [done.released.delivery.localStep], [done.read.operation]⟩ := by
  rw [At.serverSummary done.placement.placement, Read.server_summary, Retired.server_summary, AckServed.server_summary,
    AckAssigned.server_summary, Acked.server_summary, Released.server_summary, DataServed.server_summary,
    Assigned.server_summary, Sent.server_summary, prepared_server_summary]
  simp only [Summary.append, Summary.empty, List.nil_append, List.append_nil]

theorem Completion.server_streams (done : Completion initial native current monitor) :
    (applicationSteps current.endpoints .server).flatMap Netlib.Protocol.TCP.ApplicationTrace.Step.releasedPayload = request.bytes ∧
      (applicationSteps current.endpoints .server).flatMap Netlib.Protocol.TCP.ApplicationTrace.Step.readBytes = request.bytes :=
  ⟨congrArg Summary.released (Completion.server_summary done), congrArg Summary.read (Completion.server_summary done)⟩

theorem Completion.server_receives (done : Completion initial native current monitor) :
    (applicationSteps current.endpoints .server).filter isReceive = [done.released.delivery.localStep] :=
  congrArg Summary.receives (Completion.server_summary done)

theorem Completion.server_nonempty_reads (done : Completion initial native current monitor) :
    (applicationSteps current.endpoints .server).filter nonemptyRead = [done.read.operation] :=
  congrArg Summary.reads (Completion.server_summary done)

theorem Completion.write_member (done : Completion initial native current monitor) :
    initial.start.writeStep ∈ current.report.steps :=
  (done.read.anchor.retained.trans done.placement.placement.retained).subset initial.start.writeMember

end Netlib.Check.CampusTCPRoundPhaseHistory
