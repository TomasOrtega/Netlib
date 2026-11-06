import Netlib.Check.CampusTCPRecoveryRoundPhaseBase
import Netlib.Check.CampusTCPRoundPhaseHistory
import Netlib.Check.CampusTCPRoundReport

/-!
# Exact server streams through one recovery round

Retries can add receive operations without another nonempty release.
The final read retains the one actual release and its selected bytes.
-/

namespace Netlib.Check.CampusTCPRecoveryRoundHistory

open Protocol.TCP CampusTCPModel CampusTCPEnabled CampusTCPRoundStart
open CampusTCPRound (Cut)
open CampusTCPRoundPhaseBase (Move)
open CampusTCPRecoveryRoundPhaseBase (At)
open CampusTCPRoundPhaseHistory (Summary summary summary_append summary_clocks nonemptyRead)

def nonemptyRelease (operation : T.Step) : Bool := !operation.releasedPayload.isEmpty

structure Streams (bytes : List UInt8) (operations : List T.Step) (released : Bool) where
  first : Option T.Step
  releaseStream : operations.flatMap Netlib.Protocol.TCP.ApplicationTrace.Step.releasedPayload = if released then bytes else []
  readStream : operations.flatMap Netlib.Protocol.TCP.ApplicationTrace.Step.readBytes = []
  reads : operations.filter nonemptyRead = []
  releases : operations.filter nonemptyRelease = first.toList
  present : first.isSome = released
  firstPayload : ∀ operation, first = some operation → operation.releasedPayload = bytes

structure ReadStreams (bytes : List UInt8) (operations : List T.Step) (reader : T.Step) where
  first : Option T.Step
  releaseStream : operations.flatMap Netlib.Protocol.TCP.ApplicationTrace.Step.releasedPayload = bytes
  readStream : operations.flatMap Netlib.Protocol.TCP.ApplicationTrace.Step.readBytes = bytes
  reads : operations.filter nonemptyRead = [reader]
  releases : operations.filter nonemptyRelease = first.toList
  present : first.isSome = true
  firstPayload : ∀ operation, first = some operation → operation.releasedPayload = bytes
  readBytes : reader.readBytes = bytes
  readEvent : reader.event = .read bytes.length

private theorem no_releases (operations : List T.Step)
    (empty : operations.flatMap Netlib.Protocol.TCP.ApplicationTrace.Step.releasedPayload = []) : operations.filter nonemptyRelease = [] := by
  apply List.filter_eq_nil_iff.mpr
  intro operation member
  have quiet := (List.flatMap_eq_nil_iff.mp empty) operation member
  simp only [nonemptyRelease, quiet, List.isEmpty_nil, Bool.not_true, Bool.false_eq_true, not_false_eq_true]

def Streams.silent_append (history : Streams bytes operations released) (extra : List T.Step)
    (releaseStream : extra.flatMap Netlib.Protocol.TCP.ApplicationTrace.Step.releasedPayload = [])
    (readStream : extra.flatMap Netlib.Protocol.TCP.ApplicationTrace.Step.readBytes = []) (reads : extra.filter nonemptyRead = []) :
    Streams bytes (operations ++ extra) released := by
  refine ⟨history.first, ?_, ?_, ?_, ?_, history.present, history.firstPayload⟩
  · simp only [List.flatMap_append, releaseStream, List.append_nil, history.releaseStream]
  · simp only [List.flatMap_append, readStream, List.append_nil, history.readStream]
  · simp only [List.filter_append, reads, List.append_nil, history.reads]
  · simp only [List.filter_append, no_releases extra releaseStream, List.append_nil, history.releases]

def Streams.quiet_append (history : Streams bytes operations released) (operation : T.Step)
    (release : operation.releasedPayload = []) (read : operation.readBytes = []) :
    Streams bytes (operations ++ [operation]) released := by
  apply history.silent_append [operation]
  · simp only [List.flatMap_cons, List.flatMap_nil, release, List.nil_append]
  · simp only [List.flatMap_cons, List.flatMap_nil, read, List.nil_append]
  · simp only [List.filter_cons, List.filter_nil, nonemptyRead, read, List.isEmpty_nil,
      Bool.not_true, Bool.false_eq_true, ↓reduceIte]

def Streams.clocks_append (history : Streams bytes operations released) (extra : List T.Step)
    (clocks : ∀ operation ∈ extra, ∃ now, operation.event = .advanceClock now) :
    Streams bytes (operations ++ extra) released := by
  have quiet := summary_clocks extra clocks
  exact history.silent_append extra (congrArg Summary.released quiet) (congrArg Summary.read quiet)
    (congrArg Summary.reads quiet)

def Streams.first_append (history : Streams bytes operations false) (operation : T.Step)
    (nonempty : bytes ≠ []) (release : operation.releasedPayload = bytes) (read : operation.readBytes = []) :
    Streams bytes (operations ++ [operation]) true := by
  have absent : history.first = none := by
    have present := history.present
    cases selected : history.first <;> simp_all
  have populated : bytes.isEmpty = false := List.isEmpty_eq_false_iff.mpr nonempty
  refine ⟨some operation, ?_, ?_, ?_, ?_, rfl, ?_⟩
  · simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      history.releaseStream, Bool.false_eq_true, ↓reduceIte, release, List.nil_append]
  · simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      history.readStream, read]
  · simp only [List.filter_append, history.reads, List.filter_cons, List.filter_nil,
      nonemptyRead, read, List.isEmpty_nil, Bool.not_true, Bool.false_eq_true, ↓reduceIte, List.nil_append]
  · simp only [List.filter_append, history.releases, absent, Option.toList_none, List.filter_cons,
      List.filter_nil, nonemptyRelease, release, populated, Bool.not_false, ↓reduceIte, List.nil_append,
      Option.toList_some]
  · intro selected same
    cases Option.some.inj same
    exact release

def Streams.read_append (history : Streams bytes operations true) (operation : T.Step)
    (nonempty : bytes ≠ []) (event : operation.event = .read bytes.length) (read : operation.readBytes = bytes) :
    ReadStreams bytes (operations ++ [operation]) operation := by
  have release : operation.releasedPayload = [] := by
    simp only [ApplicationTrace.Step.releasedPayload, ApplicationTrace.releasedPayload, event]
  have populated : bytes.isEmpty = false := List.isEmpty_eq_false_iff.mpr nonempty
  refine ⟨history.first, ?_, ?_, ?_, ?_, history.present, history.firstPayload, read, event⟩
  · simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      release, history.releaseStream, ↓reduceIte]
  · simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      read, history.readStream, List.nil_append]
  · simp only [List.filter_append, history.reads, List.filter_cons, List.filter_nil, nonemptyRead,
      read, populated, Bool.not_false, ↓reduceIte, List.nil_append]
  · simp only [List.filter_append, history.releases, List.filter_cons, List.filter_nil,
      nonemptyRelease, release, List.isEmpty_nil, Bool.not_true, Bool.false_eq_true, ↓reduceIte, List.append_nil]

def ReadStreams.clocks_append (history : ReadStreams bytes operations reader) (extra : List T.Step)
    (clocks : ∀ operation ∈ extra, ∃ now, operation.event = .advanceClock now) :
    ReadStreams bytes (operations ++ extra) reader := by
  have quiet := summary_clocks extra clocks
  have releaseStream : extra.flatMap Netlib.Protocol.TCP.ApplicationTrace.Step.releasedPayload = [] :=
    congrArg Summary.released quiet
  have readStream : extra.flatMap Netlib.Protocol.TCP.ApplicationTrace.Step.readBytes = [] :=
    congrArg Summary.read quiet
  have reads : extra.filter nonemptyRead = [] := congrArg Summary.reads quiet
  refine ⟨history.first, ?_, ?_, ?_, ?_, history.present, history.firstPayload, history.readBytes, history.readEvent⟩
  · simp only [List.flatMap_append, releaseStream, List.append_nil, history.releaseStream]
  · simp only [List.flatMap_append, readStream, List.append_nil, history.readStream]
  · simp only [List.filter_append, reads, List.append_nil, history.reads]
  · simp only [List.filter_append, no_releases extra releaseStream, List.append_nil, history.releases]

theorem Streams.first_member (history : Streams bytes operations released) (selected : history.first = some operation) :
    operation ∈ operations ∧ operation.releasedPayload = bytes := by
  have present : operation ∈ operations.filter nonemptyRelease := by
    rw [history.releases, selected]
    simp only [Option.toList_some, List.mem_singleton]
  exact ⟨(List.mem_filter.mp present).1, history.firstPayload operation selected⟩

theorem ReadStreams.exact_release (history : ReadStreams bytes operations reader) :
    ∃ operation ∈ operations, operations.filter nonemptyRelease = [operation] ∧ operation.releasedPayload = bytes := by
  obtain ⟨operation, selected⟩ := Option.isSome_iff_exists.mp history.present
  have present : operation ∈ operations.filter nonemptyRelease := by
    rw [history.releases, selected]
    simp only [Option.toList_some, List.mem_singleton]
  exact ⟨operation, (List.mem_filter.mp present).1, by rw [history.releases, selected]; rfl,
    history.firstPayload operation selected⟩

theorem ReadStreams.exact_read (history : ReadStreams bytes operations reader) :
    reader ∈ operations ∧ operations.filter nonemptyRead = [reader] ∧
      reader.event = .read bytes.length ∧ reader.readBytes = bytes := by
  have present : reader ∈ operations.filter nonemptyRead := by rw [history.reads]; simp
  exact ⟨(List.mem_filter.mp present).1, history.reads, history.readEvent, history.readBytes⟩

variable {input : Input} {events : List Event} {report : Report input events}
  {complete : H.Completed input.active input.passive} {request : Request input}

abbrev History (_initial : Initial report complete request) (current : Cut input complete) (released : Bool) :=
  Streams request.bytes (applicationSteps current.endpoints .server) released

abbrev Complete (_initial : Initial report complete request) (current : Cut input complete) (reader : T.Step) :=
  ReadStreams request.bytes (applicationSteps current.endpoints .server) reader

variable {initial : Initial report complete request} {before current : Cut input complete} {released : Bool}

def initial_history (initial : Initial report complete request) : History initial (Cut.ofPrepared initial.start) false := by
  have quiet := CampusTCPRoundPhaseHistory.prepared_server_summary (initial := initial)
  have releases := congrArg Summary.released quiet
  refine ⟨none, releases, congrArg Summary.read quiet, congrArg Summary.reads quiet,
    no_releases _ releases, rfl, ?_⟩
  intro operation absent
  cases absent

theorem At.application_history (placement : At before current) (actor : Actor) :
    ∃ extra, applicationSteps current.endpoints actor = applicationSteps before.endpoints actor ++ extra ∧
      ∀ operation ∈ extra, ∃ now, operation.event = .advanceClock now := by
  obtain ⟨extra, history, clocks⟩ := placement.clocks
  have trace := CampusTCPRoundReport.Report.suffix before.report current.report current.supported current.finished history
  obtain ⟨updated, connected, histories⟩ := CampusTCPRoundPhaseHistory.Trace.clock_history trace before.connection
    (CampusTCPChronology.Report.chronological before.report) clocks
  have same := congrArg (fun connection => CampusTCPRoundPhaseHistory.connectionSteps connection actor)
    (current.connection.symm.trans connected)
  change applicationSteps current.endpoints actor = applicationSteps updated actor at same
  rw [same]
  exact histories actor

theorem At.summary (placement : At before current) (actor : Actor) :
    summary (applicationSteps current.endpoints actor) = summary (applicationSteps before.endpoints actor) := by
  obtain ⟨extra, history, clocks⟩ := At.application_history placement actor
  rw [history, summary_append, summary_clocks extra clocks]
  simp only [Summary.append, Summary.empty, List.append_nil]

noncomputable def History.clock (history : History initial before released) (placement : At before current) :
    History initial current released := by
  let extra := Classical.choose (At.application_history placement .server)
  have actual := Classical.choose_spec (At.application_history placement .server)
  change Streams request.bytes _ released
  rw [actual.1]
  exact history.clocks_append extra actual.2

noncomputable def Complete.clock (history : Complete initial before reader) (placement : At before current) :
    Complete initial current reader := by
  let extra := Classical.choose (At.application_history placement .server)
  have actual := Classical.choose_spec (At.application_history placement .server)
  change ReadStreams request.bytes _ reader
  rw [actual.1]
  exact history.clocks_append extra actual.2

def History.same (history : History initial before released)
    (operations : applicationSteps current.endpoints .server = applicationSteps before.endpoints .server) :
    History initial current released := by
  change Streams request.bytes _ released
  rw [operations]
  exact history

def History.network (history : History initial before released) (move : Move before actual)
    (event : CampusTCPRoundClock.NetworkAction actual.event) : History initial move.after released :=
  history.same (CampusTCPRoundPhaseHistory.Move.network_history move event .server)

def History.client_local (history : History initial before released) (move : Move before actual)
    (event : T.Event) (action : LocalAction .client actual.event event) (operation : T.Step)
    (recorded : actual.result.application = some (.client, operation)) : History initial move.after released := by
  apply history.same
  simpa only [reduceCtorEq, ite_false, List.append_nil] using
    CampusTCPRoundPhaseHistory.Move.local_history move .client event action operation recorded .server

def History.server_ack (history : History initial before released) (move : Move before actual)
    (operation : T.Step) (action : LocalAction .server actual.event (.emitAck true))
    (recorded : actual.result.application = some (.server, operation)) (event : operation.event = .emitAck true) :
    History initial move.after released := by
  have operations := CampusTCPRoundPhaseHistory.Move.local_history move .server (.emitAck true) action operation recorded .server
  simp only [ite_true] at operations
  change Streams request.bytes _ released
  rw [operations]
  have quiet := CampusTCPRoundPhaseHistory.summary_ack operation event
  apply history.quiet_append operation
  · simpa only [summary, Summary.empty, List.flatMap_cons, List.flatMap_nil, List.append_nil] using congrArg Summary.released quiet
  · simpa only [summary, Summary.empty, List.flatMap_cons, List.flatMap_nil, List.append_nil] using congrArg Summary.read quiet

private theorem receive_read_empty (operation : T.Step) (event : operation.event = .receive packet) : operation.readBytes = [] := by
  obtain ⟨_, _, _, _, _, _, _, _, empty⟩ := Endpoint.receive_effects operation.before packet
  simpa only [ApplicationTrace.Step.readBytes, operation.computed, event, ApplicationTrace.evaluate] using empty

def History.first_data (history : History initial before false) (move : Move before actual)
    (delivery : CampusTCPRoundDelivery.DataDelivered before.report complete before.endpoints index served emission emitted)
    (same : delivery.step = actual) (actor : served.ticket.value.produced.actor = .client)
    (payload : emission.asInput.packet.segment.payload = request.bytes) : History initial move.after true := by
  have operations := CampusTCPRoundPhaseHistory.Move.delivery_history move delivery.toDelivery same .server
  simp only [actor, Actor.other, ite_true] at operations
  change Streams request.bytes _ true
  rw [operations]
  apply history.first_append delivery.localStep request.nonempty
  · have released := congrArg Summary.released (CampusTCPRoundPhaseHistory.DataDelivered.summary delivery)
    simpa only [summary, List.flatMap_cons, List.flatMap_nil, List.append_nil, payload] using released
  · exact receive_read_empty delivery.localStep delivery.localEvent

def History.old_data (history : History initial before true) (move : Move before actual)
    (delivery : CampusTCPRoundDelivery.Delivery before.report complete before.endpoints index served emission emitted)
    (same : delivery.step = actual) (actor : served.ticket.value.produced.actor = .client)
    (empty : delivery.localStep.releasedPayload = []) : History initial move.after true := by
  have operations := CampusTCPRoundPhaseHistory.Move.delivery_history move delivery same .server
  simp only [actor, Actor.other, ite_true] at operations
  change Streams request.bytes _ true
  rw [operations]
  exact history.quiet_append delivery.localStep empty (receive_read_empty delivery.localStep delivery.localEvent)

def History.read (history : History initial before true) (move : Move before actual)
    (operation : T.Step) (action : LocalAction .server actual.event (.read request.bytes.length))
    (recorded : actual.result.application = some (.server, operation))
    (event : operation.event = .read request.bytes.length) (read : operation.readBytes = request.bytes) :
    Complete initial move.after operation := by
  have operations := CampusTCPRoundPhaseHistory.Move.local_history move .server (.read request.bytes.length) action operation recorded .server
  simp only [ite_true] at operations
  change ReadStreams request.bytes _ operation
  rw [operations]
  exact history.read_append operation request.nonempty event read

end Netlib.Check.CampusTCPRecoveryRoundHistory
