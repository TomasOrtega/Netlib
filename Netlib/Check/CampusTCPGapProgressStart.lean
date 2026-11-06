import Netlib.Check.CampusTCPRound
import Netlib.Check.CampusTCPRoundReport
import Netlib.Check.CampusTCPGapFacts
import Netlib.Check.CampusTCPRecoveryRoundOrigins
import Netlib.Check.CampusTCPTransferFacts
import Netlib.Protocol.TCP.EndpointHeadTimeoutEnabled
import Netlib.Protocol.TCP.EndpointOldSpanEnabled

/-!
# Actual starting cuts for a held-gap task

Original packets, held receipts, and the selected live link share one report.
The write split identifies the selected writer even when earlier bytes repeat.
-/

namespace Netlib.Check.CampusTCPGapProgressStart

open Packet Protocol Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {events : List CampusTCPModel.Event}
variable {cut anchor : Cut input complete} {actor : Actor} {lower upper : List UInt8}

structure StartupBasis (cut : Cut input complete) where
  events : List CampusTCPModel.Event
  report : Report input events
  supported : report.supported = true
  finished : report.remaining = []
  connection : report.final.connection = .application complete (Applications.initial complete)
  ordinary : CampusTCPStartupOrigins.Ordinary report
  history : CampusTCPFacts.StartupHistory report complete
  clean : CampusTCPStartupTransport.CleanServices history
  retained : ∃ extra, cut.report.steps = report.steps ++ extra
  entry : NetfilterNAT.Entry
  session : Admission.Session
  aligned : CampusTCPStartupAlignment.Alignment input complete entry session
  phase : report.final.primary.transport.admission.phase = .data session

theorem StartupBasis.of_report (report : Report input events)
    (supported : report.supported = true) (finished : report.remaining = [])
    (connection : report.final.connection = .application complete (Applications.initial complete))
    (ordinary : CampusTCPStartupOrigins.Ordinary report)
    (history : CampusTCPFacts.StartupHistory report complete)
    (clean : CampusTCPStartupTransport.CleanServices history)
    (retained : ∃ extra, cut.report.steps = report.steps ++ extra) : Nonempty (StartupBasis cut) := by
  obtain ⟨entry, session, phase, aligned, _⟩ := clean.aligned history
  exact ⟨⟨_, report, supported, finished, connection, ordinary, history, clean, retained,
    entry, session, aligned, phase⟩⟩

structure Identity (seed current : Admission.Session) : Prop where
  entry : current.entry = seed.entry
  base : ∀ direction, (current.lane direction).base = (seed.lane direction).base
  clientMSS : current.clientMSS = seed.clientMSS
  serverMSS : current.serverMSS = seed.serverMSS

structure Shape (seed current : Admission.Session) : Prop extends Identity seed current where
  coverage : ∀ direction, (current.lane direction).coverage = (seed.lane direction).coverage

theorem Identity.refl (session : Admission.Session) : Identity session session :=
  ⟨rfl, fun _ => rfl, rfl, rfl⟩

theorem Identity.trans (first : Identity seed middle) (second : Identity middle current) : Identity seed current :=
  ⟨second.entry.trans first.entry, fun direction => (second.base direction).trans (first.base direction),
    second.clientMSS.trans first.clientMSS, second.serverMSS.trans first.serverMSS⟩

theorem Shape.refl (session : Admission.Session) : Shape session session :=
  ⟨Identity.refl session, fun _ => rfl⟩

theorem Shape.trans (first : Shape seed middle) (second : Shape middle current) : Shape seed current :=
  ⟨first.toIdentity.trans second.toIdentity, fun direction => (second.coverage direction).trans (first.coverage direction)⟩

structure GatewayStart (cut : Cut input complete) (basis : StartupBasis cut) where
  seed : Admission.Session
  identity : Identity basis.session seed
  phase : (beforeService input cut.report.final .standby).admission.phase = .data seed
  trackerValid : (beforeService input cut.report.final .standby).tracker.Valid
  record : ConntrackLifecycle.Record
  member : record ∈ (beforeService input cut.report.final .standby).tracker.records
  entry : record.entry = seed.entry
  confirmed : record.seenReply = true

structure LowerRange (start : GatewayStart cut basis) (sender : Actor) (bytes : List UInt8) where
  run : Admission.Coverage.Run Nat
  member : run ∈ (start.seed.lane sender.direction).coverage.runs
  position : run.position = 0
  bytes : run.bytes = bytes

structure Original (cut : Cut input complete) (actor : Actor) (bytes : List UInt8) where
  attempt : ApplicationTrace.OutputAt (applicationSteps cut.endpoints actor)
  event : attempt.step.event = .send bytes.length true
  payload : attempt.output.packet.segment.payload = bytes
  index : Nat
  produced : Produced input.active input.passive
  stored : cut.report.final.outputs[index]? = some produced
  application : produced = .application actor attempt.step attempt.output attempt.origin

theorem Original.emitted (original : Original cut actor bytes) : original.attempt.step.emitted = bytes := by
  have fields := original.attempt.origin.fields (by intro policy same; rw [original.event] at same; cases same)
  exact fields.1.symm.trans original.payload

structure WriteBatch (cut : Cut input complete) (actor : Actor) (lower upper : List UInt8)
    (first : Original cut actor lower) (second : Original cut actor upper) where
  writer : T.Step
  prior : List T.Step
  toLower : List T.Step
  toUpper : List T.Step
  lowerSplit : first.attempt.prior = prior ++ writer :: toLower
  upperSplit : second.attempt.prior = prior ++ writer :: (toLower ++ first.attempt.step :: toUpper)
  event : writer.event = .write (lower ++ upper)
  accepted : writer.result.decision = .accepted (.write (lower.length + upper.length))
  emptyPending : writer.before.pending = []
  emptySent : writer.before.core.sent = []
  lowerChain : ApplicationTrace.Chain writer.result.state toLower first.attempt.step.before
  upperChain : ApplicationTrace.Chain first.attempt.step.result.state toUpper second.attempt.step.before
  lowerWritten : toLower.flatMap ApplicationTrace.Step.written = []
  upperWritten : toUpper.flatMap ApplicationTrace.Step.written = []
  lowerEmitted : toLower.flatMap ApplicationTrace.Step.emitted = []
  upperEmitted : toUpper.flatMap ApplicationTrace.Step.emitted = []

theorem WriteBatch.writer_member (batch : WriteBatch cut actor lower upper first second) :
    batch.writer ∈ applicationSteps cut.endpoints actor := by
  rw [first.attempt.same, batch.lowerSplit]
  simp

theorem WriteBatch.lower_coordinate (batch : WriteBatch cut actor lower upper first second) :
    (first.attempt.prior.flatMap ApplicationTrace.Step.emitted).length =
      (batch.prior.flatMap ApplicationTrace.Step.emitted).length := by
  have quiet : batch.writer.emitted = [] := by simp only [ApplicationTrace.Step.emitted, ApplicationTrace.emitted, batch.event]
  simp only [batch.lowerSplit, List.flatMap_append, List.flatMap_cons, quiet, batch.lowerEmitted,
    List.append_nil]

theorem WriteBatch.upper_coordinate (batch : WriteBatch cut actor lower upper first second) :
    (second.attempt.prior.flatMap ApplicationTrace.Step.emitted).length =
      (batch.prior.flatMap ApplicationTrace.Step.emitted).length + lower.length := by
  have quiet : batch.writer.emitted = [] := by simp only [ApplicationTrace.Step.emitted, ApplicationTrace.emitted, batch.event]
  simp only [batch.upperSplit, List.flatMap_append, List.flatMap_cons, quiet, batch.lowerEmitted,
    first.emitted, batch.upperEmitted, List.nil_append, List.append_nil, List.length_append]

structure SenderStart (cut : Cut input complete) (actor : Actor) (lower upper : List UInt8)
    (first : Original cut actor lower) (second : Original cut actor upper) where
  recovery : Recovery.State
  reaction : AckReaction.State
  head : Recovery.Outstanding
  tail : Recovery.Outstanding
  runtime : (endpoint cut.endpoints actor).recovery = some recovery
  ackRuntime : (endpoint cut.endpoints actor).ackReaction = some reaction
  ackEmpty : reaction.work.pending = []
  window : lower.length ≤ (endpoint cut.endpoints actor).sendWindow
  ledger : recovery.outstanding = [head, tail]
  headCount : head.count = lower.length
  tailCount : tail.count = upper.length
  sent : (endpoint cut.endpoints actor).core.sent = lower ++ upper
  pending : (endpoint cut.endpoints actor).pending = []
  emptyHeld : (endpoint cut.endpoints actor).receiveStore.held = []
  headSequence : (endpoint cut.endpoints actor).core.sendUna = first.attempt.output.packet.segment.sequence
  headTime : head.sentAt = first.attempt.step.before.now
  tailTime : tail.sentAt = second.attempt.step.before.now
  headID : head.id = 0
  tailID : tail.id = 1
  headStart : head.start = 0
  tailStart : tail.start = lower.length
  headLast : head.lastAt = head.sentAt
  tailLast : tail.lastAt = tail.sentAt
  headRetried : head.retried = false
  tailRetried : tail.retried = false
  nextID : recovery.nextId = 2
  frontier : recovery.frontier = lower.length + upper.length
  rto : recovery.rto = 1000
  deadline : recovery.deadline = some (head.lastAt + recovery.rto)
  timedOut : recovery.lastTimedOut = none
  timeoutCount : recovery.timeoutCount = 0
  duplicate : recovery.duplicateAcks = 1
  valid : (endpoint cut.endpoints actor).Valid
  coherent : Endpoint.RecoveryCoherent (endpoint cut.endpoints actor)
  prepared : Endpoint.AckPrepared (endpoint cut.endpoints actor)
  storage : Endpoint.StorageCoherent (endpoint cut.endpoints actor)
  clocked : recovery.Clocked

structure HeldStart (cut : Cut input complete) (receiver : Actor) (lower upper : List UInt8) where
  run : ReceiveReassembly.Run
  held : (endpoint cut.endpoints receiver).receiveStore.held = [run]
  position : run.position = lower.length
  bytes : run.bytes = upper
  receipt : run.receipt = 0
  frontier : (endpoint cut.endpoints receiver).receiveStore.frontier = 0
  nextID : (endpoint cut.endpoints receiver).receiveStore.nextID = 1
  seenGap : (endpoint cut.endpoints receiver).receiveStore.seenGap = true
  unread : (endpoint cut.endpoints receiver).core.received = []
  source : CampusTCPGapFacts.ReceiptDelivery cut.report (applicationSteps cut.endpoints receiver.other)
    receiver (applicationSteps cut.endpoints receiver) run
  recovery : Recovery.State
  reaction : AckReaction.State
  runtime : (endpoint cut.endpoints receiver).recovery = some recovery
  ackRuntime : (endpoint cut.endpoints receiver).ackReaction = some reaction
  idle : recovery.outstanding = []
  valid : (endpoint cut.endpoints receiver).Valid
  coherent : Endpoint.RecoveryCoherent (endpoint cut.endpoints receiver)
  prepared : Endpoint.AckPrepared (endpoint cut.endpoints receiver)
  storage : Endpoint.StorageCoherent (endpoint cut.endpoints receiver)

theorem HeldStart.metadata (held : HeldStart cut actor lower upper) :
    held.run.metadata = ⟨held.source.origin.allocation.input.packet.segment,
      held.source.origin.allocation.input.packet.header, held.source.origin.issuer.before.now⟩ :=
  held.source.origin.fields.2.1

def seed (complete : H.Completed input.active input.passive) : Actor → Endpoint.State
  | .client => complete.certificate.activeSeed
  | .server => complete.certificate.passiveSeed

theorem endpoint_chain (cut : Cut input complete) (actor : Actor) :
    ApplicationTrace.Chain (seed complete actor) (applicationSteps cut.endpoints actor) (endpoint cut.endpoints actor) := by
  cases actor
  · exact cut.endpoints.client.chain
  · exact cut.endpoints.server.chain

theorem seed_empty_held (complete : H.Completed input.active input.passive) (actor : Actor) :
    (seed complete actor).receiveStore.held = [] := by
  cases actor
  · exact complete.certificate.empty_receiveStore.1
  · exact complete.certificate.empty_receiveStore.2

theorem held_source (cut : Cut input complete) (actor : Actor) (run : ReceiveReassembly.Run)
    (member : run ∈ (endpoint cut.endpoints actor).receiveStore.held) :
    Nonempty (CampusTCPGapFacts.ReceiptDelivery cut.report (applicationSteps cut.endpoints actor.other)
      actor (applicationSteps cut.endpoints actor) run) := by
  obtain ⟨origin⟩ := (endpoint_chain cut actor).held_run_origin (seed_empty_held complete actor) run member
  obtain ⟨receives⟩ := CampusTCPRecoveryRoundOrigins.Report.receives cut.report complete cut.endpoints cut.connection actor
  exact CampusTCPGapFacts.receipt_delivery receives origin

structure PendingLower (cut : Cut input complete) (original : Original cut actor lower) where
  serviceIndex : Nat
  served : Served input
  stored : cut.report.final.services[serviceIndex]? = some served
  source : served.ticket.value.produced = original.produced
  emission : WireForwarding.Emission served.ticket.value.source.packet
  emitted : served.evidence.output = some emission
  packetID : Nat
  pending : cut.report.final.custody.pendingID (Transit.linkAt serviceIndex) = some packetID

theorem PendingLower.link_pending (selected : PendingLower cut original) :
    CampusTCPDeliveryEnabled.LinkPending cut.report.final selected.serviceIndex := by
  obtain ⟨packet, member, _, linked⟩ := cut.report.final.custody.pendingID_source _ _ selected.pending
  exact ⟨packet, member, linked⟩

structure GapInitial (cut : Cut input complete) (sender : Actor) (lower upper : List UInt8) where
  basis : StartupBasis cut
  lowerNonempty : lower ≠ []
  upperNonempty : upper ≠ []
  lowerSource : Original cut sender lower
  upperSource : Original cut sender upper
  write : WriteBatch cut sender lower upper lowerSource upperSource
  flight : SenderStart cut sender lower upper lowerSource upperSource
  receiver : HeldStart cut sender.other lower upper
  selected : PendingLower cut lowerSource
  gateway : GatewayStart cut basis
  lowerRange : LowerRange gateway sender lower

structure NativeEnv (cut : Cut input complete) (entry : NetfilterNAT.Entry) where
  ingress : Actor → I.InterfaceRef
  paths : ∀ actor, CampusTCPRoundGateway.Native (input.contextFor .standby)
    (beforeService input cut.report.final .standby) (ingress actor) entry actor.direction actor.nextHop
  owners : ∀ actor, cut.report.final.owner actor = .standby
  configured : input.configured .standby = true
  unpaused : cut.report.final.assignmentPaused = false
  installation : InstalledCheckpoint
  installed : cut.report.final.installation = some installation
  sealed : cut.report.final.primarySealed = true
  fenced : cut.report.final.primaryFenced = true

theorem NativeEnv.route (env : NativeEnv cut entry) (actor : Actor) : RouteReady cut.report.final actor := by
  refine ⟨env.unpaused, ?_, ?_, ?_⟩
  · rw [env.owners actor]; exact env.configured
  · intro primary
    rw [env.owners actor] at primary
    cases primary
  · intro _
    rw [env.installed]
    rfl

theorem NativeEnv.service_phase (env : NativeEnv cut entry) :
    CampusTCPGatewayEnabled.ServicePhaseReady cut.report.final .standby := by
  constructor
  · intro same
    cases same
  · intro _
    exact ⟨env.unpaused, by rw [env.installed]; rfl⟩

def Cut.ofPrefix (report : Report input events) (count : Nat) (within : count ≤ report.steps.length)
    (accepted : (report.steps.take count).all (·.result.supported) = true)
    (endpoints : Applications complete)
    (connected : (CampusTCPSchedule.Report.cut report count within).final.connection = .application complete endpoints) :
    Cut input complete :=
  ⟨_, CampusTCPSchedule.Report.cut report count within, accepted, rfl, endpoints, connected⟩

end Netlib.Check.CampusTCPGapProgressStart
