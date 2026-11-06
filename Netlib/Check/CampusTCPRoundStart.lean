import Netlib.Check.CampusTCPStartupTransport
import Netlib.Check.CampusTCPRoundSetup
import Netlib.Check.CampusTCPRoundLocal
import Netlib.Check.CampusTCPRoundGateway
import Netlib.Check.CampusTCPGatewayEnabled

/-!
# Initial cut for one campus TCP round

The cut retains the actual startup, gateway history, setup operations, and write.
The fixed environment supplies policy and ingress checks once.
-/

namespace Netlib.Check.CampusTCPRoundStart

open Protocol CampusTCPModel CampusTCPEnabled CampusTCPRoundSetup

structure Request (input : Input) where
  bytes : List UInt8
  nonempty : bytes ≠ []
  pendingFits : bytes.length ≤ input.active.pendingLimit
  mssFits : bytes.length ≤ TCP.Handshake.effectiveMSS input.active (TCP.Handshake.receiveOffer input.passive)
  receiveFits : bytes.length ≤ input.passive.capacity

variable {input : Input} {events : List CampusTCPModel.Event} {report : Report input events}
variable {complete : H.Completed input.active input.passive} {request : Request input}

theorem active_valid (complete : H.Completed input.active input.passive) : input.active.Valid := by
  have valid := complete.certificate.activePending.localValid
  rw [complete.certificate.pending_fields.1, complete.activeConfig] at valid
  exact valid

theorem passive_valid (complete : H.Completed input.active input.passive) : input.passive.Valid := by
  have valid := complete.certificate.passivePending.localValid
  rw [complete.certificate.pending_fields.2.2.1, complete.passiveConfig] at valid
  exact valid

theorem Request.positive (request : Request input) : 0 < request.bytes.length :=
  List.length_pos_iff.mpr request.nonempty

theorem Request.peer_mss (request : Request input) (complete : H.Completed input.active input.passive) :
    request.bytes.length ≤ (TCP.Handshake.receiveOffer input.passive).limit :=
  Nat.le_trans request.mssFits (TCP.Handshake.effectiveMSS_bounds input.active _ (active_valid complete)).2.1

theorem Request.epoch (request : Request input) (complete : H.Completed input.active input.passive) :
    request.bytes.length + 2 < TCP.Seq.halfSpace := by
  have capacity := (passive_valid complete).1
  have fits := request.receiveFits
  simp only [TCP.Seq.halfSpace]
  omega

structure Initial (report : Report input events) (complete : H.Completed input.active input.passive)
    (request : Request input) where
  history : CampusTCPFacts.StartupHistory report complete
  clean : CampusTCPStartupTransport.CleanServices history
  start : PreparedStart report complete request.bytes
  entry : NetfilterNAT.Entry
  session : TCP.Admission.Session
  aligned : CampusTCPStartupAlignment.Alignment input complete entry session
  phase : (CampusTCPModel.beforeService input start.next.report.final .primary).admission.phase = .data session
  valid : (CampusTCPModel.beforeService input start.next.report.final .primary).tracker.Valid
  records : (CampusTCPModel.beforeService input start.next.report.final .primary).tracker.records = [⟨entry, true⟩]

def Initial.state (initial : Initial report complete request) : State input := initial.start.next.report.final

def Initial.beforeService (initial : Initial report complete request) : CampusTCPService.Before :=
  CampusTCPModel.beforeService input initial.state .primary

theorem Initial.ofSetup (history : CampusTCPFacts.StartupHistory report complete)
    (clean : CampusTCPStartupTransport.CleanServices history) (start : PreparedStart report complete request.bytes) :
    Nonempty (Initial report complete request) := by
  obtain ⟨entry, session, phase, aligned, records⟩ := clean.aligned history
  have valid : report.final.primary.transport.tracker.Valid := by
    rw [clean.final_transport history]
    exact CampusTCPStartupAlignment.receipt_tracker_valid history.ack.receive.receipt
  have current := CampusTCPRoundLocal.setup_service start .primary
  refine ⟨⟨history, clean, start, entry, session, aligned, ?_, ?_, ?_⟩⟩
  all_goals rw [current]
  · exact phase
  · exact valid
  · exact records

theorem Initial.prepare (history : CampusTCPFacts.StartupHistory report complete)
    (clean : CampusTCPStartupTransport.CleanServices history) (supported : report.supported = true)
    (finished : report.remaining = [])
    (connection : report.final.connection = .application complete (Applications.initial complete))
    (request : Request input) : Nonempty (Initial report complete request) := by
  obtain ⟨start⟩ := CampusTCPRoundSetup.prepare report supported finished complete connection request.bytes request.pendingFits
  exact Initial.ofSetup history clean start

noncomputable def historyOfOrdinary (ordinary : CampusTCPStartupOrigins.Ordinary report)
    (complete : H.Completed input.active input.passive)
    (connection : report.final.connection = .application complete (Applications.initial complete)) :
    CampusTCPFacts.StartupHistory report complete :=
  Classical.choice (ordinary.history_exists complete (Applications.initial complete) connection)

theorem Initial.ofOrdinary (ordinary : CampusTCPStartupOrigins.Ordinary report)
    (connection : report.final.connection = .application complete (Applications.initial complete))
    (clean : CampusTCPStartupTransport.CleanServices (historyOfOrdinary ordinary complete connection))
    (start : PreparedStart report complete request.bytes) : Nonempty (Initial report complete request) :=
  Initial.ofSetup (historyOfOrdinary ordinary complete connection) clean start

theorem Initial.prepareOrdinary (ordinary : CampusTCPStartupOrigins.Ordinary report)
    (connection : report.final.connection = .application complete (Applications.initial complete))
    (clean : CampusTCPStartupTransport.CleanServices (historyOfOrdinary ordinary complete connection))
    (supported : report.supported = true) (finished : report.remaining = []) (request : Request input) :
    Nonempty (Initial report complete request) :=
  Initial.prepare (historyOfOrdinary ordinary complete connection) clean supported finished connection request

theorem Initial.send_ready (initial : Initial report complete request) :
    TCP.Endpoint.SendReady (endpoint initial.start.next.endpoints .client) request.bytes.length :=
  initial.start.send_ready request.nonempty request.mssFits request.receiveFits

structure NativeEnv (initial : Initial report complete request) where
  dataIngress : I.InterfaceRef
  ackIngress : I.InterfaceRef
  original : CampusTCPRoundGateway.Native (input.contextFor .primary) initial.beforeService
    dataIngress initial.entry .original "server"
  reply : CampusTCPRoundGateway.Native (input.contextFor .primary) initial.beforeService
    ackIngress initial.entry .reply "client"
  clientOwner : initial.state.owner .client = .primary
  serverOwner : initial.state.owner .server = .primary
  unpaused : initial.state.assignmentPaused = false
  unsealed : initial.state.primarySealed = false
  unfenced : initial.state.primaryFenced = false
  configured : input.configured .primary = true

theorem NativeEnv.owner (env : NativeEnv initial) (actor : Actor) : initial.state.owner actor = .primary := by
  cases actor
  · exact env.clientOwner
  · exact env.serverOwner

theorem NativeEnv.route (env : NativeEnv initial) (actor : Actor) : RouteReady initial.state actor := by
  refine ⟨env.unpaused, ?_, fun _ => ⟨env.unsealed, env.unfenced⟩, ?_⟩
  · rw [env.owner actor]
    exact env.configured
  · intro standby
    rw [env.owner actor] at standby
    cases standby

theorem NativeEnv.service_phase (env : NativeEnv initial) :
    CampusTCPGatewayEnabled.ServicePhaseReady initial.state .primary := by
  refine ⟨fun _ => ⟨env.unsealed, env.unfenced⟩, ?_⟩
  intro impossible
  cases impossible

theorem NativeEnv.owner_at (env : NativeEnv initial) (current : State input)
    (same : CampusTCPRoundEnvironment.environment initial.state = CampusTCPRoundEnvironment.environment current)
    (actor : Actor) : current.owner actor = .primary := by
  have owners := congrArg CampusTCPRoundEnvironment.Environment.owners same
  change initial.state.owners = current.owners at owners
  simpa only [State.owner, ← owners] using env.owner actor

theorem NativeEnv.route_at (env : NativeEnv initial) (current : State input)
    (same : CampusTCPRoundEnvironment.environment initial.state = CampusTCPRoundEnvironment.environment current)
    (actor : Actor) : RouteReady current actor := by
  have paused := congrArg CampusTCPRoundEnvironment.Environment.assignmentPaused same
  have sealed := congrArg CampusTCPRoundEnvironment.Environment.primarySealed same
  have fenced := congrArg CampusTCPRoundEnvironment.Environment.primaryFenced same
  refine ⟨paused.symm.trans env.unpaused, ?_, fun _ => ⟨sealed.symm.trans env.unsealed, fenced.symm.trans env.unfenced⟩, ?_⟩
  · rw [env.owner_at current same actor]
    exact env.configured
  · intro standby
    rw [env.owner_at current same actor] at standby
    cases standby

theorem NativeEnv.service_phase_at (env : NativeEnv initial) (current : State input)
    (same : CampusTCPRoundEnvironment.environment initial.state = CampusTCPRoundEnvironment.environment current) :
    CampusTCPGatewayEnabled.ServicePhaseReady current .primary := by
  have sealed := congrArg CampusTCPRoundEnvironment.Environment.primarySealed same
  have fenced := congrArg CampusTCPRoundEnvironment.Environment.primaryFenced same
  refine ⟨fun _ => ⟨sealed.symm.trans env.unsealed, fenced.symm.trans env.unfenced⟩, ?_⟩
  intro impossible
  cases impossible

theorem Initial.service_environment (initial : Initial report complete request) (current : State input)
    (same : CampusTCPRoundEnvironment.environment initial.state = CampusTCPRoundEnvironment.environment current) :
    initial.beforeService.environment = (CampusTCPModel.beforeService input current .primary).environment :=
  CampusTCPRoundEnvironment.service_environment initial.state current same .primary

end Netlib.Check.CampusTCPRoundStart
