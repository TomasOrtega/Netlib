import Netlib.Check.CampusTCPRecoveryStartupCurrentEntry
import Netlib.Check.CampusTCPRecoveryStartupCurrentHeaders

/-!
# Current lane coordinates from the actual service prefix

Packet roles follow the installed binding and real source headers.
Window markers keep their actual values through empty ACK processing.
-/

namespace Netlib.Check.CampusTCPRecoveryStartupCurrentCoordinates

open Packet Protocol Protocol.TCP CampusTCPModel
open CampusTCPRecoveryStartupTransport (ServiceChain beforeTransport afterTransport PrimaryServices)
open CampusTCPRecoveryStartupCurrentEntry (History EntryMatches)
open CampusTCPRecoveryStartupControlLedger (ServiceControl)
open CampusTCPRecoveryStartupPhase (Coordinates sideDirection)

variable {input : Input} {baseEvents events : List CampusTCPModel.Event}
variable {base : Report input baseEvents} {report : Report input events}
variable {current : C.State input.active input.passive} {header : Header}

structure HeaderControl (current : C.State input.active input.passive) (entry : NetfilterNAT.Entry) (served : Served input) extends ServiceControl current served where
  header : served.ticket.value.source.packet.header = entry.flow.input (sideDirection occurrence.actor)

private theorem actor_of_syn (shape : TCPHandshakeRecovery.PacketShape active passive actor kind packet)
    (flags : packet.packet.segment.flags = 2) : actor = .active := by
  have same := shape.profile.1.symm.trans flags
  cases selected : kind <;> simp only [selected, TCPHandshakeRecovery.Kind.flags] at same
  · simpa only [selected, TCPHandshakeRecovery.Kind.actor] using shape.actorEq
  all_goals contradiction

private theorem service_role (chain : ServiceChain initial services final) (served : Served input) (member : served ∈ services)
    (profile : CampusTCPStartupNative.Profile context selectedBefore input.zone header)
    (source : HeaderControl current profile.entry served)
    (shape : TCPHandshakeRecovery.PacketShape input.active input.passive source.occurrence.actor source.occurrence.kind served.ticket.value.source.asInput)
    (matching : EntryMatches profile.entry final.admission)
    (processing : CampusTCPService.Processing (input.contextFor served.ticket.value.gateway) served.before served.ticket.value.source input.zone served.mode) :
    processing.prepared.attachment.direction = sideDirection source.occurrence.actor := by
  cases selected : served.before.admission.phase.entry with
  | none =>
    have empty : served.before.admission.phase = .empty := by
      cases phase : served.before.admission.phase <;> first | rfl | (rw [phase] at selected; cases selected)
    have allowed := AdmissionExecution.Result.legacy_empty processing.admitted empty
    simp only [Admission.Allowed, empty] at allowed
    have actor := actor_of_syn shape allowed.2.2.1
    rw [actor]
    exact allowed.2.1
  | some old =>
    have finalEntry := CampusTCPRecoveryStartupFold.ServiceChain.before_entry chain served member selected
    have oldEntry := matching old finalEntry
    have entryEq := (CampusTCPRecoveryStartupTransport.admission_before_entry processing.admitted selected).trans oldEntry
    apply CampusTCPRecoveryStartupKeys.direction_of_key profile.compatible
    have key := processing.prepared.attached
    change processing.prepared.attachment.entry.flow.key processing.prepared.attachment.direction =
      (input.zone, served.ticket.value.source.packet.header) at key
    rw [entryEq, source.header] at key
    exact key.trans (Prod.ext (profile.zone_eq _).symm rfl)

private theorem service_coordinates (chain : ServiceChain initial services final) (served : Served input) (member : served ∈ services)
    (profile : CampusTCPStartupNative.Profile context selectedBefore input.zone header)
    (source : HeaderControl current profile.entry served)
    (inventory : TCPHandshakeRecovery.OutputInventory current)
    (matching : EntryMatches profile.entry final.admission)
    (prior : Coordinates input.active input.passive served.before.admission.phase) :
    Coordinates input.active input.passive served.evidence.admission.phase := by
  have shape : TCPHandshakeRecovery.PacketShape input.active input.passive source.occurrence.actor source.occurrence.kind served.ticket.value.source.asInput := by
    simpa only [source.packet] using inventory source.occurrence source.member
  cases operation : served.evidence.operation with
  | earlyDrop denied => simpa only [CampusTCPService.Evidence.admission, operation] using prior
  | processed permitted processing =>
    have selected : served.evidence.processing = some processing := by simp only [CampusTCPService.Evidence.processing, operation]
    have states := served.evidence.processing_states processing selected
    have role := service_role chain served member profile source shape matching processing
    have after := prior.admitted processing.admitted shape role
    rw [states.2]
    rcases AdmissionExecution.commit_cases processing.admitted processing.outcome.state _ processing.committed with kept | reset
    · rw [kept.1]
      exact after
    · rw [reset.1]
      trivial

theorem ServiceChain.coordinates (chain : ServiceChain initial services final)
    (profile : CampusTCPStartupNative.Profile context selectedBefore input.zone header)
    (sources : ∀ served ∈ services, Nonempty (HeaderControl current profile.entry served))
    (inventory : TCPHandshakeRecovery.OutputInventory current)
    (matching : EntryMatches profile.entry final.admission)
    (prior : Coordinates input.active input.passive initial.admission.phase) :
    Coordinates input.active input.passive final.admission.phase := by
  induction chain with
  | nil => exact prior
  | cons served primary before rest ih =>
    obtain ⟨source⟩ := sources served List.mem_cons_self
    have old : Coordinates input.active input.passive served.before.admission.phase := by
      change Coordinates input.active input.passive (beforeTransport served).admission.phase
      rw [before]
      exact prior
    have after := service_coordinates (.cons served primary before rest) served List.mem_cons_self profile source inventory matching old
    exact ih (fun selected member => sources selected (List.mem_cons_of_mem served member)) matching after

theorem History.header_control (history : History base report)
    (profile : CampusTCPStartupNative.Profile (input.contextFor .primary) (beforeService input base.final .primary) input.zone header)
    (cold : CampusTCPRecoveryStartupCold.ColdProfile report) (connected : report.final.connection = .recovering current)
    (primary : PrimaryServices report)
    (opening : CampusTCPRecoveryStartupCurrentSources.ProducedAt report source) (syn : source.occurrence.kind = .syn)
    (original : source.occurrence.packet.packet.header = header)
    (served : Served input) (member : served ∈ history.suffix.filterMap (·.result.service)) :
    Nonempty (HeaderControl current profile.entry served) := by
  have reachable := CampusTCPRecoveryStartupOrigins.Report.recoveryReachable report connected
  obtain ⟨control⟩ := history.service_control cold connected served member
  have matching := history.entry_matches profile cold connected opening syn original
  have openingActor : source.occurrence.actor = .active := by
    simpa only [syn, TCPHandshakeRecovery.Kind.actor] using (opening.shape connected).actorEq
  refine ⟨⟨control, ?_⟩⟩
  have same := congrArg (fun packet : Admission.Input => packet.packet.header) control.packet
  cases actor : control.occurrence.actor with
  | active =>
    have packetHeader := reachable.packet_inventory.same_header control.member (opening.recovering_member connected) (actor.trans openingActor.symm)
    exact same.trans (packetHeader.trans (original.trans profile.original.symm))
  | passive =>
    exact same.trans (CampusTCPRecoveryStartupCurrentHeaders.Report.passive_header report connected primary matching control.member actor)

theorem History.coordinates (history : History base report)
    (profile : CampusTCPStartupNative.Profile (input.contextFor .primary) (beforeService input base.final .primary) input.zone header)
    (cold : CampusTCPRecoveryStartupCold.ColdProfile report) (connected : report.final.connection = .recovering current)
    (primary : PrimaryServices report)
    (opening : CampusTCPRecoveryStartupCurrentSources.ProducedAt report source) (syn : source.occurrence.kind = .syn)
    (original : source.occurrence.packet.packet.header = header) :
    Coordinates input.active input.passive report.final.primary.transport.admission.phase := by
  apply ServiceChain.coordinates (CampusTCPRecoveryStartupTransport.Trace.service_chain history.trace history.primary) profile
    (fun served member => History.header_control history profile cold connected primary opening syn original served member)
    (CampusTCPRecoveryStartupOrigins.Report.recoveryReachable report connected).output_inventory
    (history.entry_matches profile cold connected opening syn original)
  change Coordinates input.active input.passive (beforeService input base.final .primary).admission.phase
  rw [profile.empty]
  trivial

end Netlib.Check.CampusTCPRecoveryStartupCurrentCoordinates
