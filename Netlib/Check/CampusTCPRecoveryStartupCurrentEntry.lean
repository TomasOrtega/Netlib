import Netlib.Check.CampusTCPRecoveryStartupControlLedger
import Netlib.Check.CampusTCPRecoveryStartupCurrentSources
import Netlib.Check.CampusTCPStartupNative

/-!
# The native binding in the current startup prefix

Fresh SYN processing uses the installed candidate. Existing admission keeps
that same binding through every actual later service.
-/

namespace Netlib.Check.CampusTCPRecoveryStartupCurrentEntry

open Packet Protocol Protocol.TCP CampusTCPModel
open CampusTCPRecoveryStartupTransport (ServiceChain beforeTransport afterTransport)

namespace S
export CampusTCPRecoveryStartupCurrentSources (ProducedAt)
end S
namespace L
export CampusTCPRecoveryStartupControlLedger (ServiceControl)
end L

variable {input : Input} {baseEvents events : List CampusTCPModel.Event}
variable {base : Report input baseEvents} {report : Report input events}
variable {current : C.State input.active input.passive} {header : Header}

structure History (base : Report input baseEvents) (report : Report input events) where
  suffix : List (Step input)
  events : List CampusTCPModel.Event
  remaining : List CampusTCPModel.Event
  trace : Trace input base.final events suffix report.final remaining
  history : report.steps = base.steps ++ suffix
  transport : ∀ actual ∈ suffix, CampusTCPRoundEnvironment.TransportOnly actual.event
  primary : ∀ served ∈ suffix.filterMap (·.result.service), served.ticket.value.gateway = .primary

def EntryMatches (entry : NetfilterNAT.Entry) (state : Admission.State) : Prop :=
  ∀ selected, state.phase.entry = some selected → selected = entry

theorem EntryMatches.empty (empty : state.phase = .empty) : EntryMatches entry state := by
  intro selected chosen
  rw [empty] at chosen
  cases chosen

private theorem Processing.entry_matches (value : CampusTCPService.Processing context before source zone mode)
    (prior : EntryMatches entry before.admission)
    (fresh : before.admission.phase = .empty → value.prepared.attachment.entry = entry) :
    EntryMatches entry value.nextAdmission := by
  intro selected chosen
  rcases AdmissionExecution.commit_cases value.admitted value.outcome.state _ value.committed with kept | reset
  · have same : value.prepared.attachment.entry = selected := by
      rw [kept.1, AdmissionExecution.Result.selected_entry] at chosen
      exact Option.some.inj chosen
    rw [← same]
    cases phase : before.admission.phase with
    | empty => exact fresh phase
    | syn old iss window mss | synAck old iss window serverISS serverWindow mss serverMSS =>
      have selected : before.admission.phase.entry = some old := by rw [phase]; rfl
      exact (CampusTCPRecoveryStartupTransport.admission_before_entry value.admitted selected).trans (prior old selected)
    | data session =>
      have selected : before.admission.phase.entry = some session.entry := by rw [phase]; rfl
      exact (CampusTCPRecoveryStartupTransport.admission_before_entry value.admitted selected).trans (prior session.entry selected)
  · rw [reset.1] at chosen
    cases chosen

private theorem Evidence.entry_matches (value : CampusTCPService.Evidence context before source zone ingress mode)
    (prior : EntryMatches entry before.admission)
    (fresh : ∀ processing, value.processing = some processing →
      before.admission.phase = .empty → processing.prepared.attachment.entry = entry) : EntryMatches entry value.admission := by
  cases value with
  | mk checks operation =>
    cases operation with
    | earlyDrop denied => exact prior
    | processed permitted processing => exact Processing.entry_matches processing prior (fresh processing rfl)

theorem ServiceChain.entry_matches (chain : ServiceChain initial services final)
    (prior : EntryMatches entry initial.admission)
    (fresh : ∀ served ∈ services, ∀ processing, served.evidence.processing = some processing →
      served.before.admission.phase = .empty → processing.prepared.attachment.entry = entry) :
    EntryMatches entry final.admission := by
  induction chain with
  | nil => exact prior
  | cons served primary before rest ih =>
    apply ih
    · apply Evidence.entry_matches served.evidence
      · change EntryMatches entry (beforeTransport served).admission
        rw [before]
        exact prior
      · exact fresh served List.mem_cons_self
    · exact fun selected member => fresh selected (List.mem_cons_of_mem served member)

theorem History.service_environment (history : History base report) (served : Served input)
    (member : served ∈ history.suffix.filterMap (·.result.service)) :
    (beforeService input base.final .primary).environment = served.before.environment := by
  obtain ⟨actual, stored, recorded⟩ := List.mem_filterMap.mp member
  have environment := CampusTCPRoundEnvironment.Trace.each_environment history.trace history.transport actual stored
  have same := CampusTCPRoundEnvironment.service_environment _ _ environment .primary
  obtain ⟨_, _, _, _, _, _, before, _⟩ := CampusTCPOrigins.service_origin actual served recorded
  rw [before, history.primary served member]
  exact same

theorem History.service_control (history : History base report) (cold : CampusTCPRecoveryStartupCold.ColdProfile report)
    (connected : report.final.connection = .recovering current) (served : Served input)
    (member : served ∈ history.suffix.filterMap (·.result.service)) : Nonempty (L.ServiceControl current served) := by
  apply CampusTCPRecoveryStartupControlLedger.Report.service_control report cold connected served
  rw [CampusTCPPrimaryTransport.Report.services report, history.history, List.filterMap_append]
  exact List.mem_append_right _ member

private theorem actor_of_syn (shape : TCPHandshakeRecovery.OutputShape active passive occurrence)
    (flags : occurrence.packet.packet.segment.flags = 2) : occurrence.actor = .active := by
  have same := shape.profile.1.symm.trans flags
  cases kind : occurrence.kind <;> simp only [kind, TCPHandshakeRecovery.Kind.flags] at same
  · simpa only [kind, TCPHandshakeRecovery.Kind.actor] using shape.actorEq
  all_goals contradiction

private theorem fresh_entry (profile : CampusTCPStartupNative.Profile context initial zone header)
    (environment : initial.environment = before.environment)
    (value : CampusTCPService.Processing processingContext before source zone mode)
    (empty : before.admission.phase = .empty) (sourceHeader : source.packet.header = header) :
    value.prepared.attachment.entry = profile.entry := by
  have allowed := AdmissionExecution.Result.legacy_empty value.admitted empty
  simp only [Admission.Allowed, empty] at allowed
  have candidate := (ConntrackLifecycle.prepare_fresh before.tracker _ value.prepared value.attached allowed.1).2.2.2
  change (if (before.tracker.model.lookup zone source.packet.header).isNone then
    some (before.configuration.nat.candidate zone source.packet.header) else none) = some value.prepared.attachment.entry at candidate
  split at candidate
  · have chosen := Option.some.inj candidate
    have configuration := congrArg CampusTCPService.Before.Environment.configuration environment
    change initial.configuration = before.configuration at configuration
    rw [← configuration, sourceHeader] at chosen
    exact chosen.symm
  · cases candidate

theorem History.entry_matches (history : History base report)
    (profile : CampusTCPStartupNative.Profile (input.contextFor .primary) (beforeService input base.final .primary) input.zone header)
    (cold : CampusTCPRecoveryStartupCold.ColdProfile report) (connected : report.final.connection = .recovering current)
    (opening : S.ProducedAt report source) (syn : source.occurrence.kind = .syn)
    (original : source.occurrence.packet.packet.header = header) :
    EntryMatches profile.entry report.final.primary.transport.admission := by
  have reachable := CampusTCPRecoveryStartupOrigins.Report.recoveryReachable report connected
  have openingMember := opening.recovering_member connected
  have openingShape := opening.shape connected
  have openingActor : source.occurrence.actor = .active := by
    simpa only [syn, TCPHandshakeRecovery.Kind.actor] using openingShape.actorEq
  apply ServiceChain.entry_matches (CampusTCPRecoveryStartupTransport.Trace.service_chain history.trace history.primary)
  · exact EntryMatches.empty profile.empty
  · intro served member processing selected empty
    obtain ⟨control⟩ := history.service_control cold connected served member
    have shape := reachable.output_shape control.member
    have legacy := AdmissionExecution.Result.legacy_empty processing.admitted empty
    simp only [Admission.Allowed, empty] at legacy
    have flags : control.occurrence.packet.packet.segment.flags = 2 := by
      rw [← control.packet]
      exact legacy.2.2.1
    have actor := actor_of_syn shape flags
    have headerEq := reachable.packet_inventory.same_header control.member openingMember (actor.trans openingActor.symm)
    have packetHeader : served.ticket.value.source.packet.header = header := by
      exact (congrArg (fun packet : Admission.Input => packet.packet.header) control.packet).trans (headerEq.trans original)
    exact fresh_entry profile (history.service_environment served member) processing empty packetHeader

end Netlib.Check.CampusTCPRecoveryStartupCurrentEntry
