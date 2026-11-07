import Netlib.Check.CampusTCPRecoveryStartupTransport
import Netlib.Check.CampusTCPRecoveryStartupCold
import Netlib.Check.CampusTCPRecoveryStartupSources

/-!
# Exact observed controls in current startup admission

The ledger cites actual retained occurrences and admitted observations.
Failed fresh processing may return to empty admission.
-/

namespace Netlib.Check.CampusTCPRecoveryStartupControlLedger

open Protocol Protocol.TCP CampusTCPModel
open CampusTCPRecoveryStartupTransport (ServiceChain beforeTransport afterTransport phaseRank)

variable {input : Input} {current : C.State input.active input.passive}

structure SeenControl (current : C.State input.active input.passive) (observations : List Admission.Seen)
    (entry : NetfilterNAT.Entry) (direction : FlowNAT.Direction) (kind : TCPHandshakeRecovery.Kind) where
  occurrence : C.Emission
  member : occurrence ∈ current.emissions
  kindEq : occurrence.kind = kind
  known : AdmissionStartupRecovery.KnownControl observations entry direction occurrence.packet.packet.segment

def ControlLedger (current : C.State input.active input.passive) (state : Admission.State) : Prop :=
  ∀ entry, state.phase.entry = some entry →
    Nonempty (SeenControl current state.observations entry .original .syn) ∧
      (2 ≤ phaseRank state.phase → Nonempty (SeenControl current state.observations entry .reply .synAck))

theorem ControlLedger.initial : ControlLedger current Admission.State.initial := by
  intro entry selected
  cases selected

theorem SeenControl.append (seen : SeenControl current observations entry direction kind) (extra : List Admission.Seen) :
    Nonempty (SeenControl current (observations ++ extra) entry direction kind) :=
  ⟨⟨seen.occurrence, seen.member, seen.kindEq, seen.known.append extra⟩⟩

private theorem kind_syn (shape : TCPHandshakeRecovery.OutputShape active passive occurrence)
    (flags : occurrence.packet.packet.segment.flags = 2) : occurrence.kind = .syn := by
  have same := shape.profile.1.symm.trans flags
  cases kind : occurrence.kind <;> simp only [kind, TCPHandshakeRecovery.Kind.flags] at same
  · rfl
  all_goals contradiction

private theorem kind_synAck (shape : TCPHandshakeRecovery.OutputShape active passive occurrence)
    (flags : occurrence.packet.packet.segment.flags = 18) : occurrence.kind = .synAck := by
  have same := shape.profile.1.symm.trans flags
  cases kind : occurrence.kind <;> simp only [kind, TCPHandshakeRecovery.Kind.flags] at same
  · contradiction
  · rfl
  all_goals contradiction

private theorem current_seen (result : AdmissionExecution.Result mode before packet lifecycle prepared)
    (same : lifecycle.packet = packet.packet.header) (member : occurrence ∈ current.emissions)
    (packetEq : packet = occurrence.packet) (kind : occurrence.kind = selectedKind)
    (direction : prepared.attachment.direction = selectedDirection) :
    Nonempty (SeenControl current (AdmissionExecution.Result.state result).observations
      prepared.attachment.entry selectedDirection selectedKind) := by
  have known : AdmissionStartupRecovery.KnownControl (AdmissionExecution.Result.state result).observations
      prepared.attachment.entry prepared.attachment.direction packet.packet.segment := by
    apply AdmissionStartupRecovery.KnownControl.of_observe packet lifecycle prepared same
    rw [AdmissionExecution.Result.ledger]
    exact List.mem_append_right _ (List.mem_singleton_self _)
  have segment := congrArg (fun value : Admission.Input => value.packet.segment) packetEq
  have fixed := (congrArg (fun value => AdmissionStartupRecovery.KnownControl
    (AdmissionExecution.Result.state result).observations prepared.attachment.entry prepared.attachment.direction value) segment).mp known
  rw [direction] at fixed
  exact ⟨⟨occurrence, member, kind, fixed⟩⟩

theorem ControlLedger.admitted (prior : ControlLedger current before)
    (result : AdmissionExecution.Result mode before packet lifecycle prepared)
    (same : lifecycle.packet = packet.packet.header) (member : occurrence ∈ current.emissions)
    (packetEq : packet = occurrence.packet)
    (shape : TCPHandshakeRecovery.OutputShape input.active input.passive occurrence) :
    ControlLedger current (AdmissionExecution.Result.state result) := by
  intro entry selected
  have chosen : prepared.attachment.entry = entry := by
    rw [AdmissionExecution.Result.selected_entry] at selected
    exact Option.some.inj selected
  cases phase : before.phase with
  | empty =>
    have legacy := AdmissionExecution.Result.legacy_empty result phase
    simp only [Admission.Allowed, phase] at legacy
    have kind := kind_syn shape (by rw [← packetEq]; exact legacy.2.2.1)
    obtain ⟨offer, read, after⟩ := result.learned_syn phase
    refine ⟨?_, ?_⟩
    · rw [← chosen]
      exact current_seen result same member packetEq kind legacy.2.1
    · intro level
      simp only [after, phaseRank] at level
      omega
  | syn old iss window mss =>
    have oldEntry : before.phase.entry = some old := by rw [phase]; rfl
    have attached := CampusTCPRecoveryStartupTransport.admission_before_entry result oldEntry
    have equal : old = entry := attached.symm.trans chosen
    have sameEntry : before.phase.entry = some entry := oldEntry.trans (congrArg some equal)
    obtain ⟨syn⟩ := (prior entry sameEntry).1
    refine ⟨?_, ?_⟩
    · rw [AdmissionExecution.Result.ledger]
      exact syn.append _
    · intro level
      rcases AdmissionExecution.Result.legacy_or_stutter result with legacy | ⟨modeEq, stutter⟩
      · simp only [Admission.Allowed, phase] at legacy
        have kind := kind_synAck shape (by rw [← packetEq]; exact legacy.2.2.2.1.1)
        rw [← chosen]
        exact current_seen result same member packetEq kind legacy.2.2.1
      · subst mode
        have after := result.phase.trans (AdmissionStartupRecovery.nextPhase_stutter stutter result.admitted)
        simp only [after, phase, phaseRank] at level
        omega
  | synAck old clientISS clientWindow serverISS serverWindow clientMSS serverMSS =>
    have oldEntry : before.phase.entry = some old := by rw [phase]; rfl
    have attached := CampusTCPRecoveryStartupTransport.admission_before_entry result oldEntry
    have equal : old = entry := attached.symm.trans chosen
    have sameEntry : before.phase.entry = some entry := oldEntry.trans (congrArg some equal)
    obtain ⟨syn⟩ := (prior entry sameEntry).1
    obtain ⟨synAck⟩ := (prior entry sameEntry).2 (by simp only [phase, phaseRank]; decide)
    rw [AdmissionExecution.Result.ledger]
    exact ⟨syn.append _, fun _ => synAck.append _⟩
  | data session =>
    have oldEntry : before.phase.entry = some session.entry := by rw [phase]; rfl
    have attached := CampusTCPRecoveryStartupTransport.admission_before_entry result oldEntry
    have equal : session.entry = entry := attached.symm.trans chosen
    obtain ⟨syn⟩ := (prior session.entry oldEntry).1
    obtain ⟨synAck⟩ := (prior session.entry oldEntry).2 (by simp only [phase, phaseRank]; decide)
    rw [AdmissionExecution.Result.ledger, ← equal]
    exact ⟨syn.append _, fun _ => synAck.append _⟩


structure ServiceControl (current : C.State input.active input.passive) (served : Served input) where
  occurrence : C.Emission
  member : occurrence ∈ current.emissions
  packet : served.ticket.value.source.asInput = occurrence.packet

theorem Processing.control_ledger (value : CampusTCPService.Processing context before source zone mode)
    (prior : ControlLedger current before.admission) (occurrence : C.Emission) (member : occurrence ∈ current.emissions)
    (packet : source.asInput = occurrence.packet)
    (shape : TCPHandshakeRecovery.OutputShape input.active input.passive occurrence) : ControlLedger current value.nextAdmission := by
  have admitted := prior.admitted value.admitted rfl member packet shape
  rcases AdmissionExecution.commit_cases value.admitted value.outcome.state _ value.committed with kept | reset
  · rw [kept.1]
    exact admitted
  · rw [reset.1]
    exact ControlLedger.initial

theorem Evidence.control_ledger (value : CampusTCPService.Evidence context before source zone ingress mode)
    (prior : ControlLedger current before.admission) (occurrence : C.Emission) (member : occurrence ∈ current.emissions)
    (packet : source.asInput = occurrence.packet)
    (shape : TCPHandshakeRecovery.OutputShape input.active input.passive occurrence) : ControlLedger current value.admission := by
  cases value with
  | mk checks operation =>
    cases operation with
    | earlyDrop denied => exact prior
    | processed permitted processing => exact Processing.control_ledger processing prior occurrence member packet shape

theorem ServiceChain.control_ledger (history : ServiceChain initial services final)
    (controls : ∀ served ∈ services, Nonempty (ServiceControl current served))
    (inventory : TCPHandshakeRecovery.OutputInventory current) (prior : ControlLedger current initial.admission) :
    ControlLedger current final.admission := by
  induction history with
  | nil => exact prior
  | cons served primary before rest ih =>
    obtain ⟨control⟩ := controls served List.mem_cons_self
    apply ih (fun selected member => controls selected (List.mem_cons_of_mem served member))
    have old : ControlLedger current served.before.admission := by
      change ControlLedger current (beforeTransport served).admission
      rw [before]
      exact prior
    exact Evidence.control_ledger served.evidence old control.occurrence control.member control.packet
      (inventory control.occurrence control.member)

theorem Report.service_control (report : Report input events) (cold : CampusTCPRecoveryStartupCold.ColdProfile report)
    (connected : report.final.connection = .recovering current) (served : Served input) (member : served ∈ report.final.services) :
    Nonempty (ServiceControl current served) := by
  have only := CampusTCPRecoveryStartupCold.Report.recovery_services report cold served member
  obtain ⟨source⟩ := CampusTCPRecoveryStartupSources.Report.service_source report served member
  cases production : served.ticket.value.produced with
  | startup actual output present | application actor actual output origin =>
    simp only [production, Produced.isRecovery] at only
    cases only
  | recovery actual occurrence present =>
    refine ⟨⟨occurrence, source.recovering_member actual occurrence present production current connected, ?_⟩⟩
    change served.ticket.value.produced.output = occurrence.packet
    rw [production]
    rfl

theorem Report.control_ledger (report : Report input events) (cold : CampusTCPRecoveryStartupCold.ColdProfile report)
    (primary : CampusTCPRecoveryStartupTransport.PrimaryServices report) (connected : report.final.connection = .recovering current) :
    ControlLedger current report.final.primary.transport.admission := by
  apply ServiceChain.control_ledger (CampusTCPRecoveryStartupTransport.Report.service_chain report primary)
  · intro served member
    apply Report.service_control report cold connected served
    rw [CampusTCPPrimaryTransport.Report.services report]
    exact member
  · exact (CampusTCPRecoveryStartupOrigins.Report.recoveryReachable report connected).output_inventory
  · exact ControlLedger.initial

theorem SeenControl.known_for (seen : SeenControl current observations entry direction kind)
    (inventory : TCPHandshakeRecovery.PacketInventory current) (member : selected ∈ current.emissions)
    (control : TCPHandshakeRecovery.TemplateKind kind) (selectedKind : selected.kind = kind) :
    AdmissionStartupRecovery.KnownControl observations entry direction selected.packet.packet.segment := by
  have packet := inventory.same_template member seen.member (selectedKind ▸ control) (selectedKind.trans seen.kindEq.symm)
  rw [packet]
  exact seen.known

theorem Report.known_syn (report : Report input events) (cold : CampusTCPRecoveryStartupCold.ColdProfile report)
    (primary : CampusTCPRecoveryStartupTransport.PrimaryServices report) (connected : report.final.connection = .recovering current)
    (entry : report.final.primary.transport.admission.phase.entry = some selectedEntry)
    (member : selected ∈ current.emissions) (kind : selected.kind = .syn) :
    AdmissionStartupRecovery.KnownControl report.final.primary.transport.admission.observations selectedEntry .original selected.packet.packet.segment := by
  obtain ⟨seen⟩ := (Report.control_ledger report cold primary connected selectedEntry entry).1
  exact seen.known_for (CampusTCPRecoveryStartupOrigins.Report.recoveryReachable report connected).packet_inventory member (Or.inl rfl) kind

theorem Report.known_synAck (report : Report input events) (cold : CampusTCPRecoveryStartupCold.ColdProfile report)
    (primary : CampusTCPRecoveryStartupTransport.PrimaryServices report) (connected : report.final.connection = .recovering current)
    (entry : report.final.primary.transport.admission.phase.entry = some selectedEntry)
    (level : 2 ≤ phaseRank report.final.primary.transport.admission.phase)
    (member : selected ∈ current.emissions) (kind : selected.kind = .synAck) :
    AdmissionStartupRecovery.KnownControl report.final.primary.transport.admission.observations selectedEntry .reply selected.packet.packet.segment := by
  obtain ⟨seen⟩ := (Report.control_ledger report cold primary connected selectedEntry entry).2 level
  exact seen.known_for (CampusTCPRecoveryStartupOrigins.Report.recoveryReachable report connected).packet_inventory member (Or.inr rfl) kind

end Netlib.Check.CampusTCPRecoveryStartupControlLedger
