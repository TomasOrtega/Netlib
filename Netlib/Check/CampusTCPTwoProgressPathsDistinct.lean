import Netlib.Check.CampusTCPTwoProgressOriginalPath

/-!
# Distinct current paths for the two original records

Sequence geometry separates the stored packet fields.
Current history and custody then separate their operation identities.
-/

namespace Netlib.Check.CampusTCPTwoProgressPathsDistinct

open Protocol Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart CampusTCPTwoProgressWire
open CampusTCPTwoProgressPaths

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current : Cut input complete} {sender : Actor} {gateway : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {native : NativeEnv cut gateway initial.gatewayState.session.entry}
variable {firstLane secondLane : CampusTCPTwoProgressMonitor.Lane}

theorem lower_length_lt_modulus (initial : TwoWriteInitial cut sender gateway lower upper) : lower.length < Seq.modulus := by
  have epoch := initial.geometry.epoch
  unfold Seq.halfSpace Seq.modulus at *
  omega

theorem sequence_ne (first : DataFields initial 0 lower firstProduced)
    (second : DataFields initial lower.length upper secondProduced) :
    firstProduced.source.packet.segment.sequence ≠ secondProduced.source.packet.segment.sequence := by
  intro same
  have coordinates := first.sequence.symm.trans (same.trans second.sequence)
  have distances := congrArg (Seq.distance (endpoint cut.endpoints sender).core.sendNext) coordinates
  rw [Seq.distance_add, Seq.distance_add, Nat.zero_mod,
    Nat.mod_eq_of_lt (lower_length_lt_modulus initial)] at distances
  have positive := List.length_pos_iff.mpr initial.lowerNonempty
  omega

theorem produced_ne (first : DataFields initial 0 lower firstProduced)
    (second : DataFields initial lower.length upper secondProduced) : firstProduced ≠ secondProduced := by
  intro same
  exact sequence_ne first second (congrArg (fun produced => produced.source.packet.segment.sequence) same)

theorem output_index_ne
    (first : Output current sender (DataFields initial 0 lower))
    (second : Output current sender (DataFields initial lower.length upper)) : first.index ≠ second.index := by
  intro same
  have stored := first.stored
  rw [same] at stored
  exact produced_ne first.fields second.fields (Option.some.inj (stored.symm.trans second.stored))

theorem ticket_id_ne (first : DataTicket initial native current .lower firstLane)
    (second : DataTicket initial native current .upper secondLane) : first.ticket.id ≠ second.ticket.id := by
  intro same
  have valid := CampusTCPOrigins.Report.work_valid current.report
  obtain ⟨completed, _, identity⟩ := Theory.Outstanding.complete_item current.report.final.work first.ticket valid first.pending
  have selected := completed.item_eq valid second.ticket second.pending same.symm
  have tickets : first.ticket = second.ticket := identity.symm.trans selected
  apply produced_ne first.output.fields second.output.fields
  exact first.produced.symm.trans ((congrArg (fun item => item.value.produced) tickets).trans second.produced)

theorem service_index_ne (first : DataLink initial current .lower firstLane)
    (second : DataLink initial current .upper secondLane) : first.index ≠ second.index := by
  intro same
  have stored := first.stored
  rw [same] at stored
  have served : first.served = second.served := Option.some.inj (stored.symm.trans second.stored)
  exact produced_ne first.fields second.fields (congrArg (fun served => served.ticket.value.produced) served)

private theorem pending_eq (first second : Theory.PacketCustody.Item (Transit input))
    (firstMember : first ∈ current.report.final.custody.pending)
    (secondMember : second ∈ current.report.final.custody.pending) (same : first.id = second.id) : first = second := by
  obtain ⟨resolved, _⟩ := Theory.PacketCustody.resolve_completes current.report.final.custody first firstMember .dropped
  have valid := CampusTCPCustodyFacts.Report.valid current.report
  exact (resolved.item_eq valid first firstMember rfl).symm.trans (resolved.item_eq valid second secondMember same.symm)

theorem ingress_packet_ne (first : DataIngress initial current .lower firstLane)
    (second : DataIngress initial current .upper secondLane) : first.packetID ≠ second.packetID := by
  intro same
  obtain ⟨left, leftMember, leftID, leftPayload⟩ := first.toIngress.custody_item
  obtain ⟨right, rightMember, rightID, rightPayload⟩ := second.toIngress.custody_item
  have items := pending_eq left right leftMember rightMember (leftID.trans (same.trans rightID.symm))
  have payload := congrArg (fun item => item.value.payload) items
  rw [leftPayload, rightPayload] at payload
  exact produced_ne first.output.fields second.output.fields
    (congrArg CampusTCPTwoProgressLossHistory.transitSource payload)

theorem ingress_link_packet_ne (first : DataIngress initial current .lower firstLane)
    (second : DataLink initial current .upper secondLane) : first.packetID ≠ second.packetID := by
  intro same
  obtain ⟨left, leftMember, leftID, leftPayload⟩ := first.toIngress.custody_item
  obtain ⟨right, rightMember, rightID, rightPayload⟩ := second.toLink.custody_item
  have items := pending_eq left right leftMember rightMember (leftID.trans (same.trans rightID.symm))
  have payload := congrArg (fun item => item.value.payload) items
  rw [leftPayload, rightPayload] at payload
  cases payload

theorem link_ingress_packet_ne (first : DataLink initial current .lower firstLane)
    (second : DataIngress initial current .upper secondLane) : first.packetID ≠ second.packetID := by
  intro same
  obtain ⟨left, leftMember, leftID, leftPayload⟩ := first.toLink.custody_item
  obtain ⟨right, rightMember, rightID, rightPayload⟩ := second.toIngress.custody_item
  have items := pending_eq left right leftMember rightMember (leftID.trans (same.trans rightID.symm))
  have payload := congrArg (fun item => item.value.payload) items
  rw [leftPayload, rightPayload] at payload
  cases payload

theorem link_packet_ne (first : DataLink initial current .lower firstLane)
    (second : DataLink initial current .upper secondLane) : first.packetID ≠ second.packetID := by
  intro same
  obtain ⟨left, leftMember, leftID, leftPayload⟩ := first.toLink.custody_item
  obtain ⟨right, rightMember, rightID, rightPayload⟩ := second.toLink.custody_item
  have items := pending_eq left right leftMember rightMember (leftID.trans (same.trans rightID.symm))
  have payload := congrArg (fun item => item.value.payload) items
  rw [leftPayload, rightPayload] at payload
  exact produced_ne first.fields second.fields (congrArg CampusTCPTwoProgressLossHistory.transitSource payload)

end Netlib.Check.CampusTCPTwoProgressPathsDistinct

namespace Netlib.Check.CampusTCPTwoProgressOriginalPath

open Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart CampusTCPTwoProgressPathsDistinct

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current : Cut input complete} {sender : Actor} {gateway : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {native : NativeEnv cut gateway initial.gatewayState.session.entry}
variable {part : CampusTCPTwoProgressSender.Part} {original : CampusTCPTwoProgressSender.Original initial part}
variable {lane firstLane secondLane : CampusTCPTwoProgressMonitor.Lane}
variable {firstOriginal : CampusTCPTwoProgressSender.Original initial .lower}
variable {secondOriginal : CampusTCPTwoProgressSender.Original initial .upper}

def InFlight.command (path : InFlight initial native current part original lane)
    (config : CampusTCPTwoProgressMonitor.Config) : CampusTCPRoundMonitor.Action :=
  match path with
  | .ingress path _ => .assign path.output.index (config.toConfig.ingress config.sender)
  | .ticket path _ => .serve path.ticket.id
  | .link path _ => .deliver path.index path.emission.bytes true

theorem InFlight.command_next (path : InFlight initial native current part original lane)
    (config : CampusTCPTwoProgressMonitor.Config) :
    CampusTCPGapProgressMonitor.nextAction config.toConfig current.report.final lane.toGap = some (path.command config) := by
  cases path with
  | ingress path _ => exact path.action config
  | ticket path _ => exact path.action config
  | link path _ => exact path.action config

theorem InFlight.command_ne (first : InFlight initial native current .lower firstOriginal firstLane)
    (second : InFlight initial native current .upper secondOriginal secondLane)
    (config : CampusTCPTwoProgressMonitor.Config) : first.command config ≠ second.command config := by
  intro same
  cases first with
  | ingress first _ =>
    cases second with
    | ingress second _ => exact output_index_ne first.output second.output (CampusTCPRoundMonitor.Action.assign.inj same).1
    | ticket second _ => cases same
    | link second _ => cases same
  | ticket first _ =>
    cases second with
    | ingress second _ => cases same
    | ticket second _ => exact ticket_id_ne first second (CampusTCPRoundMonitor.Action.serve.inj same)
    | link second _ => cases same
  | link first _ =>
    cases second with
    | ingress second _ => cases same
    | ticket second _ => cases same
    | link second _ => exact service_index_ne first second (CampusTCPRoundMonitor.Action.deliver.inj same).1

theorem InFlight.command_event_ne (first : InFlight initial native current .lower firstOriginal firstLane)
    (second : InFlight initial native current .upper secondOriginal secondLane)
    (config : CampusTCPTwoProgressMonitor.Config) : (first.command config).event ≠ (second.command config).event := by
  intro same
  have actions := congrArg CampusTCPRoundMonitor.actionOf same
  simp only [CampusTCPRoundMonitor.Action.actionOf_event] at actions
  exact first.command_ne second config (Option.some.inj actions)

def InFlight.packet (path : InFlight initial native current part original lane) : Option Nat :=
  match path with
  | .ingress path _ => some path.packetID
  | .ticket _ _ => none
  | .link path _ => some path.packetID

theorem InFlight.exposed_packet (path : InFlight initial native current part original lane)
    (config : CampusTCPTwoProgressMonitor.Config) :
    CampusTCPTwoProgressMonitor.exposedPacket config current.report.final lane = path.packet := by
  cases path with
  | ingress path _ => exact path.exposed_packet config
  | link path _ => exact path.exposed_packet config
  | ticket path _ =>
    unfold CampusTCPTwoProgressMonitor.exposedPacket
    rw [path.action config]
    simp only [bind, Option.bind, CampusTCPGapProgressMonitor.packetAt,
      CampusTCPTwoProgressMonitor.Lane.toGap, path.phase, InFlight.packet]

theorem InFlight.exposed_ne (first : InFlight initial native current .lower firstOriginal firstLane)
    (second : InFlight initial native current .upper secondOriginal secondLane)
    (config : CampusTCPTwoProgressMonitor.Config)
    (firstFound : CampusTCPTwoProgressMonitor.exposedPacket config current.report.final firstLane = some firstID)
    (secondFound : CampusTCPTwoProgressMonitor.exposedPacket config current.report.final secondLane = some secondID) : firstID ≠ secondID := by
  rw [first.exposed_packet config] at firstFound
  rw [second.exposed_packet config] at secondFound
  intro same
  cases first with
  | ticket path _ => cases firstFound
  | ingress first _ =>
    have left := Option.some.inj firstFound
    cases second with
    | ticket path _ => cases secondFound
    | ingress second _ => exact ingress_packet_ne first second (left.trans (same.trans (Option.some.inj secondFound).symm))
    | link second _ => exact ingress_link_packet_ne first second (left.trans (same.trans (Option.some.inj secondFound).symm))
  | link first _ =>
    have left := Option.some.inj firstFound
    cases second with
    | ticket path _ => cases secondFound
    | ingress second _ => exact link_ingress_packet_ne first second (left.trans (same.trans (Option.some.inj secondFound).symm))
    | link second _ => exact link_packet_ne first second (left.trans (same.trans (Option.some.inj secondFound).symm))

end Netlib.Check.CampusTCPTwoProgressOriginalPath
