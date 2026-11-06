import Netlib.Check.CampusTCPTwoProgressPaths
import Netlib.Check.CampusTCPTwoProgressReceive

namespace Netlib.Check.CampusTCPTwoProgressPaths

open Packet Protocol Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current next : Cut input complete} {sender actor : Actor} {gateway : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {fields : Produced input.active input.passive → Prop} {ingress : I.InterfaceRef} {target : Header}

private theorem prefix_lookup {α : Type} {before after : List α} {index : Nat} {value : α}
    (retained : before <+: after) (stored : before[index]? = some value) : after[index]? = some value := by
  obtain ⟨extra, history⟩ := retained
  rw [← history, List.getElem?_append_left (List.getElem?_eq_some_iff.mp stored).1]
  exact stored

def Output.reframe (path : Output current actor fields)
    (stored : next.report.final.outputs[path.index]? = some path.produced) : Output next actor fields :=
  ⟨path.index, path.produced, stored, path.actor, path.application, path.fields⟩

def Output.retain (path : Output current actor fields)
    (outputs : current.report.final.outputs <+: next.report.final.outputs) : Output next actor fields :=
  path.reframe (prefix_lookup outputs path.stored)

def Output.clock (path : Output current actor fields) (placement : CampusTCPRecoveryRoundPhaseBase.At current next) :
    Output next actor fields := path.reframe (by rw [placement.frame.outputs]; exact path.stored)

def Ingress.reframe (path : Ingress current actor fields)
    (stored : next.report.final.outputs[path.output.index]? = some path.output.produced)
    (custody : next.report.final.custody.pendingID (Transit.ingressAt path.output.index) = some path.packetID) :
    Ingress next actor fields := ⟨path.output.reframe stored, path.packetID, custody⟩

def Ingress.retain (path : Ingress current actor fields)
    (outputs : current.report.final.outputs <+: next.report.final.outputs)
    (custody : next.report.final.custody.pendingID (Transit.ingressAt path.output.index) = some path.packetID) :
    Ingress next actor fields := path.reframe (prefix_lookup outputs path.output.stored) custody

def Ingress.clock (path : Ingress current actor fields) (placement : CampusTCPRecoveryRoundPhaseBase.At current next) :
    Ingress next actor fields := path.reframe
  (by rw [placement.frame.outputs]; exact path.output.stored)
  (by rw [placement.frame.custody]; exact path.custody)

def TicketPath.reframe (path : TicketPath current actor fields gateway ingress)
    (stored : next.report.final.outputs[path.output.index]? = some path.output.produced)
    (pending : path.ticket ∈ next.report.final.work.pending) : TicketPath next actor fields gateway ingress :=
  ⟨path.output.reframe stored, path.ticket, pending, path.outputIndex, path.produced, path.gateway, path.ingress⟩

def TicketPath.retain (path : TicketPath current actor fields gateway ingress)
    (outputs : current.report.final.outputs <+: next.report.final.outputs)
    (pending : path.ticket ∈ next.report.final.work.pending) : TicketPath next actor fields gateway ingress :=
  path.reframe (prefix_lookup outputs path.output.stored) pending

def TicketPath.clock (path : TicketPath current actor fields gateway ingress)
    (placement : CampusTCPRecoveryRoundPhaseBase.At current next) : TicketPath next actor fields gateway ingress :=
  path.reframe (by rw [placement.frame.outputs]; exact path.output.stored)
    (by rw [placement.frame.work]; exact path.pending)

def Link.reframe (path : Link current actor fields target)
    (stored : next.report.final.services[path.index]? = some path.served)
    (custody : next.report.final.custody.pendingID (Transit.linkAt path.index) = some path.packetID) : Link next actor fields target :=
  ⟨path.index, path.served, stored, path.emission, path.emitted, path.actor, path.application, path.fields,
    path.target, path.packetID, custody⟩

def Link.retain (path : Link current actor fields target)
    (services : current.report.final.services <+: next.report.final.services)
    (custody : next.report.final.custody.pendingID (Transit.linkAt path.index) = some path.packetID) : Link next actor fields target :=
  path.reframe (prefix_lookup services path.stored) custody

def Link.clock (path : Link current actor fields target) (placement : CampusTCPRecoveryRoundPhaseBase.At current next) :
    Link next actor fields target := path.reframe (by rw [placement.frame.services]; exact path.stored)
  (by rw [placement.frame.custody]; exact path.custody)

theorem Ingress.custody_item (path : Ingress current actor fields) :
    ∃ item ∈ current.report.final.custody.pending, item.id = path.packetID ∧
      item.value.payload = .ingress path.output.index path.output.produced := by
  obtain ⟨item, member, identity, selected⟩ := current.report.final.custody.pendingID_source _ _ path.custody
  obtain ⟨produced, payload⟩ := CampusTCPCustodyFacts.ingress_stage _ _ selected
  have source := CampusTCPCustodyFacts.Report.sources current.report item (List.mem_append_right _ member)
  rw [payload] at source
  have same : produced = path.output.produced := Option.some.inj (source.symm.trans path.output.stored)
  subst produced
  exact ⟨item, member, identity, payload⟩

theorem Link.custody_item (path : Link current actor fields target) :
    ∃ item ∈ current.report.final.custody.pending, item.id = path.packetID ∧
      item.value.payload = .link path.index path.served path.emission path.emitted := by
  obtain ⟨item, member, identity, selected⟩ := current.report.final.custody.pendingID_source _ _ path.custody
  obtain ⟨served, emission, emitted, payload⟩ := CampusTCPCustodyFacts.link_stage _ _ selected
  have source := CampusTCPCustodyFacts.Report.sources current.report item (List.mem_append_right _ member)
  rw [payload] at source
  have same : served = path.served := Option.some.inj (source.symm.trans path.stored)
  subst served
  have sameEmission : emission = path.emission := Option.some.inj (emitted.symm.trans path.emitted)
  subst emission
  exact ⟨item, member, identity, payload⟩

variable {part : CampusTCPTwoProgressSender.Part} {lane otherLane : M.Lane} {count : Nat}
variable {native : NativeEnv cut gateway initial.gatewayState.session.entry}

def DataIngress.reframe (path : DataIngress initial current part lane)
    (stored : next.report.final.outputs[path.output.index]? = some path.output.produced)
    (custody : next.report.final.custody.pendingID (Transit.ingressAt path.output.index) = some path.packetID) :
    DataIngress initial next part lane :=
  {
    toIngress := path.toIngress.reframe stored custody
    phase := path.phase
    outputRef := path.outputRef
    packetRef := path.packetRef
  }

def DataIngress.retain (path : DataIngress initial current part lane)
    (outputs : current.report.final.outputs <+: next.report.final.outputs)
    (custody : next.report.final.custody.pendingID (Transit.ingressAt path.output.index) = some path.packetID) :
    DataIngress initial next part lane :=
  {
    toIngress := path.toIngress.retain outputs custody
    phase := path.phase
    outputRef := path.outputRef
    packetRef := path.packetRef
  }

def DataIngress.clock (path : DataIngress initial current part lane) (placement : CampusTCPRecoveryRoundPhaseBase.At current next) :
    DataIngress initial next part lane :=
  {
    toIngress := path.toIngress.clock placement
    phase := path.phase
    outputRef := path.outputRef
    packetRef := path.packetRef
  }

def DataIngress.reindex (path : DataIngress initial current part lane) (same : otherLane = lane) : DataIngress initial current part otherLane :=
  {
    toIngress := path.toIngress
    phase := by rw [same]; exact path.phase
    outputRef := by rw [same]; exact path.outputRef
    packetRef := by rw [same]; exact path.packetRef
  }

theorem DataIngress.packet_at (path : DataIngress initial current part lane) :
    CampusTCPGapProgressMonitor.packetAt lane.toGap = some path.packetID := by
  simp only [CampusTCPGapProgressMonitor.packetAt, CampusTCPTwoProgressMonitor.Lane.toGap, path.phase, path.packetRef]

theorem DataIngress.next_action (path : DataIngress initial current part lane) (config : M.Config) :
    CampusTCPGapProgressMonitor.nextAction config.toConfig current.report.final lane.toGap = some (.assign path.output.index (config.toConfig.ingress config.sender)) :=
  path.action config

theorem DataIngress.exposed_packet (path : DataIngress initial current part lane) (config : M.Config) :
    CampusTCPTwoProgressMonitor.exposedPacket config current.report.final lane = some path.packetID := by
  simp only [CampusTCPTwoProgressMonitor.exposedPacket, path.action config, bind, Option.bind]
  exact path.packet_at

def DataTicket.reframe (path : DataTicket initial native current part lane)
    (stored : next.report.final.outputs[path.output.index]? = some path.output.produced)
    (pending : path.ticket ∈ next.report.final.work.pending) :
    DataTicket initial native next part lane :=
  {
    toTicketPath := path.toTicketPath.reframe stored pending
    phase := path.phase
    outputRef := path.outputRef
    ticketRef := path.ticketRef
  }

def DataTicket.retain (path : DataTicket initial native current part lane)
    (outputs : current.report.final.outputs <+: next.report.final.outputs)
    (pending : path.ticket ∈ next.report.final.work.pending) :
    DataTicket initial native next part lane :=
  {
    toTicketPath := path.toTicketPath.retain outputs pending
    phase := path.phase
    outputRef := path.outputRef
    ticketRef := path.ticketRef
  }

def DataTicket.clock (path : DataTicket initial native current part lane) (placement : CampusTCPRecoveryRoundPhaseBase.At current next) :
    DataTicket initial native next part lane :=
  {
    toTicketPath := path.toTicketPath.clock placement
    phase := path.phase
    outputRef := path.outputRef
    ticketRef := path.ticketRef
  }

def DataTicket.reindex (path : DataTicket initial native current part lane) (same : otherLane = lane) : DataTicket initial native current part otherLane :=
  {
    toTicketPath := path.toTicketPath
    phase := by rw [same]; exact path.phase
    outputRef := by rw [same]; exact path.outputRef
    ticketRef := by rw [same]; exact path.ticketRef
  }

theorem DataTicket.packet_at (path : DataTicket initial native current part lane) :
    CampusTCPGapProgressMonitor.packetAt lane.toGap = none := by
  simp only [CampusTCPGapProgressMonitor.packetAt, CampusTCPTwoProgressMonitor.Lane.toGap, path.phase]

theorem DataTicket.next_action (path : DataTicket initial native current part lane) (config : M.Config) :
    CampusTCPGapProgressMonitor.nextAction config.toConfig current.report.final lane.toGap = some (.serve path.ticket.id) :=
  path.action config

theorem DataTicket.exposed_packet (path : DataTicket initial native current part lane) (config : M.Config) :
    CampusTCPTwoProgressMonitor.exposedPacket config current.report.final lane = none := by
  simp only [CampusTCPTwoProgressMonitor.exposedPacket, path.action config, bind, Option.bind]
  exact path.packet_at

def DataLink.reframe (path : DataLink initial current part lane)
    (stored : next.report.final.services[path.index]? = some path.served)
    (custody : next.report.final.custody.pendingID (Transit.linkAt path.index) = some path.packetID) :
    DataLink initial next part lane :=
  {
    toLink := path.toLink.reframe stored custody
    phase := path.phase
    serviceRef := path.serviceRef
    packetRef := path.packetRef
  }

def DataLink.retain (path : DataLink initial current part lane)
    (services : current.report.final.services <+: next.report.final.services)
    (custody : next.report.final.custody.pendingID (Transit.linkAt path.index) = some path.packetID) :
    DataLink initial next part lane :=
  {
    toLink := path.toLink.retain services custody
    phase := path.phase
    serviceRef := path.serviceRef
    packetRef := path.packetRef
  }

def DataLink.clock (path : DataLink initial current part lane) (placement : CampusTCPRecoveryRoundPhaseBase.At current next) :
    DataLink initial next part lane :=
  {
    toLink := path.toLink.clock placement
    phase := path.phase
    serviceRef := path.serviceRef
    packetRef := path.packetRef
  }

def DataLink.reindex (path : DataLink initial current part lane) (same : otherLane = lane) : DataLink initial current part otherLane :=
  {
    toLink := path.toLink
    phase := by rw [same]; exact path.phase
    serviceRef := by rw [same]; exact path.serviceRef
    packetRef := by rw [same]; exact path.packetRef
  }

theorem DataLink.packet_at (path : DataLink initial current part lane) :
    CampusTCPGapProgressMonitor.packetAt lane.toGap = some path.packetID := by
  simp only [CampusTCPGapProgressMonitor.packetAt, CampusTCPTwoProgressMonitor.Lane.toGap, path.phase, path.packetRef]

theorem DataLink.next_action (path : DataLink initial current part lane) (config : M.Config) :
    CampusTCPGapProgressMonitor.nextAction config.toConfig current.report.final lane.toGap = some (.deliver path.index path.emission.bytes true) :=
  path.action config

theorem DataLink.exposed_packet (path : DataLink initial current part lane) (config : M.Config) :
    CampusTCPTwoProgressMonitor.exposedPacket config current.report.final lane = some path.packetID := by
  simp only [CampusTCPTwoProgressMonitor.exposedPacket, path.action config, bind, Option.bind]
  exact path.packet_at

def AckIngress.reframe (path : AckIngress initial current count lane)
    (stored : next.report.final.outputs[path.output.index]? = some path.output.produced)
    (custody : next.report.final.custody.pendingID (Transit.ingressAt path.output.index) = some path.packetID) :
    AckIngress initial next count lane :=
  {
    toIngress := path.toIngress.reframe stored custody
    phase := path.phase
    outputRef := path.outputRef
    packetRef := path.packetRef
  }

def AckIngress.retain (path : AckIngress initial current count lane)
    (outputs : current.report.final.outputs <+: next.report.final.outputs)
    (custody : next.report.final.custody.pendingID (Transit.ingressAt path.output.index) = some path.packetID) :
    AckIngress initial next count lane :=
  {
    toIngress := path.toIngress.retain outputs custody
    phase := path.phase
    outputRef := path.outputRef
    packetRef := path.packetRef
  }

def AckIngress.clock (path : AckIngress initial current count lane) (placement : CampusTCPRecoveryRoundPhaseBase.At current next) :
    AckIngress initial next count lane :=
  {
    toIngress := path.toIngress.clock placement
    phase := path.phase
    outputRef := path.outputRef
    packetRef := path.packetRef
  }

def AckIngress.reindex (path : AckIngress initial current count lane) (same : otherLane = lane) : AckIngress initial current count otherLane :=
  {
    toIngress := path.toIngress
    phase := by rw [same]; exact path.phase
    outputRef := by rw [same]; exact path.outputRef
    packetRef := by rw [same]; exact path.packetRef
  }

theorem AckIngress.packet_at (path : AckIngress initial current count lane) :
    CampusTCPGapProgressMonitor.packetAt lane.toGap = some path.packetID := by
  simp only [CampusTCPGapProgressMonitor.packetAt, CampusTCPTwoProgressMonitor.Lane.toGap, path.phase, path.packetRef]

theorem AckIngress.next_action (path : AckIngress initial current count lane) (config : M.Config) :
    CampusTCPGapProgressMonitor.nextAction config.toConfig current.report.final lane.toGap = some (.assign path.output.index (config.toConfig.ingress config.sender.other)) :=
  path.action config

theorem AckIngress.exposed_packet (path : AckIngress initial current count lane) (config : M.Config) :
    CampusTCPTwoProgressMonitor.exposedPacket config current.report.final lane = some path.packetID := by
  simp only [CampusTCPTwoProgressMonitor.exposedPacket, path.action config, bind, Option.bind]
  exact path.packet_at

def AckTicket.reframe (path : AckTicket initial native current count lane)
    (stored : next.report.final.outputs[path.output.index]? = some path.output.produced)
    (pending : path.ticket ∈ next.report.final.work.pending) :
    AckTicket initial native next count lane :=
  {
    toTicketPath := path.toTicketPath.reframe stored pending
    phase := path.phase
    outputRef := path.outputRef
    ticketRef := path.ticketRef
  }

def AckTicket.retain (path : AckTicket initial native current count lane)
    (outputs : current.report.final.outputs <+: next.report.final.outputs)
    (pending : path.ticket ∈ next.report.final.work.pending) :
    AckTicket initial native next count lane :=
  {
    toTicketPath := path.toTicketPath.retain outputs pending
    phase := path.phase
    outputRef := path.outputRef
    ticketRef := path.ticketRef
  }

def AckTicket.clock (path : AckTicket initial native current count lane) (placement : CampusTCPRecoveryRoundPhaseBase.At current next) :
    AckTicket initial native next count lane :=
  {
    toTicketPath := path.toTicketPath.clock placement
    phase := path.phase
    outputRef := path.outputRef
    ticketRef := path.ticketRef
  }

def AckTicket.reindex (path : AckTicket initial native current count lane) (same : otherLane = lane) : AckTicket initial native current count otherLane :=
  {
    toTicketPath := path.toTicketPath
    phase := by rw [same]; exact path.phase
    outputRef := by rw [same]; exact path.outputRef
    ticketRef := by rw [same]; exact path.ticketRef
  }

theorem AckTicket.packet_at (path : AckTicket initial native current count lane) :
    CampusTCPGapProgressMonitor.packetAt lane.toGap = none := by
  simp only [CampusTCPGapProgressMonitor.packetAt, CampusTCPTwoProgressMonitor.Lane.toGap, path.phase]

theorem AckTicket.next_action (path : AckTicket initial native current count lane) (config : M.Config) :
    CampusTCPGapProgressMonitor.nextAction config.toConfig current.report.final lane.toGap = some (.serve path.ticket.id) :=
  path.action config

theorem AckTicket.exposed_packet (path : AckTicket initial native current count lane) (config : M.Config) :
    CampusTCPTwoProgressMonitor.exposedPacket config current.report.final lane = none := by
  simp only [CampusTCPTwoProgressMonitor.exposedPacket, path.action config, bind, Option.bind]
  exact path.packet_at

def AckLink.reframe (path : AckLink initial current count lane)
    (stored : next.report.final.services[path.index]? = some path.served)
    (custody : next.report.final.custody.pendingID (Transit.linkAt path.index) = some path.packetID) :
    AckLink initial next count lane :=
  {
    toLink := path.toLink.reframe stored custody
    phase := path.phase
    serviceRef := path.serviceRef
    packetRef := path.packetRef
  }

def AckLink.retain (path : AckLink initial current count lane)
    (services : current.report.final.services <+: next.report.final.services)
    (custody : next.report.final.custody.pendingID (Transit.linkAt path.index) = some path.packetID) :
    AckLink initial next count lane :=
  {
    toLink := path.toLink.retain services custody
    phase := path.phase
    serviceRef := path.serviceRef
    packetRef := path.packetRef
  }

def AckLink.clock (path : AckLink initial current count lane) (placement : CampusTCPRecoveryRoundPhaseBase.At current next) :
    AckLink initial next count lane :=
  {
    toLink := path.toLink.clock placement
    phase := path.phase
    serviceRef := path.serviceRef
    packetRef := path.packetRef
  }

def AckLink.reindex (path : AckLink initial current count lane) (same : otherLane = lane) : AckLink initial current count otherLane :=
  {
    toLink := path.toLink
    phase := by rw [same]; exact path.phase
    serviceRef := by rw [same]; exact path.serviceRef
    packetRef := by rw [same]; exact path.packetRef
  }

theorem AckLink.packet_at (path : AckLink initial current count lane) :
    CampusTCPGapProgressMonitor.packetAt lane.toGap = some path.packetID := by
  simp only [CampusTCPGapProgressMonitor.packetAt, CampusTCPTwoProgressMonitor.Lane.toGap, path.phase, path.packetRef]

theorem AckLink.next_action (path : AckLink initial current count lane) (config : M.Config) :
    CampusTCPGapProgressMonitor.nextAction config.toConfig current.report.final lane.toGap = some (.deliver path.index path.emission.bytes true) :=
  path.action config

theorem AckLink.exposed_packet (path : AckLink initial current count lane) (config : M.Config) :
    CampusTCPTwoProgressMonitor.exposedPacket config current.report.final lane = some path.packetID := by
  simp only [CampusTCPTwoProgressMonitor.exposedPacket, path.action config, bind, Option.bind]
  exact path.packet_at

theorem DataLink.receive_link (path : DataLink initial current part lane) :
    CampusTCPTwoProgressReceive.Link initial current (part.offset lower) (part.bytes lower upper)
      path.index path.served path.emission path.emitted :=
  ⟨path.stored, path.application, path.toLink.pending, path.actor, path.fields, path.target⟩

theorem DataLink.packet_fields (path : DataLink initial current part lane) :
    CampusTCPTwoProgressReceiver.PacketFields initial (part.offset lower) (part.bytes lower upper) path.emission.asInput :=
  path.receive_link.packet_fields

end Netlib.Check.CampusTCPTwoProgressPaths
