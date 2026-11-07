import Netlib.Check.CampusTCPRecoveryStartupCurrentNative

/-!
# The exact target of a current startup link

The actual service chain fixes the entry. Its selected key fixes direction.
-/

namespace Netlib.Check.CampusTCPRecoveryStartupLinkTarget

open Packet Protocol Protocol.TCP CampusTCPModel
open CampusTCPRecoveryStartupPhase (sideDirection)

namespace J
export CampusTCPStartupJobs (Source Job PacketItem)
end J
namespace N
export CampusTCPRecoveryStartupCurrentNative (Current)
end N

variable {input : Input} {baseEvents events : List CampusTCPModel.Event}
variable {base : Report input baseEvents} {report : Report input events}
variable {current : C.State input.active input.passive} {header : Header}
variable {profile : CampusTCPStartupNative.Profile (input.contextFor .primary)
  (beforeService input base.final .primary) input.zone header}

theorem link_target (value : N.Current base profile report current)
    (item : J.PacketItem input) (serviceIndex : Nat) (served : Served input)
    (emission : W.Emission served.ticket.value.source.packet) (emitted : served.evidence.output = some emission)
    (source : J.Source input) (production : served.ticket.value.produced = source.produced)
    (payload : item.value.payload = .link serviceIndex served emission emitted)
    (pending : item ∈ report.final.custody.pending) :
    emission.target = profile.entry.flow.output (sideDirection source.occurrence.actor) := by
  let job : J.Job input := .link item serviceIndex served emission emitted source production payload
  have jobPending : job.Pending report.final := pending
  have member := CampusTCPRecoveryStartupCurrentSources.Job.recovering_member report job jobPending value.connected
  change source.occurrence ∈ current.emissions at member
  have sourceAt := CampusTCPCustodyFacts.Report.sources report item (List.mem_append_right _ pending)
  rw [payload] at sourceAt
  have stored : served ∈ report.steps.filterMap (·.result.service) := by
    rw [← CampusTCPPrimaryTransport.Report.services report]
    exact List.mem_of_getElem? sourceAt
  obtain ⟨processing, selected, actualEntry⟩ := CampusTCPRecoveryStartupFold.ServiceChain.output_entry
    (CampusTCPRecoveryStartupTransport.Report.service_chain report value.primary) served stored emission emitted
  have entryEq := value.entry _ actualEntry
  have packetHeader : served.ticket.value.source.packet.header =
      profile.entry.flow.input (sideDirection source.occurrence.actor) := by
    change served.ticket.value.produced.output.packet.header = _
    rw [production]
    exact value.headers source.occurrence member
  have key := AdmissionExecution.Result.selectedKey processing.admitted
  change processing.prepared.attachment.entry.flow.key processing.prepared.attachment.direction =
    (input.zone, served.ticket.value.source.packet.header) at key
  rw [entryEq, packetHeader] at key
  have expected : profile.entry.flow.key (sideDirection source.occurrence.actor) =
      (input.zone, profile.entry.flow.input (sideDirection source.occurrence.actor)) := by
    rw [FlowNAT.Entry.key, profile.zone_eq]
  have direction := CampusTCPRecoveryStartupKeys.direction_of_key profile.compatible (key.trans expected.symm)
  have output : processing.outcome.output = some emission := by
    obtain ⟨other, recorded, output⟩ := served.evidence.processed_of_output emission emitted
    have same := Option.some.inj (selected.symm.trans recorded)
    cases same
    exact output
  have target := processing.output_target emission output
  exact target.trans (by rw [entryEq, direction])


theorem link_header (value : N.Current base profile report current)
    (item : J.PacketItem input) (serviceIndex : Nat) (served : Served input)
    (emission : W.Emission served.ticket.value.source.packet) (emitted : served.evidence.output = some emission)
    (source : J.Source input) (production : served.ticket.value.produced = source.produced)
    (payload : item.value.payload = .link serviceIndex served emission emitted)
    (pending : item ∈ report.final.custody.pending) :
    emission.asInput.packet.header = profile.entry.flow.output (sideDirection source.occurrence.actor) :=
  emission.header.trans (link_target value item serviceIndex served emission emitted source production payload pending)

end Netlib.Check.CampusTCPRecoveryStartupLinkTarget
