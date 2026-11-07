import Netlib.Check.CampusTCPStartupJobUnique
import Netlib.Check.CampusTCPStartupCriticalRank
import Netlib.Check.CampusTCPRoundService
import Netlib.Check.CampusTCPRoundAssignment

/-!
# Actual assignment and service of a protected startup path

The same physical output index moves to its next queue stage.
Service needs its actual stored emission to retain a link path.
-/

namespace Netlib.Check.CampusTCPStartupCriticalQueue

open CampusTCPModel CampusTCPStartupJobs

namespace U
export CampusTCPStartupJobUnique (Linear)
end U
namespace P
export CampusTCPStartupSelection (phaseRank path)
end P
namespace R
export CampusTCPStartupCriticalRank (stageCost pathCost)
end R

variable {input : Input}

structure StageStep (old : Job input) (actual : Step input) where
  next : Job input
  beforePath : P.path actual.before old.outputIndex = some old
  nextPath : P.path actual.result.state old.outputIndex = some next
  member : next ∈ inventory actual.result.state
  outputIndex : next.outputIndex = old.outputIndex
  source : next.source = old.source
  phase : P.phaseRank actual.result.state = P.phaseRank actual.before
  stage : R.stageCost next.stage + 1 = R.stageCost old.stage
  cost : R.pathCost (P.phaseRank actual.result.state) next + 1 = R.pathCost (P.phaseRank actual.before) old

private theorem ingress_job (item : PacketItem input) (index : Nat) (source : Source input)
    (payload : item.value.payload = .ingress index source.produced) :
    packetJob item = some (.ingress item index source payload) := by
  rcases item with ⟨id, transit, parent⟩
  dsimp only at payload
  subst transit
  cases source
  rfl

private theorem ticket_job (item : TicketItem input) (source : Source input)
    (production : item.value.produced = source.produced) : ticketJob item = some (.ticket item source production) := by
  rcases item with ⟨id, outputIndex, produced, ingress, gateway, epoch⟩
  dsimp only at production
  subst produced
  cases source
  rfl

private theorem link_job (item : PacketItem input) (index : Nat) (served : Served input)
    (emission : W.Emission served.ticket.value.source.packet) (emitted : served.evidence.output = some emission)
    (source : Source input) (production : served.ticket.value.produced = source.produced)
    (payload : item.value.payload = .link index served emission emitted) :
    packetJob item = some (.link item index served emission emitted source production payload) := by
  rcases item with ⟨id, transit, parent⟩
  dsimp only at payload
  subst transit
  rcases served with ⟨time, ⟨ticketID, ⟨outputIndex, produced, ingress, gateway, epoch⟩⟩,
    before, mode, evidence, computed, observed⟩
  dsimp only at production
  subst produced
  cases source
  rfl

theorem assignment (actual : Step input) (report : Report input events)
    (before : actual.before = report.final)
    (nocopy : ∀ actual ∈ report.steps, ∀ id, actual.event ≠ .copyPacket id)
    (item : PacketItem input) (index : Nat) (source : Source input)
    (payload : item.value.payload = .ingress index source.produced)
    (pending : item ∈ report.final.custody.pending)
    (event : actual.event = .assign index ingress) :
    Nonempty (StageStep (.ingress item index source payload) actual) := by
  let old : Job input := .ingress item index source payload
  have oldMember : old ∈ inventory report.final := inventory_member.mpr (Or.inl ⟨item, pending, ingress_job item index source payload⟩)
  have prior : U.Linear actual.before := by rw [before]; exact CampusTCPStartupJobUnique.Report.linear report nocopy
  have history : Theory.PacketCustody.History actual.before.custody := by
    rw [before]
    exact CampusTCPCustodyFacts.Report.history report
  have after := prior.step history (fun id impossible => by rw [event] at impossible; cases impossible)
  have lookup : actual.before.outputs[index]? = some source.produced := by
    have selected := CampusTCPCustodyFacts.Report.sources report item (List.mem_append_right _ pending)
    rw [payload] at selected
    simpa only [before, CampusTCPCustodyFacts.Sourced] using selected
  obtain ⟨custody, prepared, frame⟩ := CampusTCPRoundAssignment.Step.assign_frame actual index ingress event source.produced lookup
  let ticket := CampusTCPRoundAssignment.ticket actual.before index ingress source.produced
  let next : Job input := .ticket ticket source rfl
  have ticketPending : ticket ∈ actual.result.state.work.pending := by
    rw [frame]
    exact List.mem_append_right _ (by simp only [ticket, CampusTCPRoundAssignment.ticket, List.mem_singleton])
  have member : next ∈ inventory actual.result.state := inventory_member.mpr (Or.inr ⟨ticket, ticketPending, ticket_job ticket source rfl⟩)
  have phase : P.phaseRank actual.result.state = P.phaseRank actual.before := by simp only [P.phaseRank, frame]
  refine ⟨⟨next, ?_, ?_, member, rfl, rfl, phase, rfl, ?_⟩⟩
  · rw [before]
    exact (CampusTCPStartupJobUnique.Report.linear report nocopy).path_eq old oldMember
  · exact after.path_eq next member
  · simp only [R.pathCost, next, Job.stage, R.stageCost, Job.kind, Job.source, phase]
    omega

theorem service (actual : Step input) (report : Report input events)
    (before : actual.before = report.final)
    (nocopy : ∀ actual ∈ report.steps, ∀ id, actual.event ≠ .copyPacket id)
    (item : TicketItem input) (source : Source input) (production : item.value.produced = source.produced)
    (pending : item ∈ report.final.work.pending)
    (event : actual.event = .serve item.id observed)
    (served : Served input) (recorded : actual.result.service = some served)
    (emission : W.Emission served.ticket.value.source.packet) (emitted : served.evidence.output = some emission) :
    Nonempty (StageStep (.ticket item source production) actual) := by
  let old : Job input := .ticket item source production
  have found : ticketJob item = some old := ticket_job item source production
  have oldMember : old ∈ inventory report.final := inventory_member.mpr (Or.inr ⟨item, pending, found⟩)
  have prior : U.Linear actual.before := by rw [before]; exact CampusTCPStartupJobUnique.Report.linear report nocopy
  have history : Theory.PacketCustody.History actual.before.custody := by
    rw [before]
    exact CampusTCPCustodyFacts.Report.history report
  have after := prior.step history (fun id impossible => by rw [event] at impossible; cases impossible)
  obtain ⟨completed, computed, ticket, _, work, _, connection, _, _⟩ :=
    CampusTCPRoundService.Step.serve_frame actual item.id observed event served recorded
  have sameItem : completed.item = item := completed.item_eq
    (by rw [before]; exact CampusTCPOrigins.Report.work_valid report) item (by rw [before]; exact pending) rfl
  have ticketEq : served.ticket = item := ticket.trans sameItem
  have produced : served.ticket.value.produced = source.produced := by rw [ticketEq]; exact production
  obtain ⟨packet, packetPending, parent, payload⟩ := CampusTCPCustodyFacts.Step.emission_packet actual served recorded emission emitted
  let next : Job input := .link packet actual.before.services.length served emission emitted source produced payload.1
  have packetFound : packetJob packet = some next := link_job packet actual.before.services.length served emission emitted source produced payload.1
  have member : next ∈ inventory actual.result.state := inventory_member.mpr (Or.inl ⟨packet, packetPending, packetFound⟩)
  have outputIndex : next.outputIndex = old.outputIndex := by
    change served.ticket.value.outputIndex = item.value.outputIndex
    rw [ticketEq]
  have phase : P.phaseRank actual.result.state = P.phaseRank actual.before := by
    simp only [P.phaseRank, connection]
  refine ⟨⟨next, ?_, ?_, member, outputIndex, rfl, phase, rfl, ?_⟩⟩
  · rw [before]
    exact (CampusTCPStartupJobUnique.Report.linear report nocopy).path_eq old oldMember
  · rw [← outputIndex]
    exact after.path_eq next member
  · simp only [R.pathCost, next, Job.stage, R.stageCost, Job.kind, Job.source, phase]
    omega

end Netlib.Check.CampusTCPStartupCriticalQueue
