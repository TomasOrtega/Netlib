import Netlib.Check.CampusTCPStartupJobs
import Netlib.Check.CampusTCPCustodyFacts

/-!
# A fresh ingress job from the actual endpoint output

The output-list index and custody row retain the same source occurrence.
-/

namespace Netlib.Check.CampusTCPStartupOutputJob

open CampusTCPModel CampusTCPStartupJobs

variable {input : Input}

private theorem ingress_job (item : PacketItem input) (index : Nat) (source : Source input)
    (payload : item.value.payload = .ingress index source.produced) :
    packetJob item = some (.ingress item index source payload) := by
  rcases item with ⟨id, transit, parent⟩
  dsimp only at payload
  subst transit
  cases source
  rfl

theorem Step.output_job (actual : Step input) (source : Source input)
    (emitted : actual.result.output = some source.produced) :
    ∃ job ∈ inventory actual.result.state, job.outputIndex = actual.before.outputs.length ∧
      job.source = source ∧ job.stage = .ingress := by
  obtain ⟨item, pending, _, payload⟩ := CampusTCPCustodyFacts.Step.output_packet actual source.produced emitted
  let job : Job input := .ingress item actual.before.outputs.length source payload
  exact ⟨job, inventory_member.mpr (Or.inl ⟨item, pending, ingress_job item _ source payload⟩), rfl, rfl, rfl⟩

end Netlib.Check.CampusTCPStartupOutputJob
