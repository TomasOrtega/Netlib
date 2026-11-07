import Netlib.Check.CampusTCPRevocationInstallation
import Netlib.Check.CampusTCPRevocationDenial
import Netlib.Check.CampusTCPRevocationDrainBound

/-!
# No new link output or network receipt after TCP clearance

Stored native targets deny each actual service.
Endpoint buffers and new ingress work can remain in the closed state.
-/

namespace Netlib.Check.CampusTCPRevocationClosure

open CampusTCPModel CampusTCPRevocationTargets

def Closed (targets : Targets input cut) (state : State input) : Prop :=
  targets.Installed state ∧ targets.CurrentAt state ∧ CampusTCPRevocationCustody.frontier state = []

structure Quiet (actual : Step input) : Prop where
  service : ∀ served, actual.result.service = some served → served.evidence.output = none
  receipt : actual.result.receipt = none

theorem Step.closed (actual : Step input) (targets : Targets input cut)
    (revoked : CampusTCPRevocationTargets.revoked input cut.authentication = true)
    (allowed : CampusTCPRevocationControl.allowed targets.names allowance actual.before actual.event = true)
    (history : Theory.PacketCustody.History actual.before.custody) (prior : Closed targets actual.before) :
    Closed targets actual.result.state ∧ Quiet actual := by
  have frame := CampusTCPRevocationInstallation.allowed_frame targets actual allowed
  have nocopy := CampusTCPRevocationControl.allowed_no_copy targets.names allowance actual.before actual.event allowed
  have denied : ∀ served, actual.result.service = some served → served.evidence.output = none := by
    intro served present
    exact targets.service_output_none revoked actual served present prior.1
  have installed : targets.Installed actual.result.state := by
    intro gateway
    exact ⟨CampusTCPRevocationFrames.Step.stored actual targets (.forward gateway) frame (prior.1 gateway).1,
      CampusTCPRevocationFrames.Step.stored actual targets (.ingress gateway) frame (prior.1 gateway).2⟩
  have current := CampusTCPRevocationFrames.Step.current actual targets frame prior.2.1
  have subset := CampusTCPRevocationCustody.Step.frontier_sublist actual nocopy denied
  rw [prior.2.2] at subset
  have empty := subset.eq_of_length_le (by simp)
  exact ⟨⟨installed, current, empty⟩, ⟨denied,
    CampusTCPRevocationDrainBound.Step.no_receipt_when_empty actual history prior.2.2⟩⟩

theorem Trace.closed (trace : Trace input initial events steps final remaining) (targets : Targets input cut)
    (revoked : CampusTCPRevocationTargets.revoked input cut.authentication = true)
    (actions : CampusTCPRevocationControl.actions targets.names allowance steps = true)
    (history : Theory.PacketCustody.History initial.custody) (prior : Closed targets initial) :
    Closed targets final ∧ ∀ actual ∈ steps, Quiet actual := by
  induction trace with
  | done state => exact ⟨prior, by simp⟩
  | stop head blocked tail =>
    have allowed : CampusTCPRevocationControl.allowed targets.names allowance head.before head.event = true := by
      simpa only [CampusTCPRevocationControl.actions, Bool.and_true] using actions
    have current := Step.closed head targets revoked allowed history prior
    exact ⟨current.1, fun actual member => (List.mem_singleton.mp member) ▸ current.2⟩
  | next head supported rest ih =>
    simp only [CampusTCPRevocationControl.actions, Bool.and_eq_true] at actions
    have current := Step.closed head targets revoked actions.1 history prior
    have later := ih actions.2 (CampusTCPCustodyFacts.Step.history head history) current.1
    refine ⟨later.1, ?_⟩
    intro actual member
    rcases List.mem_cons.mp member with same | member
    · exact same ▸ current.2
    · exact later.2 actual member

end Netlib.Check.CampusTCPRevocationClosure
