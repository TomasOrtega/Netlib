import Netlib.Check.CampusTCPStartupJobDrain
import Netlib.Check.CampusTCPOrigins

/-!
# An actual recovery ticket service reduces the drain potential

A recorded service consumes its real ticket. It emits at most one link packet.
An unsupported operation has no recorded service and supplies no progress here.
-/

namespace Netlib.Check.CampusTCPStartupJobDrainService

open CampusTCPModel CampusTCPStartupJobs CampusTCPStartupJobDrain

variable {input : Input}

private theorem service_rows (actual : Step input) (served : Served input)
    (recorded : actual.result.service = some served) :
    ∃ id, ∃ completed : Theory.Outstanding.Completed actual.before.work id,
      completed.item = served.ticket ∧ actual.result.state.work = completed.state ∧
        actual.result.state.custody =
          match emitted : served.evidence.output with
          | none => actual.before.custody
          | some emission => Theory.PacketCustody.mint actual.before.custody
            (.link actual.before.services.length served emission emitted) := by
  obtain ⟨id, observed, completed, event, finished, ticket, _, _⟩ := CampusTCPOrigins.service_origin actual served recorded
  obtain ⟨effect, custody, computed, prepared, final⟩ := actual.transaction
  have present : effect.service = some served := by simpa only [final] using recorded
  have unchanged : custody = actual.before.custody := by
    simpa only [prepareCustody, event, pure, Except.pure, Except.ok.injEq] using prepared.symm
  rw [event] at computed
  simp only [processCore, finished, Except.mapError, bind, Except.bind] at computed
  repeat' first
    | (solve | cases computed)
    | (solve | cases computed; cases present)
    | (solve |
      cases computed
      cases present
      refine ⟨id, completed, ticket.symm, ?_, ?_⟩
      · rw [final]
      · rw [final, unchanged]
        rfl)
    | split at computed
    | dsimp only [Except.mapError, bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at computed

private theorem link_weight (before : State input) (served : Served input)
    (emission : W.Emission served.ticket.value.source.packet) (emitted : served.evidence.output = some emission) :
    packetWeight (Theory.PacketCustody.newItem before.custody (.link before.services.length served emission emitted)) =
      sourceWeight .link served.ticket.value.produced := rfl

theorem Step.service_strict (actual : Step input) (served : Served input)
    (recorded : actual.result.service = some served) (recovery : served.ticket.value.produced.isRecovery = true) :
    potential actual.result.state < potential actual.before := by
  obtain ⟨id, completed, item, work, custody⟩ := service_rows actual served recorded
  have sum := (completed.pendingPerm.map (ticketWeight (input := input))).sum_nat
  rw [List.map_cons, List.sum_cons, item] at sum
  change (actual.before.work.pending.map ticketWeight).sum = sourceWeight .ticket served.ticket.value.produced +
    (completed.state.pending.map ticketWeight).sum at sum
  have gap : sourceWeight .ticket served.ticket.value.produced = sourceWeight .link served.ticket.value.produced + 1 := by
    cases produced : served.ticket.value.produced with
    | startup step output present | application actor step output present =>
      simp only [produced, Produced.isRecovery] at recovery
      cases recovery
    | recovery control occurrence present =>
      cases kind : occurrence.kind <;> simp only [sourceWeight, kind, stageWeight]
  rw [potential_rows, potential_rows, work, custody]
  split
  · omega
  · simp only [Theory.PacketCustody.mint_pending, List.map_append, List.sum_append,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero, link_weight]
    change _ < _
    omega

end Netlib.Check.CampusTCPStartupJobDrainService
