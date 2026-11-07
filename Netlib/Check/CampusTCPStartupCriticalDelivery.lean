import Netlib.Check.CampusTCPRecoveryStartupLinkDelivery
import Netlib.Check.CampusTCPStartupCriticalChoice
import Netlib.Check.CampusTCPStartupOutputJob

/-!
# Actual startup responses supply the next bounded path

The response job comes from the same recorded control step and custody mint.
-/

namespace Netlib.Check.CampusTCPStartupCriticalDelivery

open Protocol.TCP CampusTCPModel CampusTCPStartupJobs

namespace D
export CampusTCPRecoveryStartupLinkDelivery (Delivered)
end D
namespace P
export CampusTCPStartupSelection (phaseRank choose)
end P
namespace R
export CampusTCPStartupCriticalRank (rank)
end R
namespace U
export CampusTCPStartupJobUnique (Linear)
end U

variable {input : Input} {events : List Event} {report : Report input events}
variable {current : C.State input.active input.passive} {actual : Step input}
variable {source : Source input} {served : Served input} {emission : W.Emission served.ticket.value.source.packet}

private theorem recovery_phase (connected : state.connection = .recovering current) :
    P.phaseRank state = TCPHandshakeRecovery.phaseLevel current.phase := by
  cases phase : current.phase <;> simp only [P.phaseRank, connected, phase, TCPHandshakeRecovery.phaseLevel]

theorem Delivered.phase (delivery : D.Delivered report current source index served emission actual) :
    P.phaseRank actual.result.state =
      TCPHandshakeRecovery.receiveLevel (TCPHandshakeRecovery.phaseLevel current.phase) source.occurrence.kind := by
  rw [recovery_phase delivery.delivery.connection, delivery.delivery.phase, delivery.sourceEq]

theorem Delivered.linear (delivery : D.Delivered report current source index served emission actual)
    (nocopy : ∀ step ∈ report.steps, ∀ id, step.event ≠ .copyPacket id) : U.Linear actual.result.state := by
  have before : U.Linear actual.before := by
    rw [delivery.delivery.before]
    exact CampusTCPStartupJobUnique.Report.linear report nocopy
  have history : Theory.PacketCustody.History actual.before.custody := by
    rw [delivery.delivery.before]
    exact CampusTCPCustodyFacts.Report.history report
  exact before.step history (by intro id; rw [delivery.delivery.event]; intro same; cases same)

theorem Delivered.response_job (delivery : D.Delivered report current source index served emission actual)
    (response : TCPHandshakeRecovery.receiveResponse current.phase source.occurrence.kind = some kind) :
    ∃ job ∈ inventory actual.result.state, job.actor = Actor.ofRecovery kind.actor ∧
      job.kind = kind ∧ job.stage = .ingress := by
  have responseKind := delivery.delivery.response
  rw [delivery.sourceEq, response] at responseKind
  obtain ⟨occurrence, present, actor, selectedKind⟩ := responseKind
  let next : Source input := ⟨delivery.delivery.control, occurrence, present⟩
  have emitted : actual.result.output = some next.produced := delivery.delivery.output.some present
  obtain ⟨job, member, _, original, stage⟩ := CampusTCPStartupOutputJob.Step.output_job actual next emitted
  refine ⟨job, member, ?_, ?_, stage⟩
  · simp only [Job.actor, original, next, actor]
  · simp only [Job.kind, original, next, selectedKind]

theorem Delivered.rank_after_syn (delivery : D.Delivered report current source index served emission actual)
    (nocopy : ∀ step ∈ report.steps, ∀ id, step.event ≠ .copyPacket id)
    (phase : current.phase = .opened opened) (kind : source.occurrence.kind = .syn) :
    R.rank quantum actual.result.state (P.choose actual.result.state) ≤ 6 := by
  have response : TCPHandshakeRecovery.receiveResponse current.phase source.occurrence.kind = some .synAck := by
    rw [phase, kind]
    rfl
  obtain ⟨job, member, actor, selectedKind, _⟩ := Delivered.response_job delivery response
  have after : P.phaseRank actual.result.state = 2 := by
    rw [Delivered.phase delivery, phase, kind]
    rfl
  exact CampusTCPStartupCriticalChoice.rank_choose_answered (Delivered.linear delivery nocopy) after member actor selectedKind

theorem Delivered.rank_after_synAck (delivery : D.Delivered report current source index served emission actual)
    (nocopy : ∀ step ∈ report.steps, ∀ id, step.event ≠ .copyPacket id)
    (level : TCPHandshakeRecovery.phaseLevel current.phase ≤ 3) (kind : source.occurrence.kind = .synAck) :
    R.rank quantum actual.result.state (P.choose actual.result.state) ≤ 3 := by
  have response : TCPHandshakeRecovery.receiveResponse current.phase source.occurrence.kind = some .finalAck := by
    rw [kind]
    rfl
  obtain ⟨job, member, actor, selectedKind, _⟩ := Delivered.response_job delivery response
  have after : P.phaseRank actual.result.state = 3 := by
    rw [Delivered.phase delivery, kind, TCPHandshakeRecovery.receiveLevel, Nat.max_eq_right level]
  exact CampusTCPStartupCriticalChoice.rank_choose_finalAck (Delivered.linear delivery nocopy) after member actor selectedKind

theorem Delivered.rank_after_finalAck (delivery : D.Delivered report current source index served emission actual)
    (kind : source.occurrence.kind = .finalAck) : R.rank quantum actual.result.state held = 0 := by
  have complete : P.phaseRank actual.result.state = 4 := by rw [Delivered.phase delivery, kind]; rfl
  simp only [R.rank, complete, ite_true]

end Netlib.Check.CampusTCPStartupCriticalDelivery
