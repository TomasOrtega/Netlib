import Netlib.Check.CampusTCPStartupCriticalDeliveryRetry

/-!
# Every selected live startup link reduces the critical rank

Current usefulness selects the relevant control kind for each reached phase.
-/

namespace Netlib.Check.CampusTCPStartupCriticalLinkStep

open Protocol.TCP CampusTCPModel CampusTCPStartupJobs

namespace D
export CampusTCPRecoveryStartupLinkDelivery (Delivered)
end D
namespace P
export CampusTCPStartupSelection (phaseRank retain path useful)
end P
namespace M
export CampusTCPStartupMonitor (Monitor advanceProtection)
end M
namespace R
export CampusTCPStartupCriticalRank (rank)
end R
namespace Q
export CampusTCPStartupCriticalQueueRank (retained_useful)
end Q
namespace A
export CampusTCPStartupCriticalDeliveryRank (syn_strict synAck_answered_strict finalAck_strict)
end A

variable {input : Input} {events : List Event} {report : Report input events}
variable {current : TCPHandshakeRecovery.State input.active input.passive} {actual : Step input}
variable {source : Source input} {served : Served input} {emission : W.Emission served.ticket.value.source.packet}
variable {emitted : served.evidence.output = some emission} {item : PacketItem input}
variable {production : served.ticket.value.produced = source.produced}
variable {payload : item.value.payload = .link index served emission emitted}
variable {config : CampusTCPStartupTransferMonitor.Config} {monitor : M.Monitor}

theorem strict (delivery : D.Delivered report current source index served emission actual)
    (connected : report.final.connection = .recovering current)
    (nocopy : ∀ step ∈ report.steps, ∀ id, step.event ≠ .copyPacket id)
    (pending : item ∈ report.final.custody.pending)
    (incomplete : P.phaseRank actual.before ≠ 4)
    (retained : P.retain actual.before monitor.protection = some (.path served.ticket.value.outputIndex))
    (selected : P.path actual.before served.ticket.value.outputIndex =
      some (.link item index served emission emitted source production payload)) :
    R.rank config.transfer.quantum actual.result.state (M.advanceProtection config monitor actual) <
      R.rank config.transfer.quantum actual.before monitor.protection := by
  have linear : CampusTCPStartupJobUnique.Linear actual.before := by
    rw [delivery.delivery.before]
    exact CampusTCPStartupJobUnique.Report.linear report nocopy
  have useful := Q.retained_useful linear retained selected
  cases phase : current.phase with
  | idle =>
    simp only [P.useful, P.phaseRank, delivery.delivery.before, connected, phase, Bool.false_eq_true] at useful
  | opened opened =>
    simp only [P.useful, P.phaseRank, delivery.delivery.before, connected, phase, Job.kind, Job.source] at useful
    have kind : source.occurrence.kind = .syn := (of_decide_eq_true useful).2
    exact A.syn_strict delivery connected nocopy phase kind retained selected
  | answered answered =>
    simp only [P.useful, P.phaseRank, delivery.delivery.before, connected, phase, Job.kind, Job.source] at useful
    have kind : source.occurrence.kind = .synAck := (of_decide_eq_true useful).2
    exact A.synAck_answered_strict delivery connected nocopy phase kind retained selected
  | acknowledged acknowledged client =>
    simp only [P.useful, P.phaseRank, delivery.delivery.before, connected, phase, Job.kind, Job.source] at useful
    rcases of_decide_eq_true useful with ⟨_, kind⟩ | ⟨_, kind⟩
    · exact A.finalAck_strict delivery connected phase kind retained selected
    · exact CampusTCPStartupCriticalDeliveryRetry.synAck_acknowledged_strict delivery connected nocopy pending phase kind retained selected
  | complete complete client server =>
    exact False.elim (incomplete (by simp only [P.phaseRank, delivery.delivery.before, connected, phase]))

end Netlib.Check.CampusTCPStartupCriticalLinkStep
