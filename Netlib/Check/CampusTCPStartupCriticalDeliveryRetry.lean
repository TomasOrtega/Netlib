import Netlib.Check.CampusTCPStartupCriticalDeliveryRank
import Netlib.Check.CampusTCPStartupCriticalQueueFrame

/-!
# A selected repeated SYNACK yields the final ACK path

Delivery removes its old path before the actual response receives a fresh index.
-/

namespace Netlib.Check.CampusTCPStartupCriticalDeliveryRetry

open Protocol.TCP CampusTCPModel CampusTCPStartupJobs

namespace D
export CampusTCPRecoveryStartupLinkDelivery (Delivered)
end D
namespace P
export CampusTCPStartupSelection (phaseRank retain path choose)
end P
namespace M
export CampusTCPStartupMonitor (Monitor advanceProtection expired)
end M
namespace R
export CampusTCPStartupCriticalRank (rank)
end R
namespace Q
export CampusTCPStartupCriticalQueueRank (rank_retained)
end Q
namespace C
export CampusTCPStartupCriticalDelivery.Delivered (phase rank_after_synAck)
end C

variable {input : Input} {events : List Event} {report : Report input events}
variable {current : TCPHandshakeRecovery.State input.active input.passive} {actual : Step input}
variable {source : Source input} {served : Served input} {emission : W.Emission served.ticket.value.source.packet}
variable {emitted : served.evidence.output = some emission} {item : PacketItem input}
variable {production : served.ticket.value.produced = source.produced}
variable {payload : item.value.payload = .link index served emission emitted}
variable {config : CampusTCPStartupTransferMonitor.Config} {monitor : M.Monitor}

private theorem expired_path (state : State input) (index : Nat) (event : Event) :
    M.expired quantum state (some (.path index)) event = false := by
  cases event <;> rfl

theorem synAck_acknowledged_strict (delivery : D.Delivered report current source index served emission actual)
    (connected : report.final.connection = .recovering current)
    (nocopy : ∀ step ∈ report.steps, ∀ id, step.event ≠ .copyPacket id)
    (pending : item ∈ report.final.custody.pending)
    (phase : current.phase = .acknowledged acknowledged client) (kind : source.occurrence.kind = .synAck)
    (retained : P.retain actual.before monitor.protection = some (.path served.ticket.value.outputIndex))
    (selected : P.path actual.before served.ticket.value.outputIndex =
      some (.link item index served emission emitted source production payload)) :
    R.rank config.transfer.quantum actual.result.state (M.advanceProtection config monitor actual) <
      R.rank config.transfer.quantum actual.before monitor.protection := by
  have beforePhase : P.phaseRank actual.before = 3 := by
    simp only [delivery.delivery.before, P.phaseRank, connected, phase]
  have afterPhase : P.phaseRank actual.result.state = 3 := by rw [C.phase delivery, phase, kind]; rfl
  have beforeRank : R.rank config.transfer.quantum actual.before monitor.protection = 4 := by
    rw [Q.rank_retained retained selected (by omega), beforePhase]
    simp only [CampusTCPStartupCriticalRank.pathCost, CampusTCPStartupCriticalRank.futureCost,
      Job.kind, Job.source, kind]
    rfl
  have absent := CampusTCPStartupCriticalQueueFrame.deliver_path_none actual report delivery.delivery.before
    nocopy item index served emission emitted payload pending delivery.delivery.event
  have protection : M.advanceProtection config monitor actual = P.choose actual.result.state := by
    unfold M.advanceProtection
    rw [retained]
    simp only [beforePhase, afterPhase, Nat.lt_irrefl, ite_false, expired_path, Bool.false_eq_true]
    simp only [P.retain, absent]
  have level : TCPHandshakeRecovery.phaseLevel current.phase ≤ 3 := by
    rw [phase]
    exact Nat.le_refl 3
  have bound := C.rank_after_synAck delivery nocopy level kind (quantum := config.transfer.quantum)
  rw [protection]
  omega

end Netlib.Check.CampusTCPStartupCriticalDeliveryRetry
