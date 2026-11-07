import Netlib.Check.CampusTCPStartupCriticalDelivery
import Netlib.Check.CampusTCPStartupCriticalQueueRank

/-!
# Rank descent at actual advancing startup deliveries

The phase advance releases the old path and selects the actual response.
-/

namespace Netlib.Check.CampusTCPStartupCriticalDeliveryRank

open Protocol.TCP CampusTCPModel CampusTCPStartupJobs

namespace D
export CampusTCPRecoveryStartupLinkDelivery (Delivered)
end D
namespace P
export CampusTCPStartupSelection (phaseRank retain path choose)
end P
namespace M
export CampusTCPStartupMonitor (Monitor advanceProtection)
end M
namespace R
export CampusTCPStartupCriticalRank (rank)
end R
namespace Q
export CampusTCPStartupCriticalQueueRank (rank_retained)
end Q
namespace C
export CampusTCPStartupCriticalDelivery.Delivered (phase rank_after_syn rank_after_synAck rank_after_finalAck)
end C

variable {input : Input} {events : List Event} {report : Report input events}
variable {current : TCPHandshakeRecovery.State input.active input.passive} {actual : Step input}
variable {source : Source input} {served : Served input} {emission : W.Emission served.ticket.value.source.packet}
variable {emitted : served.evidence.output = some emission} {item : PacketItem input}
variable {production : served.ticket.value.produced = source.produced}
variable {payload : item.value.payload = .link index served emission emitted}
variable {config : CampusTCPStartupTransferMonitor.Config} {monitor : M.Monitor}

private theorem protection (advance : P.phaseRank actual.before < P.phaseRank actual.result.state) :
    M.advanceProtection config monitor actual = P.choose actual.result.state := by
  simp only [M.advanceProtection, advance, ite_true]

theorem syn_strict (delivery : D.Delivered report current source index served emission actual)
    (connected : report.final.connection = .recovering current)
    (nocopy : ∀ step ∈ report.steps, ∀ id, step.event ≠ .copyPacket id)
    (phase : current.phase = .opened opened) (kind : source.occurrence.kind = .syn)
    (retained : P.retain actual.before monitor.protection = some (.path served.ticket.value.outputIndex))
    (selected : P.path actual.before served.ticket.value.outputIndex =
      some (.link item index served emission emitted source production payload)) :
    R.rank config.transfer.quantum actual.result.state (M.advanceProtection config monitor actual) <
      R.rank config.transfer.quantum actual.before monitor.protection := by
  have beforePhase : P.phaseRank actual.before = 1 := by
    simp only [delivery.delivery.before, P.phaseRank, connected, phase]
  have afterPhase : P.phaseRank actual.result.state = 2 := by rw [C.phase delivery, phase, kind]; rfl
  have beforeRank : R.rank config.transfer.quantum actual.before monitor.protection = 7 := by
    rw [Q.rank_retained retained selected (by omega), beforePhase]
    rfl
  have bound := C.rank_after_syn delivery nocopy phase kind (quantum := config.transfer.quantum)
  rw [protection (by omega)]
  omega

theorem synAck_answered_strict (delivery : D.Delivered report current source index served emission actual)
    (connected : report.final.connection = .recovering current)
    (nocopy : ∀ step ∈ report.steps, ∀ id, step.event ≠ .copyPacket id)
    (phase : current.phase = .answered answered) (kind : source.occurrence.kind = .synAck)
    (retained : P.retain actual.before monitor.protection = some (.path served.ticket.value.outputIndex))
    (selected : P.path actual.before served.ticket.value.outputIndex =
      some (.link item index served emission emitted source production payload)) :
    R.rank config.transfer.quantum actual.result.state (M.advanceProtection config monitor actual) <
      R.rank config.transfer.quantum actual.before monitor.protection := by
  have beforePhase : P.phaseRank actual.before = 2 := by
    simp only [delivery.delivery.before, P.phaseRank, connected, phase]
  have level : TCPHandshakeRecovery.phaseLevel current.phase ≤ 3 := by
    rw [phase]
    exact (by decide : (2 : Nat) ≤ 3)
  have afterPhase : P.phaseRank actual.result.state = 3 := by rw [C.phase delivery, phase, kind]; rfl
  have beforeRank : R.rank config.transfer.quantum actual.before monitor.protection = 4 := by
    rw [Q.rank_retained retained selected (by omega), beforePhase]
    rfl
  have bound := C.rank_after_synAck delivery nocopy level kind (quantum := config.transfer.quantum)
  rw [protection (by omega)]
  omega

theorem finalAck_strict (delivery : D.Delivered report current source index served emission actual)
    (connected : report.final.connection = .recovering current)
    (phase : current.phase = .acknowledged acknowledged client) (kind : source.occurrence.kind = .finalAck)
    (retained : P.retain actual.before monitor.protection = some (.path served.ticket.value.outputIndex))
    (selected : P.path actual.before served.ticket.value.outputIndex =
      some (.link item index served emission emitted source production payload)) :
    R.rank config.transfer.quantum actual.result.state (M.advanceProtection config monitor actual) <
      R.rank config.transfer.quantum actual.before monitor.protection := by
  have beforePhase : P.phaseRank actual.before = 3 := by
    simp only [delivery.delivery.before, P.phaseRank, connected, phase]
  have beforeRank : R.rank config.transfer.quantum actual.before monitor.protection = 1 := by
    rw [Q.rank_retained retained selected (by omega), beforePhase]
    simp only [CampusTCPStartupCriticalRank.pathCost, CampusTCPStartupCriticalRank.futureCost,
      Job.kind, Job.source, kind]
    rfl
  rw [C.rank_after_finalAck delivery kind, beforeRank]
  decide

end Netlib.Check.CampusTCPStartupCriticalDeliveryRank
