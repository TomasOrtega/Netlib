import Netlib.Check.CampusTCPStartupCriticalDelivery
import Netlib.Check.CampusTCPStartupCriticalDemand
import Netlib.Check.CampusTCPStartupMonitor

/-!
# An actual phase advance reduces every protected critical rank

The current rank covers the next response even when another path advances first.
-/

namespace Netlib.Check.CampusTCPStartupCriticalReceiveAdvance

open Protocol.TCP CampusTCPModel CampusTCPStartupJobs

namespace D
export CampusTCPRecoveryStartupLinkDelivery (Delivered)
end D
namespace P
export CampusTCPStartupSelection (phaseRank choose)
end P
namespace M
export CampusTCPStartupMonitor (Monitor advanceProtection)
end M
namespace R
export CampusTCPStartupCriticalRank (rank)
end R
namespace L
export CampusTCPStartupCriticalDemand (rank_phase_one rank_phase_two rank_positive)
end L
namespace C
export CampusTCPStartupCriticalDelivery.Delivered (phase rank_after_syn rank_after_synAck rank_after_finalAck)
end C

variable {input : Input} {events : List Event} {report : Report input events}
variable {current : TCPHandshakeRecovery.State input.active input.passive} {actual : Step input}
variable {source : Source input} {served : Served input} {emission : W.Emission served.ticket.value.source.packet}
variable {config : CampusTCPStartupTransferMonitor.Config} {monitor : M.Monitor}

private theorem phase_before (delivery : D.Delivered report current source index served emission actual)
    (connected : report.final.connection = .recovering current) :
    P.phaseRank actual.before = TCPHandshakeRecovery.phaseLevel current.phase := by
  cases phase : current.phase <;>
    simp only [P.phaseRank, delivery.delivery.before, connected, phase, TCPHandshakeRecovery.phaseLevel]

theorem nondecrease (delivery : D.Delivered report current source index served emission actual)
    (connected : report.final.connection = .recovering current) :
    P.phaseRank actual.before ≤ P.phaseRank actual.result.state := by
  have bounded : TCPHandshakeRecovery.phaseLevel current.phase ≤ 4 := by
    cases current.phase <;> simp only [TCPHandshakeRecovery.phaseLevel] <;> omega
  rw [phase_before delivery connected, C.phase delivery]
  cases source.occurrence.kind <;> simp only [TCPHandshakeRecovery.receiveLevel] <;> omega

theorem strict (delivery : D.Delivered report current source index served emission actual)
    (connected : report.final.connection = .recovering current)
    (nocopy : ∀ step ∈ report.steps, ∀ id, step.event ≠ .copyPacket id)
    (phase : P.phaseRank actual.before = 1 ∨ P.phaseRank actual.before = 2 ∨ P.phaseRank actual.before = 3)
    (advance : P.phaseRank actual.before < P.phaseRank actual.result.state) :
    R.rank config.transfer.quantum actual.result.state (M.advanceProtection config monitor actual) <
      R.rank config.transfer.quantum actual.before monitor.protection := by
  have beforeConnected : actual.before.connection = .recovering current := by rw [delivery.delivery.before]; exact connected
  have linear : CampusTCPStartupJobUnique.Linear actual.before := by
    rw [delivery.delivery.before]
    exact CampusTCPStartupJobUnique.Report.linear report nocopy
  have positive := L.rank_positive beforeConnected linear phase
    (held := monitor.protection) (quantum := config.transfer.quantum)
  have before := phase_before delivery connected
  have protection : M.advanceProtection config monitor actual = P.choose actual.result.state := by
    simp only [M.advanceProtection, advance, ite_true]
  rw [protection]
  cases kind : source.occurrence.kind with
  | finalAck =>
    rw [C.rank_after_finalAck delivery kind]
    exact positive
  | synReplyAck =>
    have same : P.phaseRank actual.result.state = P.phaseRank actual.before := by
      rw [C.phase delivery, before, kind, TCPHandshakeRecovery.receiveLevel]
    omega
  | syn =>
    cases currentPhase : current.phase with
    | idle =>
      have zero : P.phaseRank actual.before = 0 := by rw [before, currentPhase]; rfl
      rcases phase with first | second | third <;> omega
    | opened opened =>
      have one : P.phaseRank actual.before = 1 := by rw [before, currentPhase]; rfl
      have lower := L.rank_phase_one beforeConnected linear one
        (held := monitor.protection) (quantum := config.transfer.quantum)
      have upper := C.rank_after_syn delivery nocopy currentPhase kind (quantum := config.transfer.quantum)
      omega
    | answered answered =>
      have same : P.phaseRank actual.result.state = P.phaseRank actual.before := by
        rw [C.phase delivery, before, currentPhase, kind]
        rfl
      omega
    | acknowledged acknowledged client =>
      have same : P.phaseRank actual.result.state = P.phaseRank actual.before := by
        rw [C.phase delivery, before, currentPhase, kind]
        rfl
      omega
    | complete complete client server =>
      have four : P.phaseRank actual.before = 4 := by rw [before, currentPhase]; rfl
      rcases phase with first | second | third <;> omega
  | synAck =>
    cases currentPhase : current.phase with
    | idle =>
      have zero : P.phaseRank actual.before = 0 := by rw [before, currentPhase]; rfl
      rcases phase with first | second | third <;> omega
    | opened opened =>
      have one : P.phaseRank actual.before = 1 := by rw [before, currentPhase]; rfl
      have lower := L.rank_phase_one beforeConnected linear one
        (held := monitor.protection) (quantum := config.transfer.quantum)
      have level : TCPHandshakeRecovery.phaseLevel current.phase ≤ 3 := by
        rw [currentPhase]
        exact (by decide : (1 : Nat) ≤ 3)
      have upper := C.rank_after_synAck delivery nocopy level kind (quantum := config.transfer.quantum)
      omega
    | answered answered =>
      have two : P.phaseRank actual.before = 2 := by rw [before, currentPhase]; rfl
      have lower := L.rank_phase_two beforeConnected linear two
        (held := monitor.protection) (quantum := config.transfer.quantum)
      have level : TCPHandshakeRecovery.phaseLevel current.phase ≤ 3 := by
        rw [currentPhase]
        exact (by decide : (2 : Nat) ≤ 3)
      have upper := C.rank_after_synAck delivery nocopy level kind (quantum := config.transfer.quantum)
      omega
    | acknowledged acknowledged client =>
      have same : P.phaseRank actual.result.state = P.phaseRank actual.before := by
        rw [C.phase delivery, before, currentPhase, kind]
        rfl
      omega
    | complete complete client server =>
      have four : P.phaseRank actual.before = 4 := by rw [before, currentPhase]; rfl
      rcases phase with first | second | third <;> omega

end Netlib.Check.CampusTCPStartupCriticalReceiveAdvance
