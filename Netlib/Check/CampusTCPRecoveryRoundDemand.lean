import Netlib.Check.CampusTCPRecoveryRoundEvidence
import Netlib.Check.CampusTCPRecoveryRoundMonitorFacts

/-!
# Current demands from actual recovery phase evidence

Packet demands read the selected live identity and stored operation references.
Timer demands use the sender's current runtime and stored deadline.
-/

namespace Netlib.Check.CampusTCPRecoveryRoundEvidence

open Protocol.TCP CampusTCPModel CampusTCPEnabled CampusTCPRoundStart
open CampusTCPRound (Cut)
namespace M
export CampusTCPRecoveryRoundMonitor (Monitor Demand nextDemand packetAt clientRecovery)
end M
namespace R
export CampusTCPRoundMonitor (nextAction ingressAction ticketAction linkAction Action)
end R
namespace F
export CampusTCPRecoveryRoundMonitorFacts (nextDemand_action nextDemand_operation)
end F

variable {input : Input} {events : List Event} {report : Report input events}
  {complete : H.Completed input.active input.passive} {request : Request input}
  {initial : Initial report complete request} {native : NativeEnv initial} {quantum : Nat}
  {current : Cut input complete} {monitor : M.Monitor} {sentAt retries : Nat} {released : Bool}

def packetDemand (monitor : M.Monitor) (action : R.Action) (packet : Nat) : M.Demand :=
  if monitor.drops.length < 2 then .resolution action packet else .operation action

theorem packetDemand_serves (monitor : M.Monitor) (action : R.Action) (packet : Nat) (event : Event) :
    CampusTCPRecoveryRoundMonitor.serves (packetDemand monitor action packet) event = true ↔
      event = action.event ∨ monitor.drops.length < 2 ∧ event = .dropPacket packet := by
  by_cases credit : monitor.drops.length < 2
  · simp only [packetDemand, credit, ite_true, CampusTCPRecoveryRoundMonitorFacts.serves_resolution, true_and]
  · simp only [packetDemand, credit, ite_false, CampusTCPRecoveryRoundMonitorFacts.serves_operation,
      false_and, or_false]

private theorem ticket_action (state : State input) (ticket : Work.Item (Ticket input.active input.passive))
    (member : ticket ∈ state.work.pending) : R.ticketAction state (some ticket.id) = some (.serve ticket.id) := by
  unfold CampusTCPRoundMonitor.ticketAction
  simp only [bind, Option.bind]
  cases found : state.work.pending.find? (fun item => item.id == ticket.id) with
  | none =>
    have absent := List.find?_eq_none.mp found ticket member
    exact False.elim (absent (beq_self_eq_true _))
  | some item => rfl

theorem NeedSend.next_action (record : NeedSend initial current monitor) (native : NativeEnv initial) (quantum : Nat) :
    R.nextAction (CampusTCPRecoveryRoundPhaseBase.config initial native quantum).toConfig current.report.final monitor.round =
      some (.send .client request.bytes.length true) := by
  rw [record.monitorEq]
  rfl

theorem NeedSend.demand (record : NeedSend initial current monitor) (native : NativeEnv initial) (quantum : Nat) :
    M.nextDemand (CampusTCPRecoveryRoundPhaseBase.config initial native quantum) current.report.final monitor =
      some (.operation (.send .client request.bytes.length true)) := by
  rw [record.monitorEq]
  rfl

theorem DataIngress.next_action (record : DataIngress initial current monitor sentAt retries released)
    (native : NativeEnv initial) (quantum : Nat) :
    R.nextAction (CampusTCPRecoveryRoundPhaseBase.config initial native quantum).toConfig current.report.final monitor.round =
      some (.assign record.output.index native.dataIngress) := by
  simp only [R.nextAction, record.phaseEq, R.ingressAction, record.outputRef, record.packetRef,
    record.output.stored, record.custody, bind, Option.bind, beq_self_eq_true, ite_true, pure]
  rfl

theorem DataIngress.demand (record : DataIngress initial current monitor sentAt retries released)
    (native : NativeEnv initial) (quantum : Nat) :
    M.nextDemand (CampusTCPRecoveryRoundPhaseBase.config initial native quantum) current.report.final monitor =
      some (packetDemand monitor (.assign record.output.index native.dataIngress) record.packetID) := by
  simpa only [M.packetAt, record.phaseEq, record.packetRef, packetDemand] using
    F.nextDemand_action _ _ _ record.waiting _ (record.next_action native quantum)

theorem DataTicket.next_action (record : DataTicket initial native current monitor sentAt retries released) (quantum : Nat) :
    R.nextAction (CampusTCPRecoveryRoundPhaseBase.config initial native quantum).toConfig current.report.final monitor.round =
      some (.serve record.ticket.id) := by
  simp only [R.nextAction, record.phaseEq, record.ticketRef]
  exact ticket_action _ _ record.pending

theorem DataTicket.demand (record : DataTicket initial native current monitor sentAt retries released) (quantum : Nat) :
    M.nextDemand (CampusTCPRecoveryRoundPhaseBase.config initial native quantum) current.report.final monitor =
      some (.operation (.serve record.ticket.id)) :=
  F.nextDemand_operation _ _ _ record.waiting _ (record.next_action quantum) (by rw [M.packetAt, record.phaseEq])

theorem DataLink.next_action (record : DataLink initial current monitor sentAt retries released)
    (native : NativeEnv initial) (quantum : Nat) :
    R.nextAction (CampusTCPRecoveryRoundPhaseBase.config initial native quantum).toConfig current.report.final monitor.round =
      some (.deliver record.index record.emission.bytes true) := by
  simp only [R.nextAction, record.phaseEq, R.linkAction, record.serviceRef, record.packetRef,
    record.stored, record.emitted, record.custody, bind, Option.bind, beq_self_eq_true, ite_true, pure]

theorem DataLink.demand (record : DataLink initial current monitor sentAt retries released)
    (native : NativeEnv initial) (quantum : Nat) :
    M.nextDemand (CampusTCPRecoveryRoundPhaseBase.config initial native quantum) current.report.final monitor =
      some (packetDemand monitor (.deliver record.index record.emission.bytes true) record.packetID) := by
  simpa only [M.packetAt, record.phaseEq, record.packetRef, packetDemand] using
    F.nextDemand_action _ _ _ record.waiting _ (record.next_action native quantum)

theorem NeedAck.next_action (record : NeedAck initial current monitor sentAt retries)
    (native : NativeEnv initial) (quantum : Nat) :
    R.nextAction (CampusTCPRecoveryRoundPhaseBase.config initial native quantum).toConfig current.report.final monitor.round =
      some (.emitAck .server true) := by rw [R.nextAction, record.phaseEq]

theorem NeedAck.demand (record : NeedAck initial current monitor sentAt retries)
    (native : NativeEnv initial) (quantum : Nat) :
    M.nextDemand (CampusTCPRecoveryRoundPhaseBase.config initial native quantum) current.report.final monitor =
      some (.operation (.emitAck .server true)) :=
  F.nextDemand_operation _ _ _ record.waiting _ (record.next_action native quantum) (by rw [M.packetAt, record.phaseEq])

theorem AckIngress.next_action (record : AckIngress initial current monitor sentAt retries)
    (native : NativeEnv initial) (quantum : Nat) :
    R.nextAction (CampusTCPRecoveryRoundPhaseBase.config initial native quantum).toConfig current.report.final monitor.round =
      some (.assign record.output.index native.ackIngress) := by
  simp only [R.nextAction, record.phaseEq, R.ingressAction, record.outputRef, record.packetRef,
    record.output.stored, record.custody, bind, Option.bind, beq_self_eq_true, ite_true, pure]
  rfl

theorem AckIngress.demand (record : AckIngress initial current monitor sentAt retries)
    (native : NativeEnv initial) (quantum : Nat) :
    M.nextDemand (CampusTCPRecoveryRoundPhaseBase.config initial native quantum) current.report.final monitor =
      some (packetDemand monitor (.assign record.output.index native.ackIngress) record.packetID) := by
  simpa only [M.packetAt, record.phaseEq, record.packetRef, packetDemand] using
    F.nextDemand_action _ _ _ record.waiting _ (record.next_action native quantum)

theorem AckTicket.next_action (record : AckTicket initial native current monitor sentAt retries) (quantum : Nat) :
    R.nextAction (CampusTCPRecoveryRoundPhaseBase.config initial native quantum).toConfig current.report.final monitor.round =
      some (.serve record.ticket.id) := by
  simp only [R.nextAction, record.phaseEq, record.ticketRef]
  exact ticket_action _ _ record.pending

theorem AckTicket.demand (record : AckTicket initial native current monitor sentAt retries) (quantum : Nat) :
    M.nextDemand (CampusTCPRecoveryRoundPhaseBase.config initial native quantum) current.report.final monitor =
      some (.operation (.serve record.ticket.id)) :=
  F.nextDemand_operation _ _ _ record.waiting _ (record.next_action quantum) (by rw [M.packetAt, record.phaseEq])

theorem AckLink.next_action (record : AckLink initial current monitor sentAt retries)
    (native : NativeEnv initial) (quantum : Nat) :
    R.nextAction (CampusTCPRecoveryRoundPhaseBase.config initial native quantum).toConfig current.report.final monitor.round =
      some (.deliver record.index record.emission.bytes true) := by
  simp only [R.nextAction, record.phaseEq, R.linkAction, record.serviceRef, record.packetRef,
    record.stored, record.emitted, record.custody, bind, Option.bind, beq_self_eq_true, ite_true, pure]

theorem AckLink.demand (record : AckLink initial current monitor sentAt retries)
    (native : NativeEnv initial) (quantum : Nat) :
    M.nextDemand (CampusTCPRecoveryRoundPhaseBase.config initial native quantum) current.report.final monitor =
      some (packetDemand monitor (.deliver record.index record.emission.bytes true) record.packetID) := by
  simpa only [M.packetAt, record.phaseEq, record.packetRef, packetDemand] using
    F.nextDemand_action _ _ _ record.waiting _ (record.next_action native quantum)

theorem Waiting.recovery (record : Waiting initial current monitor sentAt retries released) :
    M.clientRecovery current.report.final = some record.live.sender.recovery := by
  simp only [M.clientRecovery, current.connection, record.live.sender.runtime]

theorem Waiting.demand (record : Waiting initial current monitor sentAt retries released)
    (native : NativeEnv initial) (quantum : Nat) :
    M.nextDemand (CampusTCPRecoveryRoundPhaseBase.config initial native quantum) current.report.final monitor =
      some (if record.live.sender.recovery.now < record.live.sender.entry.lastAt + record.live.sender.recovery.rto then
        .tick (min (record.live.sender.recovery.now + quantum)
          (record.live.sender.entry.lastAt + record.live.sender.recovery.rto)) else .timeout) := by
  simp only [M.nextDemand, record.waiting, ite_true, record.recovery, record.live.sender.deadline,
    bind, Option.bind]
  split <;> rfl

theorem Waiting.tick_demand (record : Waiting initial current monitor sentAt retries released)
    (native : NativeEnv initial) (quantum : Nat)
    (early : record.live.sender.recovery.now < record.live.sender.entry.lastAt + record.live.sender.recovery.rto) :
    M.nextDemand (CampusTCPRecoveryRoundPhaseBase.config initial native quantum) current.report.final monitor =
      some (.tick (min (record.live.sender.recovery.now + quantum)
        (record.live.sender.entry.lastAt + record.live.sender.recovery.rto))) := by
  rw [record.demand native quantum]
  simp only [early, ite_true]

theorem Waiting.timeout_demand (record : Waiting initial current monitor sentAt retries released)
    (native : NativeEnv initial) (quantum : Nat)
    (due : record.live.sender.entry.lastAt + record.live.sender.recovery.rto ≤ record.live.sender.recovery.now) :
    M.nextDemand (CampusTCPRecoveryRoundPhaseBase.config initial native quantum) current.report.final monitor = some .timeout := by
  rw [record.demand native quantum]
  simp only [Nat.not_lt.mpr due, ite_false]

theorem NeedRead.next_action (record : NeedRead initial current monitor retries)
    (native : NativeEnv initial) (quantum : Nat) :
    R.nextAction (CampusTCPRecoveryRoundPhaseBase.config initial native quantum).toConfig current.report.final monitor.round =
      some (.read .server request.bytes.length) := by rw [R.nextAction, record.phaseEq]; rfl

theorem NeedRead.demand (record : NeedRead initial current monitor retries)
    (native : NativeEnv initial) (quantum : Nat) :
    M.nextDemand (CampusTCPRecoveryRoundPhaseBase.config initial native quantum) current.report.final monitor =
      some (.operation (.read .server request.bytes.length)) :=
  F.nextDemand_operation _ _ _ record.waiting _ (record.next_action native quantum) (by rw [M.packetAt, record.phaseEq])

theorem Done.demand (record : Done initial current monitor retries) (native : NativeEnv initial) (quantum : Nat) :
    M.nextDemand (CampusTCPRecoveryRoundPhaseBase.config initial native quantum) current.report.final monitor = none := by
  simp only [M.nextDemand, record.waiting, Bool.false_eq_true, ite_false, R.nextAction, record.phaseEq, bind, Option.bind]

theorem Done.rank_zero (record : Done initial current monitor retries) (native : NativeEnv initial) (quantum : Nat) :
    monitor.rank (CampusTCPRecoveryRoundPhaseBase.config initial native quantum) current.report.final = 0 := by
  simp only [CampusTCPRecoveryRoundMonitor.Monitor.rank, record.waiting, Bool.false_eq_true, ite_false,
    record.phaseEq]

theorem Evidence.pending_positive (evidence : Evidence initial native quantum current monitor)
    (positive : 0 < monitor.rank (CampusTCPRecoveryRoundPhaseBase.config initial native quantum) current.report.final) :
    ∃ demand, M.nextDemand (CampusTCPRecoveryRoundPhaseBase.config initial native quantum) current.report.final monitor = some demand := by
  cases evidence with
  | needSend record => exact ⟨_, record.demand native quantum⟩
  | dataIngress record => exact ⟨_, record.demand native quantum⟩
  | dataTicket record => exact ⟨_, record.demand quantum⟩
  | dataLink record => exact ⟨_, record.demand native quantum⟩
  | needAck record => exact ⟨_, record.demand native quantum⟩
  | ackIngress record => exact ⟨_, record.demand native quantum⟩
  | ackTicket record => exact ⟨_, record.demand quantum⟩
  | ackLink record => exact ⟨_, record.demand native quantum⟩
  | waiting record => exact ⟨_, record.demand native quantum⟩
  | needRead record => exact ⟨_, record.demand native quantum⟩
  | done record => rw [record.rank_zero native quantum] at positive; omega

theorem Evidence.done_of_rank_zero (evidence : Evidence initial native quantum current monitor)
    (zero : monitor.rank (CampusTCPRecoveryRoundPhaseBase.config initial native quantum) current.report.final = 0) :
    ∃ retries, Nonempty (Done initial current monitor retries) := by
  cases evidence with
  | needSend record =>
    rw [record.monitorEq, CampusTCPRecoveryRoundMonitor.initial_rank] at zero
    omega
  | dataIngress record =>
    simp only [CampusTCPRecoveryRoundMonitor.Monitor.rank, record.waiting, Bool.false_eq_true, ite_false,
      record.phaseEq, CampusTCPRoundMonitor.Monitor.rank, CampusTCPRoundMonitor.Phase.rank] at zero
    omega
  | dataTicket record =>
    simp only [CampusTCPRecoveryRoundMonitor.Monitor.rank, record.waiting, Bool.false_eq_true, ite_false,
      record.phaseEq, CampusTCPRoundMonitor.Monitor.rank, CampusTCPRoundMonitor.Phase.rank] at zero
    omega
  | dataLink record =>
    simp only [CampusTCPRecoveryRoundMonitor.Monitor.rank, record.waiting, Bool.false_eq_true, ite_false,
      record.phaseEq, CampusTCPRoundMonitor.Monitor.rank, CampusTCPRoundMonitor.Phase.rank] at zero
    omega
  | needAck record =>
    simp only [CampusTCPRecoveryRoundMonitor.Monitor.rank, record.waiting, Bool.false_eq_true, ite_false,
      record.phaseEq, CampusTCPRoundMonitor.Monitor.rank, CampusTCPRoundMonitor.Phase.rank] at zero
    omega
  | ackIngress record =>
    simp only [CampusTCPRecoveryRoundMonitor.Monitor.rank, record.waiting, Bool.false_eq_true, ite_false,
      record.phaseEq, CampusTCPRoundMonitor.Monitor.rank, CampusTCPRoundMonitor.Phase.rank] at zero
    omega
  | ackTicket record =>
    simp only [CampusTCPRecoveryRoundMonitor.Monitor.rank, record.waiting, Bool.false_eq_true, ite_false,
      record.phaseEq, CampusTCPRoundMonitor.Monitor.rank, CampusTCPRoundMonitor.Phase.rank] at zero
    omega
  | ackLink record =>
    simp only [CampusTCPRecoveryRoundMonitor.Monitor.rank, record.waiting, Bool.false_eq_true, ite_false,
      record.phaseEq, CampusTCPRoundMonitor.Monitor.rank, CampusTCPRoundMonitor.Phase.rank] at zero
    omega
  | waiting record =>
    simp only [CampusTCPRecoveryRoundMonitor.Monitor.rank, record.waiting, ite_true] at zero
    omega
  | needRead record =>
    simp only [CampusTCPRecoveryRoundMonitor.Monitor.rank, record.waiting, Bool.false_eq_true, ite_false, record.phaseEq] at zero
    omega
  | done record => exact ⟨_, ⟨record⟩⟩

end Netlib.Check.CampusTCPRecoveryRoundEvidence
