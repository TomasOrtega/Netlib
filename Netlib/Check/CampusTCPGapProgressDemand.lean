import Netlib.Check.CampusTCPGapProgressEvidence
import Netlib.Check.CampusTCPGapProgressMonitorFacts

/-!
# Current demands from held-gap phase evidence

Packet demands select the current stored operation and live packet identity.
Waiting demands use the sender's actual head record and deadline.
-/

namespace Netlib.Check.CampusTCPGapProgressEvidence

open Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPGapProgressStart (GapInitial NativeEnv)
open CampusTCPGapProgressSetup (config)
namespace M
export CampusTCPGapProgressMonitor (Config Monitor Demand nextDemand nextAction packetAt senderRecovery)
end M
namespace R
export CampusTCPRoundMonitor (ingressAction ticketAction linkAction Action)
end R
namespace F
export CampusTCPGapProgressMonitorFacts (nextDemand_action nextDemand_operation)
end F

variable {input : Input} {complete : H.Completed input.active input.passive}
  {cut current : Cut input complete} {sender : Actor} {lower upper : List UInt8}
  {initial : GapInitial cut sender lower upper}
  {native : NativeEnv cut initial.gateway.seed.entry} {allowance retries : Nat}
  {monitor : M.Monitor} {released : Bool}

def packetDemand (allowance : Nat) (monitor : M.Monitor) (action : R.Action) (packet : Nat) : M.Demand :=
  if monitor.drops.length < allowance then .resolution action packet else .operation action

theorem packetDemand_event (allowance : Nat) (monitor : M.Monitor) (action : R.Action) (packet : Nat) :
    (packetDemand allowance monitor action packet).event = action.event := by
  unfold packetDemand
  split <;> rfl

theorem packetDemand_serves (allowance : Nat) (monitor : M.Monitor) (action : R.Action) (packet : Nat) (event : Event) :
    CampusTCPGapProgressMonitor.serves (packetDemand allowance monitor action packet) event = true ↔
      event = action.event ∨ monitor.drops.length < allowance ∧ event = .dropPacket packet := by
  by_cases credit : monitor.drops.length < allowance
  · simp only [packetDemand, credit, ite_true, CampusTCPGapProgressMonitorFacts.serves_resolution, true_and]
  · simp only [packetDemand, credit, ite_false, CampusTCPGapProgressMonitorFacts.serves_operation,
      false_and, or_false]

private theorem ticket_action (state : State input) (ticket : Work.Item (Ticket input.active input.passive))
    (member : ticket ∈ state.work.pending) : R.ticketAction state (some ticket.id) = some (.serve ticket.id) := by
  unfold R.ticketAction
  simp only [bind, Option.bind]
  cases found : state.work.pending.find? (fun item => item.id == ticket.id) with
  | none =>
    have absent := List.find?_eq_none.mp found ticket member
    exact False.elim (absent (beq_self_eq_true _))
  | some item => rfl

theorem DataIngress.packet_at (record : DataIngress initial allowance current monitor retries released) :
    M.packetAt monitor = some record.packetID := by rw [M.packetAt, record.phaseEq]; exact record.packetRef

theorem DataLink.packet_at (record : DataLink initial allowance current monitor retries released) :
    M.packetAt monitor = some record.packetID := by rw [M.packetAt, record.phaseEq]; exact record.packetRef

theorem AckIngress.packet_at (record : AckIngress initial allowance current monitor retries) :
    M.packetAt monitor = some record.packetID := by rw [M.packetAt, record.phaseEq]; exact record.packetRef

theorem AckLink.packet_at (record : AckLink initial allowance current monitor retries) :
    M.packetAt monitor = some record.packetID := by rw [M.packetAt, record.phaseEq]; exact record.packetRef

theorem DataIngress.next_action (record : DataIngress initial allowance current monitor retries released)
    (native : NativeEnv cut initial.gateway.seed.entry) (quantum : Nat) :
    M.nextAction (config initial native quantum allowance) current.report.final monitor =
      some (.assign record.output.index (native.ingress sender)) := by
  simp only [M.nextAction, record.phaseEq, R.ingressAction, record.outputRef, record.packetRef,
    record.output.stored, record.custody, bind, Option.bind, beq_self_eq_true, ite_true, pure]
  cases sender <;> rfl

theorem DataIngress.demand (record : DataIngress initial allowance current monitor retries released)
    (native : NativeEnv cut initial.gateway.seed.entry) (quantum : Nat) :
    M.nextDemand (config initial native quantum allowance) current.report.final monitor =
      some (packetDemand allowance monitor (.assign record.output.index (native.ingress sender)) record.packetID) := by
  rw [F.nextDemand_action _ _ _ record.waiting _ (record.next_action native quantum),
    M.packetAt, record.phaseEq, record.packetRef]
  rfl

theorem DataTicket.next_action (record : DataTicket initial native allowance current monitor retries released) (quantum : Nat) :
    M.nextAction (config initial native quantum allowance) current.report.final monitor = some (.serve record.ticket.id) := by
  simp only [M.nextAction, record.phaseEq, record.ticketRef]
  exact ticket_action _ _ record.pending

theorem DataTicket.completes (record : DataTicket initial native allowance current monitor retries released) :
    ∃ completed, Work.complete current.report.final.work record.ticket.id = .ok completed ∧ completed.item = record.ticket :=
  Theory.Outstanding.complete_item _ record.ticket (CampusTCPOrigins.Report.work_valid current.report) record.pending

theorem DataTicket.demand (record : DataTicket initial native allowance current monitor retries released) (quantum : Nat) :
    M.nextDemand (config initial native quantum allowance) current.report.final monitor = some (.operation (.serve record.ticket.id)) :=
  F.nextDemand_operation _ _ _ record.waiting _ (record.next_action quantum) (by rw [M.packetAt, record.phaseEq])

theorem DataLink.next_action (record : DataLink initial allowance current monitor retries released)
    (native : NativeEnv cut initial.gateway.seed.entry) (quantum : Nat) :
    M.nextAction (config initial native quantum allowance) current.report.final monitor =
      some (.deliver record.index record.emission.bytes true) := by
  simp only [M.nextAction, record.phaseEq, R.linkAction, record.serviceRef, record.packetRef,
    record.stored, record.emitted, record.custody, bind, Option.bind, beq_self_eq_true, ite_true, pure]

theorem DataLink.demand (record : DataLink initial allowance current monitor retries released)
    (native : NativeEnv cut initial.gateway.seed.entry) (quantum : Nat) :
    M.nextDemand (config initial native quantum allowance) current.report.final monitor =
      some (packetDemand allowance monitor (.deliver record.index record.emission.bytes true) record.packetID) := by
  rw [F.nextDemand_action _ _ _ record.waiting _ (record.next_action native quantum),
    M.packetAt, record.phaseEq, record.packetRef]
  rfl

theorem NeedAck.next_action (record : NeedAck initial allowance current monitor retries)
    (native : NativeEnv cut initial.gateway.seed.entry) (quantum : Nat) :
    M.nextAction (config initial native quantum allowance) current.report.final monitor = some (.emitAck sender.other true) := by
  rw [M.nextAction, record.phaseEq]
  rfl

theorem NeedAck.demand (record : NeedAck initial allowance current monitor retries)
    (native : NativeEnv cut initial.gateway.seed.entry) (quantum : Nat) :
    M.nextDemand (config initial native quantum allowance) current.report.final monitor = some (.operation (.emitAck sender.other true)) :=
  F.nextDemand_operation _ _ _ record.waiting _ (record.next_action native quantum) (by rw [M.packetAt, record.phaseEq])

theorem AckIngress.next_action (record : AckIngress initial allowance current monitor retries)
    (native : NativeEnv cut initial.gateway.seed.entry) (quantum : Nat) :
    M.nextAction (config initial native quantum allowance) current.report.final monitor =
      some (.assign record.output.index (native.ingress sender.other)) := by
  simp only [M.nextAction, record.phaseEq, R.ingressAction, record.outputRef, record.packetRef,
    record.output.stored, record.custody, bind, Option.bind, beq_self_eq_true, ite_true, pure]
  cases sender <;> rfl

theorem AckIngress.demand (record : AckIngress initial allowance current monitor retries)
    (native : NativeEnv cut initial.gateway.seed.entry) (quantum : Nat) :
    M.nextDemand (config initial native quantum allowance) current.report.final monitor =
      some (packetDemand allowance monitor (.assign record.output.index (native.ingress sender.other)) record.packetID) := by
  rw [F.nextDemand_action _ _ _ record.waiting _ (record.next_action native quantum),
    M.packetAt, record.phaseEq, record.packetRef]
  rfl

theorem AckTicket.next_action (record : AckTicket initial native allowance current monitor retries) (quantum : Nat) :
    M.nextAction (config initial native quantum allowance) current.report.final monitor = some (.serve record.ticket.id) := by
  simp only [M.nextAction, record.phaseEq, record.ticketRef]
  exact ticket_action _ _ record.pending

theorem AckTicket.completes (record : AckTicket initial native allowance current monitor retries) :
    ∃ completed, Work.complete current.report.final.work record.ticket.id = .ok completed ∧ completed.item = record.ticket :=
  Theory.Outstanding.complete_item _ record.ticket (CampusTCPOrigins.Report.work_valid current.report) record.pending

theorem AckTicket.demand (record : AckTicket initial native allowance current monitor retries) (quantum : Nat) :
    M.nextDemand (config initial native quantum allowance) current.report.final monitor = some (.operation (.serve record.ticket.id)) :=
  F.nextDemand_operation _ _ _ record.waiting _ (record.next_action quantum) (by rw [M.packetAt, record.phaseEq])

theorem AckLink.next_action (record : AckLink initial allowance current monitor retries)
    (native : NativeEnv cut initial.gateway.seed.entry) (quantum : Nat) :
    M.nextAction (config initial native quantum allowance) current.report.final monitor =
      some (.deliver record.index record.emission.bytes true) := by
  simp only [M.nextAction, record.phaseEq, R.linkAction, record.serviceRef, record.packetRef,
    record.stored, record.emitted, record.custody, bind, Option.bind, beq_self_eq_true, ite_true, pure]

theorem AckLink.demand (record : AckLink initial allowance current monitor retries)
    (native : NativeEnv cut initial.gateway.seed.entry) (quantum : Nat) :
    M.nextDemand (config initial native quantum allowance) current.report.final monitor =
      some (packetDemand allowance monitor (.deliver record.index record.emission.bytes true) record.packetID) := by
  rw [F.nextDemand_action _ _ _ record.waiting _ (record.next_action native quantum),
    M.packetAt, record.phaseEq, record.packetRef]
  rfl

theorem Waiting.recovery (record : Waiting initial allowance current monitor retries released)
    (native : NativeEnv cut initial.gateway.seed.entry) (quantum : Nat) :
    M.senderRecovery (config initial native quantum allowance) current.report.final = some record.live.senderFlight.recovery := by
  simp only [M.senderRecovery, current.connection, config, record.live.senderFlight.runtime]

def Waiting.tickTarget (record : Waiting initial allowance current monitor retries released) (quantum : Nat) : Nat :=
  min (record.live.senderFlight.recovery.now + quantum)
    (record.live.senderFlight.head.lastAt + record.live.senderFlight.recovery.rto)

theorem Waiting.tick_target_bounds (record : Waiting initial allowance current monitor retries released) (quantum : Nat)
    (positive : 0 < quantum)
    (early : record.live.senderFlight.recovery.now < record.live.senderFlight.head.lastAt + record.live.senderFlight.recovery.rto) :
    record.live.senderFlight.recovery.now < record.tickTarget quantum ∧
      record.tickTarget quantum ≤ record.live.senderFlight.recovery.now + quantum ∧
      record.tickTarget quantum ≤ record.live.senderFlight.head.lastAt + record.live.senderFlight.recovery.rto := by
  unfold Waiting.tickTarget
  omega

theorem Waiting.demand (record : Waiting initial allowance current monitor retries released)
    (native : NativeEnv cut initial.gateway.seed.entry) (quantum : Nat) :
    M.nextDemand (config initial native quantum allowance) current.report.final monitor =
      some (if record.live.senderFlight.recovery.now < record.live.senderFlight.head.lastAt + record.live.senderFlight.recovery.rto then
        .tick sender (record.tickTarget quantum) else .timeout sender) := by
  simp only [M.nextDemand, record.waiting, ite_true, record.recovery native quantum, record.live.senderFlight.deadline,
    bind, Option.bind]
  split <;> rfl

theorem Waiting.tick_demand (record : Waiting initial allowance current monitor retries released)
    (native : NativeEnv cut initial.gateway.seed.entry) (quantum : Nat)
    (early : record.live.senderFlight.recovery.now < record.live.senderFlight.head.lastAt + record.live.senderFlight.recovery.rto) :
    M.nextDemand (config initial native quantum allowance) current.report.final monitor = some (.tick sender (record.tickTarget quantum)) := by
  rw [record.demand native quantum]
  simp only [early, ite_true]

theorem Waiting.timeout_demand (record : Waiting initial allowance current monitor retries released)
    (native : NativeEnv cut initial.gateway.seed.entry) (quantum : Nat)
    (due : record.live.senderFlight.head.lastAt + record.live.senderFlight.recovery.rto ≤ record.live.senderFlight.recovery.now) :
    M.nextDemand (config initial native quantum allowance) current.report.final monitor = some (.timeout sender) := by
  rw [record.demand native quantum]
  simp only [Nat.not_lt.mpr due, ite_false]

theorem NeedRead.next_action (record : NeedRead initial allowance current monitor retries)
    (native : NativeEnv cut initial.gateway.seed.entry) (quantum : Nat) :
    M.nextAction (config initial native quantum allowance) current.report.final monitor = some (.read sender.other (lower ++ upper).length) := by
  rw [M.nextAction, record.phaseEq]
  rfl

theorem NeedRead.demand (record : NeedRead initial allowance current monitor retries)
    (native : NativeEnv cut initial.gateway.seed.entry) (quantum : Nat) :
    M.nextDemand (config initial native quantum allowance) current.report.final monitor = some (.operation (.read sender.other (lower ++ upper).length)) :=
  F.nextDemand_operation _ _ _ record.waiting _ (record.next_action native quantum) (by rw [M.packetAt, record.phaseEq])

theorem Done.demand (record : Done initial allowance current monitor retries)
    (native : NativeEnv cut initial.gateway.seed.entry) (quantum : Nat) :
    M.nextDemand (config initial native quantum allowance) current.report.final monitor = none := by
  simp only [M.nextDemand, record.waiting, Bool.false_eq_true, ite_false, M.nextAction, record.phaseEq, bind, Option.bind]

theorem Done.rank_zero (record : Done initial allowance current monitor retries)
    (native : NativeEnv cut initial.gateway.seed.entry) (quantum : Nat) :
    monitor.rank (config initial native quantum allowance) current.report.final = 0 := by
  simp only [CampusTCPGapProgressMonitor.Monitor.rank, record.waiting, Bool.false_eq_true, ite_false, record.phaseEq]

theorem Evidence.pending_positive (evidence : Evidence initial native allowance current monitor) (quantum : Nat)
    (positive : 0 < monitor.rank (config initial native quantum allowance) current.report.final) :
    ∃ demand, M.nextDemand (config initial native quantum allowance) current.report.final monitor = some demand := by
  cases evidence with
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

theorem Evidence.done_of_rank_zero (evidence : Evidence initial native allowance current monitor) (quantum : Nat)
    (zero : monitor.rank (config initial native quantum allowance) current.report.final = 0) :
    ∃ retries, Nonempty (Done initial allowance current monitor retries) := by
  cases evidence with
  | dataIngress record =>
    simp only [CampusTCPGapProgressMonitor.Monitor.rank, record.waiting, Bool.false_eq_true, ite_false,
      record.phaseEq, CampusTCPRoundMonitor.Phase.rank] at zero
    omega
  | dataTicket record =>
    simp only [CampusTCPGapProgressMonitor.Monitor.rank, record.waiting, Bool.false_eq_true, ite_false,
      record.phaseEq, CampusTCPRoundMonitor.Phase.rank] at zero
    omega
  | dataLink record =>
    simp only [CampusTCPGapProgressMonitor.Monitor.rank, record.waiting, Bool.false_eq_true, ite_false,
      record.phaseEq, CampusTCPRoundMonitor.Phase.rank] at zero
    omega
  | needAck record =>
    simp only [CampusTCPGapProgressMonitor.Monitor.rank, record.waiting, Bool.false_eq_true, ite_false,
      record.phaseEq, CampusTCPRoundMonitor.Phase.rank] at zero
    omega
  | ackIngress record =>
    simp only [CampusTCPGapProgressMonitor.Monitor.rank, record.waiting, Bool.false_eq_true, ite_false,
      record.phaseEq, CampusTCPRoundMonitor.Phase.rank] at zero
    omega
  | ackTicket record =>
    simp only [CampusTCPGapProgressMonitor.Monitor.rank, record.waiting, Bool.false_eq_true, ite_false,
      record.phaseEq, CampusTCPRoundMonitor.Phase.rank] at zero
    omega
  | ackLink record =>
    simp only [CampusTCPGapProgressMonitor.Monitor.rank, record.waiting, Bool.false_eq_true, ite_false,
      record.phaseEq, CampusTCPRoundMonitor.Phase.rank] at zero
    omega
  | waiting record =>
    simp only [CampusTCPGapProgressMonitor.Monitor.rank, record.waiting, ite_true] at zero
    omega
  | needRead record =>
    simp only [CampusTCPGapProgressMonitor.Monitor.rank, record.waiting, Bool.false_eq_true, ite_false, record.phaseEq] at zero
    omega
  | done record => exact ⟨_, ⟨record⟩⟩

theorem Evidence.rank_positive (evidence : Evidence initial native allowance current monitor) (quantum : Nat)
    (unfinished : monitor.phase ≠ .done) : 0 < monitor.rank (config initial native quantum allowance) current.report.final := by
  by_cases positive : 0 < monitor.rank (config initial native quantum allowance) current.report.final
  · exact positive
  · have zero : monitor.rank (config initial native quantum allowance) current.report.final = 0 := by omega
    obtain ⟨_, ⟨done⟩⟩ := evidence.done_of_rank_zero quantum zero
    exact False.elim (unfinished done.phaseEq)

theorem Evidence.pending (evidence : Evidence initial native allowance current monitor) (quantum : Nat)
    (unfinished : monitor.phase ≠ .done) :
    ∃ demand, M.nextDemand (config initial native quantum allowance) current.report.final monitor = some demand :=
  evidence.pending_positive quantum (evidence.rank_positive quantum unfinished)

end Netlib.Check.CampusTCPGapProgressEvidence
