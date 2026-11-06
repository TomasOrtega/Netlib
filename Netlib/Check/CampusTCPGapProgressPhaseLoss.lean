import Netlib.Check.CampusTCPGapProgressDrop
import Netlib.Check.CampusTCPGapProgressRetry
import Netlib.Check.CampusTCPGapProgressRank

/-!
# Actual loss phases in held-gap progress

Each selected drop consumes its actual pending identity.
The first timer reserve uses the elapsed time at the initial cut.
-/

namespace Netlib.Check.CampusTCPGapProgressEvidence

open Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPRoundPhaseBase (Move)
open CampusTCPGapProgressStart (GapInitial NativeEnv)
open CampusTCPGapProgressSetup (config)

namespace M
export CampusTCPGapProgressMonitor (Monitor Demand observe nextDemand senderRecovery waitBound)
end M

variable {input : Input} {complete : H.Completed input.active input.passive}
  {cut current : Cut input complete} {sender : Actor} {lower upper : List UInt8}
  {initial : GapInitial cut sender lower upper} {native : NativeEnv cut initial.gateway.seed.entry}
  {quantum allowance retries : Nat} {monitor : M.Monitor} {released : Bool}
  {phase : CampusTCPRoundMonitor.Phase} {id : Nat} {action : CampusTCPRoundMonitor.Action}

theorem Active.remaining (record : Active initial allowance current monitor retries released phase)
    (native : NativeEnv cut initial.gateway.seed.entry) (quantum : Nat) :
    record.live.senderFlight.head.lastAt + record.live.senderFlight.recovery.rto -
      record.live.senderFlight.recovery.now ≤ M.waitBound (config initial native quantum allowance) monitor.retries := by
  let flight := record.live.senderFlight
  change flight.head.lastAt + flight.recovery.rto - flight.recovery.now ≤ _
  rw [record.retryCount]
  by_cases first : retries = 0
  · have monotone := flight.monotone
    simp only [Endpoint.State.now, initial.flight.runtime, flight.runtime,
      Option.map_some, Option.getD_some] at monotone
    have head := flight.firstTime first
    have rto : flight.recovery.rto = initial.flight.recovery.rto := by
      rw [flight.rto, first, initial.flight.rto]
    simp only [M.waitBound, first, ite_true, config]
    rw [head, rto]
    omega
  · have clocked := flight.clocked flight.head (by rw [flight.source]; simp)
    simp only [M.waitBound, first, ite_false, config, initial.flight.rto]
    rw [← flight.rto]
    omega

theorem Active.drop_at (record : Active initial allowance current monitor retries released phase)
    (native : NativeEnv cut initial.gateway.seed.entry) (quantum : Nat)
    (item : Theory.PacketCustody.Item (Transit input)) (member : item ∈ current.report.final.custody.pending)
    (budget : monitor.drops.length < allowance) (action : CampusTCPRoundMonitor.Action)
    (selected : M.nextDemand (config initial native quantum allowance) current.report.final monitor =
      some (.resolution action item.id)) :
    ∃ actual : Step input, ∃ move : Move current actual,
      actual.event = .dropPacket item.id ∧
      Nonempty (Waiting initial allowance move.after
        (M.observe (config initial native quantum allowance) monitor actual) retries released) := by
  obtain ⟨actual, ⟨appended⟩⟩ := CampusTCPRecoveryRoundDrop.append current item member
  let move := appended.move
  let live := CampusTCPGapProgressDrop.live_after record.live appended
  have observed := CampusTCPGapProgressDrop.observe_selected appended.facts
    (config initial native quantum allowance) monitor action selected
  let first := record.first.map (fun receipt => receipt.reframe (by
    rw [move.final, appended.facts.receipts]
    exact receipt.stored))
  refine ⟨actual, move, appended.facts.event, ?_⟩
  rw [observed]
  refine ⟨{
    live, waiting := rfl, retryCount := record.retryCount, dropCount := ?_, bound := ?_, drops := ?_
    dropStep := actual, member := move.member, dropPacket := item.id, lastDrop := ?_
    facts := by simpa only [appended.facts.beforeEq] using appended.facts
    absent := ?_, first, firstRef := ?_, firstOperation := ?_ }⟩
  · simp only [List.length_append, List.length_cons, List.length_nil, Nat.zero_add, record.dropCount]
  · have count := record.dropCount
    omega
  · simpa only [dropID, appended.facts.event, Option.toList_some] using record.drops.append move
  · simp
  · rw [move.final, appended.facts.custody]
    exact appended.facts.resolved.completed.no_pending_id (CampusTCPCustodyFacts.Report.valid current.report).1
  · simpa only [first, Option.map_map, Function.comp_def, FirstReceipt.reframe] using record.firstRef
  · change record.live.history.streams.first = _
    simpa only [first, Option.map_map, Function.comp_def, FirstReceipt.reframe] using record.firstOperation

structure Dropped (initial : GapInitial cut sender lower upper) (native : NativeEnv cut initial.gateway.seed.entry)
    (quantum allowance : Nat) (current : Cut input complete) (monitor : M.Monitor) (id : Nat) where
  actual : Step input
  move : Move current actual
  event : actual.event = .dropPacket id
  evidence : Nonempty (Evidence initial native allowance move.after
    (M.observe (config initial native quantum allowance) monitor actual))
  decreases : (M.observe (config initial native quantum allowance) monitor actual).rank
      (config initial native quantum allowance) move.after.report.final <
    monitor.rank (config initial native quantum allowance) current.report.final

private theorem packet_resolution (allowance : Nat) (monitor : M.Monitor)
    (expected action : CampusTCPRoundMonitor.Action) (packet id : Nat)
    (same : packetDemand allowance monitor expected packet = .resolution action id) :
    monitor.drops.length < allowance ∧ packet = id := by
  by_cases budget : monitor.drops.length < allowance
  · simp only [packetDemand, budget, ite_true, CampusTCPGapProgressMonitor.Demand.resolution.injEq] at same
    exact ⟨budget, same.2⟩
  · simp only [packetDemand, budget, ite_false, reduceCtorEq] at same

private theorem drop_packet (record : Active initial allowance current monitor retries released phase)
    (budget : allowance ≤ 2)
    (eligible : phase = .dataIngress ∨ phase = .dataLink ∨ phase = .ackIngress ∨ phase = .ackLink)
    (predicate : Transit input → Bool) (packet : Nat)
    (custody : current.report.final.custody.pendingID predicate = some packet)
    (expected action : CampusTCPRoundMonitor.Action) (id : Nat)
    (next : M.nextDemand (config initial native quantum allowance) current.report.final monitor =
      some (packetDemand allowance monitor expected packet))
    (selected : M.nextDemand (config initial native quantum allowance) current.report.final monitor =
      some (.resolution action id)) : Nonempty (Dropped initial native quantum allowance current monitor id) := by
  have equal := Option.some.inj (next.symm.trans selected)
  obtain ⟨credit, same⟩ := packet_resolution allowance monitor expected action packet id equal
  obtain ⟨item, member, itemID, _⟩ := current.report.final.custody.pendingID_source predicate packet custody
  have identity : item.id = id := itemID.trans same
  have chosen : M.nextDemand (config initial native quantum allowance) current.report.final monitor =
      some (.resolution action item.id) := by rw [identity]; exact selected
  obtain ⟨actual, move, event, ⟨waiting⟩⟩ := record.drop_at native quantum item member credit action chosen
  obtain ⟨facts⟩ := CampusTCPRecoveryRoundDrop.Step.facts actual item (by rw [move.beforeEq]; exact member) event
  have observed := CampusTCPGapProgressDrop.observe_selected facts
    (config initial native quantum allowance) monitor action (by rw [move.beforeEq]; exact chosen)
  have retryCredit : monitor.retries < allowance := by
    have count := record.dropCount
    rw [record.retryCount]
    omega
  have phaseNow : monitor.phase = .dataIngress ∨ monitor.phase = .dataLink ∨
      monitor.phase = .ackIngress ∨ monitor.phase = .ackLink := by rw [record.phaseEq]; exact eligible
  have runtime : M.senderRecovery (config initial native quantum allowance) current.report.final =
      some record.live.senderFlight.recovery := by
    simp only [M.senderRecovery, current.connection, config, record.live.senderFlight.runtime]
  have sameRecovery : M.senderRecovery (config initial native quantum allowance) move.after.report.final =
      M.senderRecovery (config initial native quantum allowance) current.report.final := by
    have connected : move.after.report.final.connection = current.report.final.connection := by
      rw [move.final, facts.connection, move.beforeEq]
    unfold M.senderRecovery
    rw [connected]
  refine ⟨⟨actual, move, event.trans (congrArg Event.dropPacket identity), ⟨.waiting waiting⟩, ?_⟩⟩
  rw [observed]
  exact CampusTCPGapProgressMonitor.rank_drop _ _ _ _ item.id record.waiting budget retryCredit phaseNow
    record.live.senderFlight.recovery runtime sameRecovery record.live.senderFlight.deadline (record.remaining native quantum)

theorem Evidence.drop_selected (evidence : Evidence initial native allowance current monitor)
    (budget : allowance ≤ 2)
    (selected : M.nextDemand (config initial native quantum allowance) current.report.final monitor =
      some (.resolution action id)) : Nonempty (Dropped initial native quantum allowance current monitor id) := by
  cases evidence with
  | dataIngress record =>
    exact drop_packet record.toActive budget (by simp) _ _ record.custody _ _ _ (record.demand native quantum) selected
  | dataTicket record => rw [record.demand quantum] at selected; cases selected
  | dataLink record =>
    exact drop_packet record.toActive budget (by simp) _ _ record.custody _ _ _ (record.demand native quantum) selected
  | needAck record => rw [record.demand native quantum] at selected; cases selected
  | ackIngress record =>
    exact drop_packet record.toActive budget (by simp) _ _ record.custody _ _ _ (record.demand native quantum) selected
  | ackTicket record => rw [record.demand quantum] at selected; cases selected
  | ackLink record =>
    exact drop_packet record.toActive budget (by simp) _ _ record.custody _ _ _ (record.demand native quantum) selected
  | waiting record => rw [record.demand native quantum] at selected; split at selected <;> cases selected
  | needRead record => rw [record.demand native quantum] at selected; cases selected
  | done record => rw [record.demand native quantum] at selected; cases selected

end Netlib.Check.CampusTCPGapProgressEvidence
