import Netlib.Check.CampusTCPRecoveryRoundEvidence
import Netlib.Check.CampusTCPRecoveryRoundMonitorFacts
import Netlib.Check.CampusTCPRecoveryRoundRetry
import Netlib.Check.CampusTCPRecoveryRoundDemand
import Netlib.Check.CampusTCPRecoveryRoundRank

/-!
# Actual loss and retry phases

A failed attempt has one stored packet drop.
The next transmission comes from the sender's real timer.
-/

namespace Netlib.Check.CampusTCPRecoveryRoundEvidence

noncomputable section

open Protocol.TCP CampusTCPModel CampusTCPEnabled CampusTCPRoundStart
open CampusTCPRound (Cut)
open CampusTCPRecoveryRoundPhaseBase (At Anchor)
namespace M
export CampusTCPRecoveryRoundMonitor (Monitor Demand Config observe nextDemand observeDrop)
end M

variable {input : Input} {events : List Event} {report : Report input events}
  {complete : H.Completed input.active input.passive} {request : Request input}
  {initial : Initial report complete request} {native : NativeEnv initial} {quantum : Nat}
  {current : Cut input complete} {monitor : M.Monitor} {sentAt retries : Nat} {released : Bool}
  {phase : CampusTCPRoundMonitor.Phase}
  {id : Nat} {action : CampusTCPRoundMonitor.Action}

private theorem streams_cast_first (same : left = right)
    (history : CampusTCPRecoveryRoundHistory.Streams bytes right released) :
    (Eq.mpr (congrArg (fun operations => CampusTCPRecoveryRoundHistory.Streams bytes operations released) same) history).first =
      history.first := by cases same; rfl

private theorem history_first_eq (old : CampusTCPRecoveryRoundHistory.History initial before released)
    (next : CampusTCPRecoveryRoundHistory.History initial after released)
    (operations : applicationSteps after.endpoints .server = applicationSteps before.endpoints .server) :
    next.first = old.first := by
  have lists : next.first.toList = old.first.toList := by rw [← next.releases, operations, old.releases]
  cases nextFirst : next.first <;> cases oldFirst : old.first <;> simp_all

theorem Active.drop_at (record : Active initial current monitor sentAt retries released phase)
    (item : Theory.PacketCustody.Item (Transit input)) (member : item ∈ current.report.final.custody.pending)
    (budget : monitor.drops.length < 2) (action : CampusTCPRoundMonitor.Action)
    (selected : M.nextDemand (CampusTCPRecoveryRoundPhaseBase.config initial native quantum)
      current.report.final monitor = some (.resolution action item.id)) :
    ∃ actual : Step input, ∃ move : CampusTCPRoundPhaseBase.Move current actual,
      actual.event = .dropPacket item.id ∧
      Nonempty (Waiting initial move.after
        (M.observe (CampusTCPRecoveryRoundPhaseBase.config initial native quantum) monitor actual) sentAt retries released) := by
  obtain ⟨actual, ⟨appended⟩⟩ := CampusTCPRecoveryRoundDrop.append current item member
  let move := appended.move
  let live := record.live.drop appended
  have observed := appended.facts.observe (CampusTCPRecoveryRoundPhaseBase.config initial native quantum) monitor action selected
  let first := record.first.map (fun receipt => receipt.reframe (by
    rw [move.final, appended.facts.receipts]
    exact receipt.stored))
  refine ⟨actual, move, appended.facts.event, ?_⟩
  rw [observed]
  refine ⟨⟨live, rfl, record.retryCount, ?_, ?_, ?_, actual, move.member, item.id, ?_, ?_, ?_, first, ?_, ?_⟩⟩
  · simp only [CampusTCPRecoveryRoundMonitor.observeDrop, List.length_append, List.length_cons,
      List.length_nil, Nat.zero_add, record.dropCount]
  · have count := record.dropCount
    omega
  · simpa only [dropID, appended.facts.event, Option.toList_some, CampusTCPRecoveryRoundMonitor.observeDrop] using record.drops.append move
  · simp [CampusTCPRecoveryRoundMonitor.observeDrop]
  · simpa only [appended.facts.beforeEq] using appended.facts
  · rw [move.final, appended.facts.custody]
    exact appended.facts.resolved.completed.no_pending_id (CampusTCPCustodyFacts.Report.valid current.report).1
  · simpa only [first, CampusTCPRecoveryRoundMonitor.observeDrop, Option.map_map, Function.comp_def,
      FirstReceipt.reframe] using record.firstRef
  · have history : live.history.first = record.live.history.first := by
      change (Eq.mpr (congrArg (fun operations => CampusTCPRecoveryRoundHistory.Streams request.bytes operations released)
        (congrArg (fun endpoints => applicationSteps endpoints .server) appended.endpoints)) record.live.history).first = _
      exact streams_cast_first (congrArg (fun endpoints => applicationSteps endpoints .server) appended.endpoints)
        record.live.history
    rw [history]
    simpa only [first, Option.map_map, Function.comp_def, FirstReceipt.reframe] using record.firstOperation

theorem Waiting.retry_at (record : Waiting initial current monitor sentAt retries released)
    (due : record.live.sender.entry.lastAt + record.live.sender.recovery.rto ≤ record.live.sender.recovery.now) :
    ∃ actual : Step input, ∃ move : CampusTCPRoundPhaseBase.Move current actual,
      actual.event = .timeout .client true ∧
      Nonempty (DataIngress initial move.after
        (M.observe (CampusTCPRecoveryRoundPhaseBase.config initial native quantum) monitor actual) sentAt (retries + 1) released) := by
  obtain ⟨actual, ⟨retry⟩⟩ := CampusTCPRecoveryRoundRetry.retry_at record.live native quantum monitor
    record.waiting record.retryCount record.credit due
  let move := retry.move
  let first := record.first.map (fun receipt => receipt.reframe (by
    rw [move.final, retry.facts.receipts]
    exact receipt.stored))
  have history : retry.next.history.first = record.live.history.first := by
    apply history_first_eq record.live.history retry.next.history
    have operations := CampusTCPRoundPhaseHistory.Move.local_history move .client (.timeout true)
      (by rw [retry.facts.event]; exact .timeout _) retry.application.operation retry.application.recorded .server
    simpa only [reduceCtorEq, ite_false, List.append_nil] using operations
  let output : DataOutput initial move.after := ⟨actual.before.outputs.length, retry.application.produced,
    retry.source, by rw [retry.application.production]; rfl,
    by rw [retry.application.production]; trivial, retry.fields⟩
  refine ⟨actual, move, retry.facts.event, ?_⟩
  refine ⟨⟨⟨retry.next, ?_, ?_, retry.monitorRetries, ?_, ?_, first, ?_, ?_⟩,
    output, retry.packetID, retry.custody, ?_, ?_⟩⟩
  · rw [retry.observed]

  · rw [retry.observed]
  · rw [retry.observed]
    exact record.dropCount
  · have log := record.drops.append move
    simpa only [dropID, retry.facts.event, Option.toList_none, List.append_nil, retry.observed] using log
  · rw [retry.observed]
    simpa only [first, Option.map_map, Function.comp_def, FirstReceipt.reframe] using record.firstRef
  · rw [history]
    simpa only [first, Option.map_map, Function.comp_def, FirstReceipt.reframe] using record.firstOperation
  · rw [retry.observed]
  · rw [retry.observed]


structure Dropped (initial : Initial report complete request) (native : NativeEnv initial) (quantum : Nat)
    (current : Cut input complete) (monitor : M.Monitor) (id : Nat) where
  actual : Step input
  move : CampusTCPRoundPhaseBase.Move current actual
  event : actual.event = .dropPacket id
  evidence : Nonempty (Evidence initial native quantum move.after
    (M.observe (CampusTCPRecoveryRoundPhaseBase.config initial native quantum) monitor actual))
  decreases : (M.observe (CampusTCPRecoveryRoundPhaseBase.config initial native quantum) monitor actual).rank
      (CampusTCPRecoveryRoundPhaseBase.config initial native quantum) move.after.report.final <
    monitor.rank (CampusTCPRecoveryRoundPhaseBase.config initial native quantum) current.report.final

private theorem packet_resolution (monitor : M.Monitor) (expected action : CampusTCPRoundMonitor.Action)
    (packet id : Nat) (same : packetDemand monitor expected packet = .resolution action id) :
    monitor.drops.length < 2 ∧ packet = id := by
  by_cases budget : monitor.drops.length < 2
  · simp only [packetDemand, budget, ite_true, CampusTCPRecoveryRoundMonitor.Demand.resolution.injEq] at same
    exact ⟨budget, same.2⟩
  · simp only [packetDemand, budget, ite_false, reduceCtorEq] at same

private theorem drop_packet (record : Active initial current monitor sentAt retries released phase)
    (eligible : phase = .dataIngress ∨ phase = .dataLink ∨ phase = .ackIngress ∨ phase = .ackLink)
    (predicate : Transit input → Bool) (packet : Nat)
    (custody : current.report.final.custody.pendingID predicate = some packet)
    (expected action : CampusTCPRoundMonitor.Action) (id : Nat)
    (next : M.nextDemand (CampusTCPRecoveryRoundPhaseBase.config initial native quantum) current.report.final monitor =
      some (packetDemand monitor expected packet))
    (selected : M.nextDemand (CampusTCPRecoveryRoundPhaseBase.config initial native quantum) current.report.final monitor =
      some (.resolution action id)) : Nonempty (Dropped initial native quantum current monitor id) := by
  have equal := Option.some.inj (next.symm.trans selected)
  obtain ⟨budget, same⟩ := packet_resolution monitor expected action packet id equal
  obtain ⟨item, member, itemID, _⟩ := current.report.final.custody.pendingID_source predicate packet custody
  have identity : item.id = id := itemID.trans same
  have chosen : M.nextDemand (CampusTCPRecoveryRoundPhaseBase.config initial native quantum) current.report.final monitor =
      some (.resolution action item.id) := by rw [identity]; exact selected
  obtain ⟨actual, move, event, ⟨waiting⟩⟩ := record.drop_at item member budget action chosen
  obtain ⟨facts⟩ := CampusTCPRecoveryRoundDrop.Step.facts actual item (by rw [move.beforeEq]; exact member) event
  have observed := facts.observe (CampusTCPRecoveryRoundPhaseBase.config initial native quantum) monitor action
    (by rw [move.beforeEq]; exact chosen)
  have credit : monitor.retries < 2 := by
    have count := record.dropCount
    rw [record.retryCount]
    omega
  have clocked := record.live.sender.clocked record.live.sender.entry (by rw [record.live.sender.source]; simp)
  have remaining : (record.live.sender.entry.lastAt + record.live.sender.recovery.rto) - record.live.sender.recovery.now ≤
      2 ^ monitor.retries * 1000 := by
    rw [record.retryCount, ← record.live.sender.rto]
    omega
  have phaseNow : monitor.round.phase = .dataIngress ∨ monitor.round.phase = .dataLink ∨
      monitor.round.phase = .ackIngress ∨ monitor.round.phase = .ackLink := by rw [record.phaseEq]; exact eligible
  have runtime : CampusTCPRecoveryRoundMonitor.clientRecovery current.report.final = some record.live.sender.recovery := by
    simp only [CampusTCPRecoveryRoundMonitor.clientRecovery, current.connection, record.live.sender.runtime]
  have sameRecovery : CampusTCPRecoveryRoundMonitor.clientRecovery move.after.report.final =
      CampusTCPRecoveryRoundMonitor.clientRecovery current.report.final := by
    have connected : move.after.report.final.connection = current.report.final.connection := by
      rw [move.final, facts.connection, move.beforeEq]
    unfold CampusTCPRecoveryRoundMonitor.clientRecovery
    rw [connected]
  refine ⟨⟨actual, move, event.trans (congrArg Event.dropPacket identity), ⟨.waiting waiting⟩, ?_⟩⟩
  rw [observed]
  exact CampusTCPRecoveryRoundMonitor.rank_drop _ _ _ _ item.id record.waiting credit phaseNow
    record.live.sender.recovery runtime sameRecovery record.live.sender.deadline remaining

theorem Evidence.drop_selected (evidence : Evidence initial native quantum current monitor)
    (selected : M.nextDemand (CampusTCPRecoveryRoundPhaseBase.config initial native quantum) current.report.final monitor =
      some (.resolution action id)) : Nonempty (Dropped initial native quantum current monitor id) := by
  cases evidence with
  | needSend record => rw [record.demand native quantum] at selected; cases selected
  | dataIngress record =>
    exact drop_packet record.toActive (by simp) _ _ record.custody _ _ _ (record.demand native quantum) selected
  | dataTicket record => rw [record.demand quantum] at selected; cases selected
  | dataLink record =>
    exact drop_packet record.toActive (by simp) _ _ record.custody _ _ _ (record.demand native quantum) selected
  | needAck record => rw [record.demand native quantum] at selected; cases selected
  | ackIngress record =>
    exact drop_packet record.toActive (by simp) _ _ record.custody _ _ _ (record.demand native quantum) selected
  | ackTicket record => rw [record.demand quantum] at selected; cases selected
  | ackLink record =>
    exact drop_packet record.toActive (by simp) _ _ record.custody _ _ _ (record.demand native quantum) selected
  | waiting record => rw [record.demand native quantum] at selected; split at selected <;> cases selected
  | needRead record => rw [record.demand native quantum] at selected; cases selected
  | done record => rw [record.demand native quantum] at selected; cases selected

end

end Netlib.Check.CampusTCPRecoveryRoundEvidence
