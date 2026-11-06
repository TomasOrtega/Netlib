import Netlib.Check.CampusTCPTwoProgressPhaseState
import Netlib.Check.CampusTCPTwoProgressPhaseObserveReceive
import Netlib.Check.CampusTCPTwoProgressPathRetain
import Netlib.Check.CampusTCPTwoProgressPathsDistinct

namespace Netlib.Check.CampusTCPTwoProgressPhaseReceiveState

open Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart CampusTCPTwoProgressPhaseBase CampusTCPTwoProgressPhaseState
open CampusTCPTwoProgressPaths
open CampusTCPTwoProgressSetup (config)

namespace O
export CampusTCPTwoProgressPhaseObserveReceive (dataLaneAt receiptLane receiptUpdate)
end O
namespace D
export CampusTCPTwoProgressPhaseReceive (Delivered Arrival)
end D
namespace Debt
export CampusTCPTwoProgressPhaseDebt (Work Debt)
end Debt
namespace Distinct
export CampusTCPTwoProgressPathsDistinct
  (service_index_ne ingress_link_packet_ne link_ingress_packet_ne link_packet_ne)
end Distinct

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current : Cut input complete} {sender : Actor} {gateway : Gateway} {lower upper chunk : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {native : NativeEnv cut gateway initial.gatewayState.session.entry} {quantum allowance : Nat}
variable {monitor : M.Monitor} {sent : S.Stage initial} {beforeStage afterStage : R.Stage}
variable {core : Core initial native quantum allowance current monitor sent beforeStage}
variable {part other : S.Part} {lane otherLane : M.Lane}

private theorem original_not_send (value : OriginalLane initial native current view beforeStage part lane) :
    lane.phase ≠ .needSend := by
  cases value with
  | done phase => rw [phase]; decide
  | active work _ =>
    cases work with
    | ingress path _ => rw [path.phase]; decide
    | ticket path _ => rw [path.phase]; decide
    | link path _ _ => rw [path.phase]; decide

theorem receive_sender_recovery {path : DataLink initial current part lane}
    (value : D.Delivered core path afterStage chunk) :
    value.next.live.senderFlight.recovery = core.live.senderFlight.recovery := by
  apply Option.some.inj
  exact value.next.live.senderFlight.runtime.symm.trans
    ((congrArg Endpoint.State.recovery value.value.peer).trans core.live.senderFlight.runtime)

private theorem range_same {path : DataLink initial current part lane}
    (value : D.Delivered core path afterStage chunk) (role : S.Part) :
    CampusTCPTwoProgressPathsReady.rangeAt value.next.live.gatewayState role =
      CampusTCPTwoProgressPathsReady.rangeAt core.live.gatewayState role := by
  have same := core.live.gatewayState.ranges_same value.next.live.gatewayState (value.value.gateway gateway)
  cases role
  · exact same.1
  · exact same.2

private theorem consumed {path : DataLink initial current part lane} (value : D.Delivered core path afterStage chunk) :
    CampusTCPTwoProgressPathRetain.consumedPacket current.report.final value.value.delivery.step.event = some path.packetID := by
  rw [value.value.delivery.event]
  exact path.custody

private theorem different_packets {path : DataLink initial current part lane}
    (value : D.Delivered core path afterStage chunk) (id : Nat) (different : path.packetID ≠ id) :
    CampusTCPTwoProgressPathRetain.consumedPacket current.report.final value.value.delivery.step.event ≠ some id := by
  rw [consumed value]
  exact fun same => different (Option.some.inj same)

private def retain_work {path : DataLink initial current part lane}
    (value : D.Delivered core path afterStage chunk) (work : Debt.Work initial native current other otherLane)
    (different : part ≠ other) : Debt.Work initial native value.value.move.after other otherLane := by
  cases part <;> cases other
  all_goals try exact False.elim (different rfl)
  case lower.upper =>
    cases work with
    | ingress waiting => exact .ingress (waiting.after_move value.value.move
        (different_packets value _ (Distinct.link_ingress_packet_ne path waiting)))
    | ticket waiting => exact .ticket (waiting.after_quiet value.value.move (by rw [value.value.delivery.event]; trivial))
    | link waiting => exact .link (waiting.after_move value.value.move
        (different_packets value _ (Distinct.link_packet_ne path waiting)))
  case upper.lower =>
    cases work with
    | ingress waiting => exact .ingress (waiting.after_move value.value.move
        (different_packets value _ (Ne.symm (Distinct.ingress_link_packet_ne waiting path))))
    | ticket waiting => exact .ticket (waiting.after_quiet value.value.move (by rw [value.value.delivery.event]; trivial))
    | link waiting => exact .link (waiting.after_move value.value.move
        (different_packets value _ (Ne.symm (Distinct.link_packet_ne waiting path))))

private def retain_data {path : DataLink initial current part lane}
    (value : D.Delivered core path afterStage chunk)
    (work : DataWork initial native current core.live.gatewayState other otherLane) (different : part ≠ other) :
    DataWork initial native value.value.move.after value.next.live.gatewayState other otherLane := by
  cases part <;> cases other
  all_goals try exact False.elim (different rfl)
  case lower.upper =>
    cases work with
    | ingress waiting source =>
      exact .ingress (waiting.after_move value.value.move
        (different_packets value _ (Distinct.link_ingress_packet_ne path waiting))) (source.retain_steps value.value.move.retained)
    | ticket waiting source =>
      exact .ticket (waiting.after_quiet value.value.move (by rw [value.value.delivery.event]; trivial))
        (source.retain_steps value.value.move.retained)
    | link waiting source covered =>
      exact .link (waiting.after_move value.value.move
        (different_packets value _ (Distinct.link_packet_ne path waiting))) (source.retain_steps value.value.move.retained)
        (by rw [range_same value]; exact covered)
  case upper.lower =>
    cases work with
    | ingress waiting source =>
      exact .ingress (waiting.after_move value.value.move
        (different_packets value _ (Ne.symm (Distinct.ingress_link_packet_ne waiting path)))) (source.retain_steps value.value.move.retained)
    | ticket waiting source =>
      exact .ticket (waiting.after_quiet value.value.move (by rw [value.value.delivery.event]; trivial))
        (source.retain_steps value.value.move.retained)
    | link waiting source covered =>
      exact .link (waiting.after_move value.value.move
        (different_packets value _ (Ne.symm (Distinct.link_packet_ne waiting path)))) (source.retain_steps value.value.move.retained)
        (by rw [range_same value]; exact covered)

private theorem arrived_other (arrival : D.Arrival beforeStage part afterStage) (different : part ≠ other) :
    Arrived afterStage other → Arrived beforeStage other := by
  cases arrival <;> cases other <;> simp_all [Arrived]

private def retain_original {path : DataLink initial current part lane}
    (value : D.Delivered core path afterStage chunk) (arrival : D.Arrival beforeStage part afterStage)
    (old : OriginalLane initial native current core.live.gatewayState beforeStage other otherLane)
    (different : part ≠ other) :
    OriginalLane initial native value.value.move.after value.next.live.gatewayState afterStage other otherLane := by
  cases old with
  | done phase => exact .done phase
  | active work missing => exact .active (retain_data value work different) (fun arrived => missing (arrived_other arrival different arrived))

theorem receive_pending_queue {path : DataLink initial current part lane}
    (value : D.Delivered core path afterStage chunk) : value.next.live.receiverFacts.reaction.work.pending ≠ [] := by
  have same : value.next.live.receiverFacts.reaction = value.value.receiver.reaction := by
    apply Option.some.inj
    exact value.next.live.receiverFacts.ackRuntime.symm.trans value.value.receiver.ackRuntime
  rw [same]
  exact value.value.pending

private theorem missing_lower_retired (core : Core initial native quantum allowance current monitor sent beforeStage)
    (missing : ¬Arrived beforeStage .lower) : sent.retiredBytes = 0 := by
  have bounded := core.retired
  cases beforeStage <;> simp_all [Arrived, CampusTCPTwoProgressReceiver.Stage.bytes]

private theorem head_lower (retired : sent.retiredBytes = 0)
    (selected : CampusTCPTwoProgressRetry.HeadRange sent part head rest) : part = .lower := by
  cases selected with
  | lower => rfl
  | upper =>
    change lower.length = 0 at retired
    exact False.elim (initial.lowerNonempty (List.length_eq_zero_iff.mp retired))

private theorem length_positive (initial : TwoWriteInitial cut sender gateway lower upper) (role : S.Part) :
    0 < (role.bytes lower upper).length := by
  cases role
  · exact List.length_pos_iff.mpr initial.lowerNonempty
  · exact List.length_pos_iff.mpr initial.upperNonempty

theorem head_coverage_strict (selected : CampusTCPTwoProgressRetry.HeadRange sent part head rest)
    (covered : part.offset lower + (part.bytes lower upper).length ≤ (afterStage.bytes lower upper).length) :
    sent.retiredBytes < (afterStage.bytes lower upper).length := by
  have positive := length_positive initial part
  cases selected <;> simp only [CampusTCPTwoProgressSender.Part.offset, CampusTCPTwoProgressSender.Part.bytes,
    CampusTCPTwoProgressSender.Stage.retiredBytes] at * <;> omega

private theorem exists_head (active : Active core) :
    ∃ part head rest, CampusTCPTwoProgressRetry.HeadRange sent part head rest := by
  have preparing := active.preparing
  have nonempty := active.nonempty
  cases sent with
  | written | lower => cases preparing
  | retired => exact False.elim (nonempty rfl)
  | both first second head => exact ⟨.lower, head, [second.entry], .lower first second head⟩
  | tail first second head => exact ⟨.upper, head, [], .upper first second head⟩

private def lower_finish (active : Active core) (path : DataLink initial current .lower monitor.lower)
    (source : CampusTCPTwoProgressReadWriter.SelectedOutput initial current path.served.ticket.value.produced)
    (missing : ¬Arrived beforeStage .lower) (mode : monitor.mode = .originals) (_ack : monitor.ack = none)
    (value : D.Delivered core path afterStage chunk) (arrival : D.Arrival beforeStage .lower afterStage)
    (released : lower.length ≤ (afterStage.bytes lower upper).length)
    (observed : CampusTCPTwoProgressMonitor.observe (config initial native quantum allowance) monitor value.value.delivery.step =
      O.receiptUpdate monitor .lower current.report.final.receipts.length value.value.delivery.localStep.stamp chunk) :
    Active value.next := by
  have retired : sent.retiredBytes = 0 := missing_lower_retired core missing
  have lowerEq := congrArg CampusTCPTwoProgressMonitor.Monitor.lower observed
  have upperEq := congrArg CampusTCPTwoProgressMonitor.Monitor.upper observed
  change (CampusTCPTwoProgressMonitor.observe (config initial native quantum allowance) monitor value.value.delivery.step).upper = monitor.upper at upperEq
  have retryEq := congrArg CampusTCPTwoProgressMonitor.Monitor.retry observed
  change (CampusTCPTwoProgressMonitor.observe (config initial native quantum allowance) monitor value.value.delivery.step).retry = monitor.retry at retryEq
  have ackEq := congrArg CampusTCPTwoProgressMonitor.Monitor.ack observed
  have strict : sent.retiredBytes < (afterStage.bytes lower upper).length := by
    have positive := List.length_pos_iff.mpr initial.lowerNonempty
    omega
  refine {
    mode := ?_, preparing := active.preparing, nonempty := active.nonempty
    recoveryHead := by
      intro recovering
      rw [observed] at recovering
      have impossible : CampusTCPTwoProgressMonitor.Mode.originals = .recovery := mode.symm.trans recovering
      cases impossible
    lowerLane := ?_, upperLane := ?_, retry := ?_, ack := ?_
    originals := ?_, recovery := ?_, serial := ?_, ackNonempty := ?_, waiting := ?_, runnable := ?_, originalOpen := ?_
    debt := ?_, upperMissing := ?_, zeroAck := ?_
    ackGateway := by
      intro lane pending phase
      rw [ackEq] at pending
      have impossible := (congrArg (fun state => state.phase) (Option.some.inj pending)).trans phase
      cases impossible
    sources := active.sources.data path source value.value }
  · rw [observed]
    exact .inl mode
  · rw [lowerEq]
    exact .done rfl
  · rw [upperEq]
    exact retain_original value arrival active.upperLane (by decide)
  · rw [retryEq]
    exact .done (active.originals mode).1
  · unfold AckState
    rw [ackEq]
    exact .pending rfl (receive_pending_queue value)
  · intro _
    rw [observed]
    exact ⟨(active.originals mode).1, rfl, (active.originals mode).2.2⟩
  · intro wrong
    rw [observed] at wrong
    have falseMode : CampusTCPTwoProgressMonitor.Mode.originals = .recovery := mode.symm.trans wrong
    cases falseMode
  · intro _
    rw [observed]
    exact (active.originals mode).1
  · intro _ empty
    rw [empty, CampusTCPTwoProgressReceiver.Stage.bytes] at strict
    exact Nat.not_lt_zero _ strict
  · intro waiting
    rw [observed] at waiting
    cases waiting
  · intro _ _ none
    rw [observed] at none
    cases none
  · intro _ none
    rw [observed] at none
    cases none
  · intro role head rest selected
    have roleEq := head_lower (initial := initial) retired selected
    subst role
    exact ⟨.ack _ (by rw [ackEq]; rfl) (by simpa only [CampusTCPTwoProgressSender.Part.offset,
      CampusTCPTwoProgressSender.Part.bytes, Nat.zero_add] using released)⟩
  · intro noRetirement absent done
    have beforeAbsent : ¬Arrived beforeStage .upper := by
      intro arrived
      cases arrival <;> simp_all [Arrived]
    have beforeDone : monitor.upper.phase = .done := by rw [upperEq] at done; exact done
    obtain ⟨position, cause⟩ := active.upperMissing noRetirement beforeAbsent beforeDone
    exact ⟨position, by rw [value.book]; exact cause⟩
  · intro _ _ equal
    exact False.elim (Nat.ne_of_lt strict equal)

private def upper_finish (active : Active core) (path : DataLink initial current .upper monitor.upper)
    (source : CampusTCPTwoProgressReadWriter.SelectedOutput initial current path.served.ticket.value.produced)
    (mode : monitor.mode = .originals) (ack : monitor.ack = none)
    (value : D.Delivered core path afterStage chunk) (arrival : D.Arrival beforeStage .upper afterStage)
    (shape : (beforeStage = .empty ∧ afterStage = .upperHeld) ∨
      (beforeStage = .lowerReleased ∧ afterStage = .allReleased))
    (observed : CampusTCPTwoProgressMonitor.observe (config initial native quantum allowance) monitor value.value.delivery.step =
      O.receiptUpdate monitor .upper current.report.final.receipts.length value.value.delivery.localStep.stamp chunk) :
    Active value.next := by
  have lowerEq := congrArg CampusTCPTwoProgressMonitor.Monitor.lower observed
  change (CampusTCPTwoProgressMonitor.observe (config initial native quantum allowance) monitor value.value.delivery.step).lower = monitor.lower at lowerEq
  have upperEq := congrArg CampusTCPTwoProgressMonitor.Monitor.upper observed
  have retryEq := congrArg CampusTCPTwoProgressMonitor.Monitor.retry observed
  change (CampusTCPTwoProgressMonitor.observe (config initial native quantum allowance) monitor value.value.delivery.step).retry = monitor.retry at retryEq
  have ackEq := congrArg CampusTCPTwoProgressMonitor.Monitor.ack observed
  have arrived : Arrived afterStage .upper := by rcases shape with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> trivial
  refine {
    mode := ?_, preparing := active.preparing, nonempty := active.nonempty
    recoveryHead := by
      intro recovering
      rw [observed] at recovering
      have impossible : CampusTCPTwoProgressMonitor.Mode.originals = .recovery := mode.symm.trans recovering
      cases impossible
    lowerLane := ?_, upperLane := ?_, retry := ?_, ack := ?_
    originals := ?_, recovery := ?_, serial := ?_, ackNonempty := ?_, waiting := ?_, runnable := ?_, originalOpen := ?_
    debt := ?_, upperMissing := ?_, zeroAck := ?_
    ackGateway := by
      intro lane pending phase
      rw [ackEq] at pending
      have impossible := (congrArg (fun state => state.phase) (Option.some.inj pending)).trans phase
      cases impossible
    sources := active.sources.data path source value.value }
  · rw [observed]
    exact .inl mode
  · rw [lowerEq]
    exact retain_original value arrival active.lowerLane (by decide)
  · rw [upperEq]
    exact .done rfl
  · rw [retryEq]
    exact .done (active.originals mode).1
  · unfold AckState
    rw [ackEq]
    exact .pending rfl (receive_pending_queue value)
  · intro _
    rw [observed]
    exact ⟨(active.originals mode).1, rfl, (active.originals mode).2.2⟩
  · intro wrong
    rw [observed] at wrong
    have falseMode : CampusTCPTwoProgressMonitor.Mode.originals = .recovery := mode.symm.trans wrong
    cases falseMode
  · intro _
    rw [observed]
    exact (active.originals mode).1
  · intro _ empty
    rw [empty] at arrived
    cases arrived
  · intro waiting
    rw [observed] at waiting
    cases waiting
  · intro _ _ none
    rw [observed] at none
    cases none
  · intro _ none
    rw [observed] at none
    cases none
  · intro role head rest selected
    rcases shape with ⟨empty, held⟩ | ⟨prior, released⟩
    · have retired : sent.retiredBytes = 0 := by
        have bounded := core.retired
        rw [empty] at bounded
        change sent.retiredBytes ≤ 0 at bounded
        omega
      have sameRole := head_lower (initial := initial) retired selected
      subst role
      obtain ⟨debt⟩ := active.debt .lower head rest selected
      cases debt with
      | cause position chosen => exact ⟨.cause position (by rw [value.book]; exact chosen)⟩
      | lower _ work => exact ⟨.lower rfl (by rw [lowerEq]; exact retain_work value work (by decide))⟩
      | upper same _ => cases same
      | retry work => exact False.elim (work.not_done (active.originals mode).1)
      | ack old present _ => rw [ack] at present; cases present
    · exact ⟨.ack _ (by rw [ackEq]; rfl) (by
        rw [released]
        cases role <;> simp only [CampusTCPTwoProgressSender.Part.offset, CampusTCPTwoProgressSender.Part.bytes,
          CampusTCPTwoProgressReceiver.Stage.bytes, List.length_append, Nat.zero_add] <;> omega)⟩
  · intro _ missing _
    exact False.elim (missing arrived)
  · intro _ _ equal
    rw [receive_sender_recovery value]
    rcases shape with ⟨empty, _⟩ | ⟨prior, released⟩
    · exact core.emptyDuplicate empty
    · have bounded := core.retired
      rw [prior] at bounded
      rw [released] at equal
      change sent.retiredBytes ≤ lower.length at bounded
      change sent.retiredBytes = (lower ++ upper).length at equal
      have positive := List.length_pos_iff.mpr initial.upperNonempty
      simp only [List.length_append] at equal
      omega

private structure OriginalLink (core : Core initial native quantum allowance current monitor sent beforeStage)
    (part : S.Part) (lane : M.Lane) where
  path : DataLink initial current part lane
  source : CampusTCPTwoProgressReadWriter.SelectedOutput initial current path.served.ticket.value.produced
  covered : (CampusTCPTwoProgressPathsReady.rangeAt core.live.gatewayState part).isSome = true
  missing : ¬Arrived beforeStage part

private def original_link (value : OriginalLane initial native current core.live.gatewayState beforeStage part lane)
    (phase : lane.phase = .dataLink) : OriginalLink core part lane := by
  cases value with
  | done done => rw [done] at phase; cases phase
  | active work missing =>
    cases work with
    | ingress path source => rw [path.phase] at phase; cases phase
    | ticket path source => rw [path.phase] at phase; cases phase
    | link path source covered => exact ⟨path, source, covered, missing⟩

private theorem original_allowed (active : Active core) (mode : monitor.mode = .originals) (ack : monitor.ack = none)
    (event : CampusTCPModel.Event)
    (serves : CampusTCPTwoProgressMonitor.servesOption
        (CampusTCPTwoProgressMonitor.laneDemand (config initial native quantum allowance) current.report.final monitor monitor.lower) event = true ∨
      CampusTCPTwoProgressMonitor.servesOption
        (CampusTCPTwoProgressMonitor.laneDemand (config initial native quantum allowance) current.report.final monitor monitor.upper) event = true)
    (notClock : ∀ actor millis, event ≠ .advanceClock actor millis) :
    CampusTCPTwoProgressMonitor.Allowed (config initial native quantum allowance) current.report.final monitor event := by
  let cfg := config initial native quantum allowance
  change CampusTCPTwoProgressMonitor.servesOption
      (CampusTCPTwoProgressMonitor.laneDemand cfg current.report.final monitor monitor.lower) event = true ∨
    CampusTCPTwoProgressMonitor.servesOption
      (CampusTCPTwoProgressMonitor.laneDemand cfg current.report.final monitor monitor.upper) event = true at serves
  have lower := original_not_send active.lowerLane
  have upper := original_not_send active.upperLane
  have available : ((CampusTCPTwoProgressMonitor.laneDemand cfg current.report.final monitor monitor.lower).isSome ||
      (CampusTCPTwoProgressMonitor.laneDemand cfg current.report.final monitor monitor.upper).isSome) = true := by
    cases first : CampusTCPTwoProgressMonitor.laneDemand cfg current.report.final monitor monitor.lower <;>
      cases second : CampusTCPTwoProgressMonitor.laneDemand cfg current.report.final monitor monitor.upper <;>
      simp_all [CampusTCPTwoProgressMonitor.servesOption]
  apply (CampusTCPTwoProgressMonitorFacts.allowed_iff cfg current.report.final monitor event).mpr
  refine ⟨by rw [mode]; decide, .inl ⟨.originalChoice
    (CampusTCPTwoProgressMonitor.laneDemand cfg current.report.final monitor monitor.lower)
    (CampusTCPTwoProgressMonitor.laneDemand cfg current.report.final monitor monitor.upper), ?_, ?_⟩, ?_⟩
  · simp only [CampusTCPTwoProgressMonitor.nextDemand, mode,
      (CampusTCPTwoProgressMonitorFacts.phase_beq_false _ _).mpr lower,
      (CampusTCPTwoProgressMonitorFacts.phase_beq_false _ _).mpr upper, Bool.false_eq_true, ite_false,
      ack, available, ite_true]
  · exact (CampusTCPTwoProgressMonitorFacts.serves_originalChoice _ _ _).mpr serves
  · cases event <;> try rfl
    exact False.elim (notClock _ _ rfl)

private theorem lane_deliver_eq (cfg : CampusTCPTwoProgressMonitor.Config) (state : State input)
    (monitor : M.Monitor) (lane : M.Lane) (action : CampusTCPRoundMonitor.Action)
    (next : CampusTCPGapProgressMonitor.nextAction cfg.toConfig state lane.toGap = some action)
    (served : CampusTCPTwoProgressMonitor.servesOption (CampusTCPTwoProgressMonitor.laneDemand cfg state monitor lane)
      (.deliver index bytes true) = true) : (.deliver index bytes true : CampusTCPModel.Event) = action.event := by
  apply (CampusTCPGapProgressMonitorFacts.actionOf_iff _ _).mp
  cases packet : CampusTCPGapProgressMonitor.packetAt lane.toGap <;>
    by_cases budget : monitor.drops.length < cfg.lossAllowance <;>
    simpa [CampusTCPTwoProgressMonitor.laneDemand, next, packet, budget,
      CampusTCPTwoProgressMonitor.servesOption, CampusTCPGapProgressMonitor.serves] using served

private theorem upper_not_lower (active : Active core) (path : DataLink initial current .upper monitor.upper) :
    CampusTCPTwoProgressMonitor.servesOption
      (CampusTCPTwoProgressMonitor.laneDemand (config initial native quantum allowance) current.report.final monitor monitor.lower)
      (.deliver path.index path.emission.bytes true) = false := by
  apply Bool.eq_false_iff.mpr
  intro served
  cases active.lowerLane with
  | done phase =>
    simp [CampusTCPTwoProgressMonitor.laneDemand, CampusTCPGapProgressMonitor.nextAction,
      CampusTCPTwoProgressMonitor.Lane.toGap, phase, CampusTCPTwoProgressMonitor.servesOption] at served
  | active work _ =>
    cases work with
    | ingress waiting source =>
      have event := lane_deliver_eq _ _ _ _ _ (waiting.action (config initial native quantum allowance)) served
      cases event
    | ticket waiting source =>
      have event := lane_deliver_eq _ _ _ _ _ (waiting.action (config initial native quantum allowance)) served
      cases event
    | link waiting source covered =>
      have event := lane_deliver_eq _ _ _ _ _ (waiting.action (config initial native quantum allowance)) served
      exact Distinct.service_index_ne waiting path (CampusTCPModel.Event.deliver.inj event).1.symm

structure Received (core : Core initial native quantum allowance current monitor sent beforeStage)
    (part : S.Part) (target : CampusTCPTwoProgressMonitor.DropTarget) where
  path : DataLink initial current part (O.dataLaneAt monitor target)
  afterStage : R.Stage
  chunk : List UInt8
  value : D.Delivered core path afterStage chunk
  observed : CampusTCPTwoProgressMonitor.observe (config initial native quantum allowance) monitor value.value.delivery.step =
    O.receiptUpdate monitor target current.report.final.receipts.length value.value.delivery.localStep.stamp chunk
  active : Active value.next

theorem lower_at (active : Active core) (mode : monitor.mode = .originals) (ack : monitor.ack = none)
    (phase : monitor.lower.phase = .dataLink) : Nonempty (Received core .lower .lower) := by
  let selected := original_link active.lowerLane phase
  have serves := CampusTCPTwoProgressPhaseObserve.laneDemand_serves (config initial native quantum allowance)
    current.report.final monitor monitor.lower _ (selected.path.action (config initial native quantum allowance))
  have allowed := original_allowed active mode ack (.deliver selected.path.index selected.path.emission.bytes true)
    (.inl serves) (by intro actor millis equal; cases equal)
  have first := original_not_send active.lowerLane
  have second := original_not_send active.upperLane
  cases beforeStage with
  | empty =>
    obtain ⟨value⟩ := CampusTCPTwoProgressPhaseReceive.lower_at core selected.path selected.covered
    have observed := CampusTCPTwoProgressPhaseObserveReceive.receipt_lower value mode first second ack allowed
    exact ⟨⟨selected.path, .lowerReleased, lower, value, observed,
      lower_finish active selected.path selected.source selected.missing mode ack value .lower (Nat.le_refl _) observed⟩⟩
  | upperHeld =>
    obtain ⟨value⟩ := CampusTCPTwoProgressPhaseReceive.gap_at core selected.path selected.covered
    have observed := CampusTCPTwoProgressPhaseObserveReceive.receipt_lower value mode first second ack allowed
    exact ⟨⟨selected.path, .allReleased, lower ++ upper, value, observed,
      lower_finish active selected.path selected.source selected.missing mode ack value .gap
        (by simp only [CampusTCPTwoProgressReceiver.Stage.bytes, List.length_append]; omega) observed⟩⟩
  | lowerReleased | allReleased => exact False.elim (selected.missing trivial)

theorem upper_at (active : Active core) (mode : monitor.mode = .originals) (ack : monitor.ack = none)
    (phase : monitor.upper.phase = .dataLink) : Nonempty (Received core .upper .upper) := by
  let selected := original_link active.upperLane phase
  have serves := CampusTCPTwoProgressPhaseObserve.laneDemand_serves (config initial native quantum allowance)
    current.report.final monitor monitor.upper _ (selected.path.action (config initial native quantum allowance))
  have allowed := original_allowed active mode ack (.deliver selected.path.index selected.path.emission.bytes true)
    (.inr serves) (by intro actor millis equal; cases equal)
  have first := original_not_send active.lowerLane
  have second := original_not_send active.upperLane
  have other := upper_not_lower active selected.path
  cases beforeStage with
  | empty =>
    obtain ⟨value⟩ := CampusTCPTwoProgressPhaseReceive.hold_at core selected.path selected.covered
    have observed := CampusTCPTwoProgressPhaseObserveReceive.receipt_upper value mode first second ack
      (by rw [value.value.delivery.beforeEq, value.value.delivery.event]; exact other) allowed
    exact ⟨⟨selected.path, .upperHeld, [], value, observed,
      upper_finish active selected.path selected.source mode ack value .hold (.inl ⟨rfl, rfl⟩) observed⟩⟩
  | lowerReleased =>
    obtain ⟨value⟩ := CampusTCPTwoProgressPhaseReceive.upper_at core selected.path selected.covered
    have observed := CampusTCPTwoProgressPhaseObserveReceive.receipt_upper value mode first second ack
      (by rw [value.value.delivery.beforeEq, value.value.delivery.event]; exact other) allowed
    exact ⟨⟨selected.path, .allReleased, upper, value, observed,
      upper_finish active selected.path selected.source mode ack value .upper (.inr ⟨rfl, rfl⟩) observed⟩⟩
  | upperHeld | allReleased => exact False.elim (selected.missing trivial)

end Netlib.Check.CampusTCPTwoProgressPhaseReceiveState
