import Netlib.Check.CampusTCPTwoTransferLocatedDataReceive
import Netlib.Check.CampusTCPTwoTransferPhaseState
import Netlib.Check.CampusTCPTwoProgressPathsDistinct

/-!
# Current forward phases after the actual data receipt

The selected data lane ends and creates one real pending ACK lane.
Actual writer sources, unselected paths, and loss causes remain on the same suffix.
-/

namespace Netlib.Check.CampusTCPTwoTransferDataReceiveProgress

open Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart
open CampusTCPTwoTransferNative (Checks Routing)
open CampusTCPTwoTransferLocatedCore (Core config)
open CampusTCPTwoTransferPhaseState (Active Debt)
open CampusTCPTwoTransferWork (Work DataWork OriginalLane RetryLane AckWork AckState)
open CampusTCPTwoTransferPaths (DataLink DataIngress)
open CampusTCPTwoTransferAdmission (rangeAt)
open CampusTCPTwoProgressPhaseBase (Arrived)

namespace M
export CampusTCPTwoProgressMonitor (Lane)
end M
namespace W
export CampusTCPTwoTransferMonitor (Monitor observe)
end W
namespace S
export CampusTCPTwoProgressSender (Stage Part)
end S
namespace R
export CampusTCPTwoProgressReceiver (Stage)
end R
namespace N
export CampusTCPTwoTransferLocatedDataReceive (Received Dispatch lower_at hold_at upper_at gap_at old_at)
end N
namespace D
export CampusTCPTwoProgressPhaseReceive (Arrival)
end D
namespace O
export CampusTCPTwoProgressPhaseObserveReceive (dataLaneAt receiptUpdate receiptLane)
end O
namespace Distinct
export CampusTCPTwoProgressPathsDistinct (service_index_ne ingress_link_packet_ne link_ingress_packet_ne link_packet_ne)
end Distinct

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current : Cut input complete} {sender : Actor} {gateway location : Gateway} {lower upper chunk : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {checks : Checks cut initial.gatewayState.session.entry} {routing : Routing cut gateway}
variable {quantum allowance : Nat} {reverseLower reverseUpper : List UInt8}
variable {monitor : W.Monitor} {sent : S.Stage initial} {beforeStage afterStage : R.Stage}
variable {core : Core initial checks routing quantum allowance reverseLower reverseUpper current monitor location sent beforeStage}
variable {head : Recovery.Outstanding} {rest : List Recovery.Outstanding}
variable {part other : S.Part} {lane otherLane : M.Lane} {target : CampusTCPTwoProgressMonitor.DropTarget}

local notation "cfg" => config initial checks routing quantum allowance reverseLower reverseUpper

private theorem original_not_send (value : OriginalLane initial checks current view beforeStage part lane) :
    lane.phase ≠ .needSend := by
  cases value with
  | done phase => rw [phase]; decide
  | active work _ =>
    cases work with
    | ingress path _ => rw [path.phase]; decide
    | ticket path _ => rw [path.phase]; decide
    | link path _ _ => rw [path.phase]; decide

theorem receive_sender_recovery {path : DataLink initial current part lane}
    (value : N.Received core path target afterStage chunk) :
    value.next.live.senderFlight.recovery = core.live.senderFlight.recovery := value.sender_recovery

private theorem range_same {path : DataLink initial current part lane}
    (value : N.Received core path target afterStage chunk) (role : S.Part) :
    rangeAt value.next.live.gatewayState role = rangeAt core.live.gatewayState role := by
  rw [value.gateway]
  cases role <;> rfl

private theorem consumed {path : DataLink initial current part lane} (value : N.Received core path target afterStage chunk) :
    CampusTCPTwoProgressPathRetain.consumedPacket current.report.final value.value.value.delivery.step.event = some path.packetID := by
  rw [value.value.value.delivery.event]
  exact path.custody

private theorem different_packets {path : DataLink initial current part lane}
    (value : N.Received core path target afterStage chunk) (id : Nat) (different : path.packetID ≠ id) :
    CampusTCPTwoProgressPathRetain.consumedPacket current.report.final value.value.value.delivery.step.event ≠ some id := by
  rw [consumed value]
  exact fun same => different (Option.some.inj same)

private def retain_work {path : DataLink initial current part lane}
    (value : N.Received core path target afterStage chunk) (work : Work initial checks current location other otherLane)
    (different : part ≠ other) : Work initial checks value.value.value.move.after location other otherLane := by
  cases part <;> cases other
  all_goals try exact False.elim (different rfl)
  case lower.upper =>
    cases work with
    | ingress waiting => exact .ingress (waiting.after_move value.value.value.move
        (different_packets value _ (Distinct.link_ingress_packet_ne path waiting)))
    | ticket waiting selected => exact .ticket (waiting.after_quiet value.value.value.move (by rw [value.value.value.delivery.event]; trivial)) selected
    | link waiting => exact .link (waiting.after_move value.value.value.move
        (different_packets value _ (Distinct.link_packet_ne path waiting)))
  case upper.lower =>
    cases work with
    | ingress waiting => exact .ingress (waiting.after_move value.value.value.move
        (different_packets value _ (Ne.symm (Distinct.ingress_link_packet_ne waiting path))))
    | ticket waiting selected => exact .ticket (waiting.after_quiet value.value.value.move (by rw [value.value.value.delivery.event]; trivial)) selected
    | link waiting => exact .link (waiting.after_move value.value.value.move
        (different_packets value _ (Ne.symm (Distinct.link_packet_ne waiting path))))

private def retain_data {path : DataLink initial current part lane}
    (value : N.Received core path target afterStage chunk)
    (work : DataWork initial checks current core.live.gatewayState other otherLane) (different : part ≠ other) :
    DataWork initial checks value.value.value.move.after value.next.live.gatewayState other otherLane := by
  cases part <;> cases other
  all_goals try exact False.elim (different rfl)
  case lower.upper =>
    cases work with
    | ingress waiting source =>
      exact .ingress (waiting.after_move value.value.value.move
        (different_packets value _ (Distinct.link_ingress_packet_ne path waiting))) (source.retain_steps value.value.value.move.retained)
    | ticket waiting selected source =>
      exact .ticket (waiting.after_quiet value.value.value.move (by rw [value.value.value.delivery.event]; trivial)) selected
        (source.retain_steps value.value.value.move.retained)
    | link waiting source covered =>
      exact .link (waiting.after_move value.value.value.move
        (different_packets value _ (Distinct.link_packet_ne path waiting))) (source.retain_steps value.value.value.move.retained)
        (by rw [range_same value]; exact covered)
  case upper.lower =>
    cases work with
    | ingress waiting source =>
      exact .ingress (waiting.after_move value.value.value.move
        (different_packets value _ (Ne.symm (Distinct.ingress_link_packet_ne waiting path)))) (source.retain_steps value.value.value.move.retained)
    | ticket waiting selected source =>
      exact .ticket (waiting.after_quiet value.value.value.move (by rw [value.value.value.delivery.event]; trivial)) selected
        (source.retain_steps value.value.value.move.retained)
    | link waiting source covered =>
      exact .link (waiting.after_move value.value.value.move
        (different_packets value _ (Ne.symm (Distinct.link_packet_ne waiting path)))) (source.retain_steps value.value.value.move.retained)
        (by rw [range_same value]; exact covered)

private theorem arrived_other (arrival : D.Arrival beforeStage part afterStage) (different : part ≠ other) :
    Arrived afterStage other → Arrived beforeStage other := by
  cases arrival <;> cases other <;> simp_all [Arrived]

private def retain_original {path : DataLink initial current part lane}
    (value : N.Received core path target afterStage chunk) (arrival : D.Arrival beforeStage part afterStage)
    (old : OriginalLane initial checks current core.live.gatewayState beforeStage other otherLane)
    (different : part ≠ other) :
    OriginalLane initial checks value.value.value.move.after value.next.live.gatewayState afterStage other otherLane := by
  cases old with
  | done phase => exact .done phase
  | active work missing => exact .active (retain_data value work different) (fun arrived => missing (arrived_other arrival different arrived))

theorem receive_pending_queue {path : DataLink initial current part lane}
    (value : N.Received core path target afterStage chunk) : value.next.live.receiverFacts.reaction.work.pending ≠ [] := value.pending

private theorem missing_lower_retired (core : Core initial checks routing quantum allowance reverseLower reverseUpper current monitor location sent beforeStage)
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

private def lower_finish (active : Active core) (path : DataLink initial current .lower monitor.exchange.forward.lower)
    (source : CampusTCPTwoProgressReadWriter.SelectedOutput initial current path.served.ticket.value.produced)
    (missing : ¬Arrived beforeStage .lower) (mode : monitor.exchange.forward.mode = .originals) (_ack : monitor.exchange.forward.ack = none)
    (value : N.Received core path .lower afterStage chunk) (arrival : D.Arrival beforeStage .lower afterStage)
    (released : lower.length ≤ (afterStage.bytes lower upper).length)
    (observed : (W.observe cfg monitor value.value.value.delivery.step).exchange.forward =
      O.receiptUpdate monitor.exchange.forward .lower current.report.final.receipts.length value.value.value.delivery.localStep.stamp chunk) :
    Active value.next := by
  have retired : sent.retiredBytes = 0 := missing_lower_retired core missing
  have lowerEq := congrArg CampusTCPTwoProgressMonitor.Monitor.lower observed
  have upperEq := congrArg CampusTCPTwoProgressMonitor.Monitor.upper observed
  change ((W.observe cfg monitor value.value.value.delivery.step).exchange.forward).upper = monitor.exchange.forward.upper at upperEq
  have retryEq := congrArg CampusTCPTwoProgressMonitor.Monitor.retry observed
  change ((W.observe cfg monitor value.value.value.delivery.step).exchange.forward).retry = monitor.exchange.forward.retry at retryEq
  have ackEq := congrArg CampusTCPTwoProgressMonitor.Monitor.ack observed
  have strict : sent.retiredBytes < (afterStage.bytes lower upper).length := by
    have positive := List.length_pos_iff.mpr initial.lowerNonempty
    omega
  refine {
    exchange := by rw [value.observed]; exact active.exchange
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
    sources := active.sources.data path source value.value.value }
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
    exact ⟨.ack _ (by rw [ackEq]; rfl) (.pending rfl value.pending) (by simpa only [CampusTCPTwoProgressSender.Part.offset,
      CampusTCPTwoProgressSender.Part.bytes, Nat.zero_add] using released)⟩
  · intro noRetirement absent done
    have beforeAbsent : ¬Arrived beforeStage .upper := by
      intro arrived
      cases arrival <;> simp_all [Arrived]
    have beforeDone : monitor.exchange.forward.upper.phase = .done := by rw [upperEq] at done; exact done
    obtain ⟨position, cause⟩ := active.upperMissing noRetirement beforeAbsent beforeDone
    exact ⟨position, by rw [value.book]; exact cause⟩
  · intro _ _ equal
    exact False.elim (Nat.ne_of_lt strict equal)

private def upper_finish (active : Active core) (path : DataLink initial current .upper monitor.exchange.forward.upper)
    (source : CampusTCPTwoProgressReadWriter.SelectedOutput initial current path.served.ticket.value.produced)
    (mode : monitor.exchange.forward.mode = .originals) (ack : monitor.exchange.forward.ack = none)
    (value : N.Received core path .upper afterStage chunk) (arrival : D.Arrival beforeStage .upper afterStage)
    (shape : (beforeStage = .empty ∧ afterStage = .upperHeld) ∨
      (beforeStage = .lowerReleased ∧ afterStage = .allReleased))
    (observed : (W.observe cfg monitor value.value.value.delivery.step).exchange.forward =
      O.receiptUpdate monitor.exchange.forward .upper current.report.final.receipts.length value.value.value.delivery.localStep.stamp chunk) :
    Active value.next := by
  have lowerEq := congrArg CampusTCPTwoProgressMonitor.Monitor.lower observed
  change ((W.observe cfg monitor value.value.value.delivery.step).exchange.forward).lower = monitor.exchange.forward.lower at lowerEq
  have upperEq := congrArg CampusTCPTwoProgressMonitor.Monitor.upper observed
  have retryEq := congrArg CampusTCPTwoProgressMonitor.Monitor.retry observed
  change ((W.observe cfg monitor value.value.value.delivery.step).exchange.forward).retry = monitor.exchange.forward.retry at retryEq
  have ackEq := congrArg CampusTCPTwoProgressMonitor.Monitor.ack observed
  have arrived : Arrived afterStage .upper := by rcases shape with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> trivial
  refine {
    exchange := by rw [value.observed]; exact active.exchange
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
    sources := active.sources.data path source value.value.value }
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
      | ack old present _ _ => rw [ack] at present; cases present
    · exact ⟨.ack _ (by rw [ackEq]; rfl) (.pending rfl value.pending) (by
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


private theorem head_part (first : CampusTCPTwoProgressRetry.HeadRange sent part head rest)
    (second : CampusTCPTwoProgressRetry.HeadRange sent other otherHead otherRest) : other = part := by
  cases first <;> cases second <;> rfl

private def retry_finish (active : Active core) (path : DataLink initial current part monitor.exchange.forward.retry)
    (source : CampusTCPTwoProgressReadWriter.SelectedOutput initial current path.served.ticket.value.produced)
    (selected : CampusTCPTwoProgressRetry.HeadRange sent part head rest) (mode : monitor.exchange.forward.mode = .recovery)
    (value : N.Received core path .retry afterStage chunk) (arrival : D.Arrival beforeStage part afterStage)
    (covered : part.offset lower + (part.bytes lower upper).length ≤ (afterStage.bytes lower upper).length)
    (observed : (W.observe cfg monitor value.value.value.delivery.step).exchange.forward =
      O.receiptUpdate monitor.exchange.forward .retry current.report.final.receipts.length value.value.value.delivery.localStep.stamp chunk) :
    Active value.next := by
  have lowerEq := congrArg CampusTCPTwoProgressMonitor.Monitor.lower observed
  change ((W.observe cfg monitor value.value.value.delivery.step).exchange.forward).lower = monitor.exchange.forward.lower at lowerEq
  have upperEq := congrArg CampusTCPTwoProgressMonitor.Monitor.upper observed
  change ((W.observe cfg monitor value.value.value.delivery.step).exchange.forward).upper = monitor.exchange.forward.upper at upperEq
  have retryEq := congrArg CampusTCPTwoProgressMonitor.Monitor.retry observed
  have ackEq := congrArg CampusTCPTwoProgressMonitor.Monitor.ack observed
  have strict := head_coverage_strict selected covered
  refine {
    exchange := by rw [value.observed]; exact active.exchange
    mode := ?_, preparing := active.preparing, nonempty := active.nonempty
    recoveryHead := by
      intro _ _ role currentHead currentRest current
      have oldWaiting : monitor.exchange.forward.waiting = false := by
        cases waiting : monitor.exchange.forward.waiting with
        | false => rfl
        | true =>
          have done := (active.waiting waiting).2
          have impossible := path.phase.symm.trans done
          cases impossible
      exact active.recoveryHead mode oldWaiting role currentHead currentRest current
    lowerLane := ?_, upperLane := ?_, retry := ?_, ack := ?_
    originals := ?_, recovery := ?_, serial := ?_, ackNonempty := ?_, waiting := ?_, runnable := ?_, originalOpen := ?_
    debt := ?_, upperMissing := ?_, zeroAck := ?_
    ackGateway := by
      intro lane pending phase
      rw [ackEq] at pending
      have impossible := (congrArg (fun state => state.phase) (Option.some.inj pending)).trans phase
      cases impossible
    sources := active.sources.data path source value.value.value }
  · rw [observed]
    exact .inr mode
  · rw [lowerEq]
    exact .done (active.recovery mode).1
  · rw [upperEq]
    exact .done (active.recovery mode).2
  · rw [retryEq]
    exact .done rfl
  · unfold AckState
    rw [ackEq]
    exact .pending rfl (receive_pending_queue value)
  · intro wrong
    rw [observed] at wrong
    have impossible : CampusTCPTwoProgressMonitor.Mode.recovery = .originals := mode.symm.trans wrong
    cases impossible
  · intro _
    rw [observed]
    exact active.recovery mode
  · intro _
    rw [observed]
    rfl
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
  · intro role currentHead currentRest current
    have same := head_part selected current
    subst role
    exact ⟨.ack _ (by rw [ackEq]; rfl) (.pending rfl value.pending) covered⟩
  · intro noRetirement absent done
    cases part with
    | lower =>
      have beforeAbsent : ¬Arrived beforeStage .upper := by
        intro arrived
        cases arrival <;> simp_all [Arrived]
      obtain ⟨position, cause⟩ := active.upperMissing noRetirement beforeAbsent (active.recovery mode).2
      exact ⟨position, by rw [value.book]; exact cause⟩
    | upper =>
      have positive := List.length_pos_iff.mpr initial.upperNonempty
      cases afterStage <;> simp_all [Arrived, CampusTCPTwoProgressReceiver.Stage.bytes,
        CampusTCPTwoProgressSender.Part.offset, CampusTCPTwoProgressSender.Part.bytes, List.length_append]
      all_goals omega
  · intro _ _ equal
    exact False.elim (Nat.ne_of_lt strict equal)


private def link_source (work : DataWork initial checks current core.live.gatewayState part lane)
    (path : DataLink initial current part lane) :
    CampusTCPTwoProgressReadWriter.SelectedOutput initial current path.served.ticket.value.produced := by
  cases work with
  | ingress stored _ => have impossible := stored.phase.symm.trans path.phase; cases impossible
  | ticket stored _ _ => have impossible := stored.phase.symm.trans path.phase; cases impossible
  | link stored source _ =>
    have index : stored.index = path.index := Option.some.inj (stored.serviceRef.symm.trans path.serviceRef)
    have present := stored.stored
    rw [index] at present
    exact source.reindex (congrArg (fun served => served.ticket.value.produced) (Option.some.inj (present.symm.trans path.stored)))

private theorem link_known (work : DataWork initial checks current core.live.gatewayState part lane)
    (path : DataLink initial current part lane) : (rangeAt core.live.gatewayState part).isSome = true := by
  cases work with
  | ingress stored _ => have impossible := stored.phase.symm.trans path.phase; cases impossible
  | ticket stored _ _ => have impossible := stored.phase.symm.trans path.phase; cases impossible
  | link _ _ known => exact known

private theorem link_missing (work : OriginalLane initial checks current core.live.gatewayState beforeStage part lane)
    (path : DataLink initial current part lane) : ¬Arrived beforeStage part := by
  cases work with
  | active _ missing => exact missing
  | done done => rw [path.phase] at done; cases done

private theorem lane_deliver_eq (localConfig : CampusTCPTwoProgressMonitor.Config) (state : State input)
    (localMonitor : CampusTCPTwoProgressMonitor.Monitor) (lane : M.Lane) (action : CampusTCPRoundMonitor.Action)
    (next : CampusTCPGapProgressMonitor.nextAction localConfig.toConfig state lane.toGap = some action)
    (served : CampusTCPTwoProgressMonitor.servesOption (CampusTCPTwoProgressMonitor.laneDemand localConfig state localMonitor lane)
      (.deliver index bytes true) = true) : (.deliver index bytes true : CampusTCPModel.Event) = action.event := by
  apply (CampusTCPGapProgressMonitorFacts.actionOf_iff _ _).mp
  cases packet : CampusTCPGapProgressMonitor.packetAt lane.toGap <;>
    by_cases budget : localMonitor.drops.length < localConfig.lossAllowance <;>
    simpa [CampusTCPTwoProgressMonitor.laneDemand, next, packet, budget,
      CampusTCPTwoProgressMonitor.servesOption, CampusTCPGapProgressMonitor.serves] using served

private theorem upper_not_lower (active : Active core) (path : DataLink initial current .upper monitor.exchange.forward.upper) :
    CampusTCPTwoProgressMonitor.servesOption
      (CampusTCPTwoProgressMonitor.laneDemand ((cfg).at current.report.final).forward current.report.final monitor.exchange.forward monitor.exchange.forward.lower)
      (.deliver path.index path.emission.bytes true) = false := by
  apply Bool.eq_false_iff.mpr
  intro served
  cases active.lowerLane with
  | done phase =>
    simp [CampusTCPTwoProgressMonitor.laneDemand, CampusTCPGapProgressMonitor.nextAction,
      CampusTCPTwoProgressMonitor.Lane.toGap, phase, CampusTCPTwoProgressMonitor.servesOption] at served
  | active work _ =>
    cases work with
    | ingress waiting _ =>
      have event := lane_deliver_eq _ _ _ _ _ (waiting.action ((cfg).at current.report.final).forward) served
      cases event
    | ticket waiting _ _ =>
      have event := lane_deliver_eq _ _ _ _ _ (waiting.action ((cfg).at current.report.final).forward) served
      cases event
    | link waiting _ _ =>
      have event := lane_deliver_eq _ _ _ _ _ (waiting.action ((cfg).at current.report.final).forward) served
      exact Distinct.service_index_ne waiting path (CampusTCPModel.Event.deliver.inj event).1.symm

structure Result (core : Core initial checks routing quantum allowance reverseLower reverseUpper current monitor location sent beforeStage)
    (path : DataLink initial current part lane) (target : CampusTCPTwoProgressMonitor.DropTarget) where
  stage : R.Stage
  chunk : List UInt8
  value : N.Received core path target stage chunk
  active : Active value.next

theorem lower_at (active : Active core) (path : DataLink initial current .lower monitor.exchange.forward.lower)
    (mode : monitor.exchange.forward.mode = .originals) (ack : monitor.exchange.forward.ack = none)
    (allowed : CampusTCPTwoTransferMonitor.Allowed cfg current.report.final monitor (.deliver path.index path.emission.bytes true)) :
    Nonempty (Result core path .lower) := by
  let work := active.lowerLane.dataWork (by rw [path.phase]; decide)
  let source := link_source work path
  have known := link_known work path
  have missing := link_missing active.lowerLane path
  have dispatch : N.Dispatch cfg current.report.final monitor monitor.exchange.forward.lower .lower :=
    .lower active.exchange mode active.lower_not_needSend active.upper_not_needSend ack
  cases beforeStage with
  | empty =>
    obtain ⟨value⟩ := N.lower_at core path dispatch known allowed
    exact ⟨⟨.lowerReleased, lower, value, lower_finish active path source missing mode ack value .lower
      (Nat.le_refl _) (congrArg (fun whole : W.Monitor => whole.exchange.forward) value.observed)⟩⟩
  | upperHeld =>
    obtain ⟨value⟩ := N.gap_at core path dispatch known allowed
    exact ⟨⟨.allReleased, lower ++ upper, value, lower_finish active path source missing mode ack value .gap
      (by simp only [CampusTCPTwoProgressReceiver.Stage.bytes, List.length_append]; omega)
      (congrArg (fun whole : W.Monitor => whole.exchange.forward) value.observed)⟩⟩
  | lowerReleased | allReleased => exact False.elim (missing trivial)

theorem upper_at (active : Active core) (path : DataLink initial current .upper monitor.exchange.forward.upper)
    (mode : monitor.exchange.forward.mode = .originals) (ack : monitor.exchange.forward.ack = none)
    (allowed : CampusTCPTwoTransferMonitor.Allowed cfg current.report.final monitor (.deliver path.index path.emission.bytes true)) :
    Nonempty (Result core path .upper) := by
  let work := active.upperLane.dataWork (by rw [path.phase]; decide)
  let source := link_source work path
  have known := link_known work path
  have missing := link_missing active.upperLane path
  have dispatch : N.Dispatch cfg current.report.final monitor monitor.exchange.forward.upper .upper :=
    .upper active.exchange mode active.lower_not_needSend active.upper_not_needSend ack (by
      intro index bytes next
      have same := congrArg CampusTCPRoundMonitor.Action.event (Option.some.inj ((path.action _).symm.trans next))
      change Event.deliver path.index path.emission.bytes true = .deliver index bytes true at same
      rw [← same]
      exact upper_not_lower active path)
  cases beforeStage with
  | empty =>
    obtain ⟨value⟩ := N.hold_at core path dispatch known allowed
    exact ⟨⟨.upperHeld, [], value, upper_finish active path source mode ack value .hold (.inl ⟨rfl, rfl⟩)
      (congrArg (fun whole : W.Monitor => whole.exchange.forward) value.observed)⟩⟩
  | lowerReleased =>
    obtain ⟨value⟩ := N.upper_at core path dispatch known allowed
    exact ⟨⟨.allReleased, upper, value, upper_finish active path source mode ack value .upper (.inr ⟨rfl, rfl⟩)
      (congrArg (fun whole : W.Monitor => whole.exchange.forward) value.observed)⟩⟩
  | upperHeld | allReleased => exact False.elim (missing trivial)

theorem retry_at (active : Active core) (path : DataLink initial current part monitor.exchange.forward.retry)
    (selected : CampusTCPTwoProgressRetry.HeadRange sent part head rest)
    (mode : monitor.exchange.forward.mode = .recovery) (ack : monitor.exchange.forward.ack = none)
    (waiting : monitor.exchange.forward.waiting = false)
    (allowed : CampusTCPTwoTransferMonitor.Allowed cfg current.report.final monitor (.deliver path.index path.emission.bytes true)) :
    Nonempty (Result core path .retry) := by
  let work : DataWork initial checks current core.live.gatewayState part monitor.exchange.forward.retry := by
    cases active.retry with
    | active role otherHead otherRest current work =>
      have same := head_part selected current
      subst role
      exact work
    | done done => rw [path.phase] at done; cases done
  let source := link_source work path
  have known := link_known work path
  have dispatch : N.Dispatch cfg current.report.final monitor monitor.exchange.forward.retry .retry :=
    .retry active.exchange mode ack waiting
  cases selected with
  | lower first second head =>
    cases beforeStage with
    | empty =>
      obtain ⟨value⟩ := N.lower_at core path dispatch known allowed
      exact ⟨⟨.lowerReleased, lower, value, retry_finish active path source (.lower first second head) mode value .lower
        (by change 0 + lower.length ≤ lower.length; omega)
        (congrArg (fun whole : W.Monitor => whole.exchange.forward) value.observed)⟩⟩
    | upperHeld =>
      obtain ⟨value⟩ := N.gap_at core path dispatch known allowed
      exact ⟨⟨.allReleased, lower ++ upper, value, retry_finish active path source (.lower first second head) mode value .gap
        (by change 0 + lower.length ≤ (lower ++ upper).length; simp only [List.length_append]; omega)
        (congrArg (fun whole : W.Monitor => whole.exchange.forward) value.observed)⟩⟩
    | lowerReleased =>
      obtain ⟨value⟩ := N.old_at core path dispatch known (by change 0 + lower.length ≤ lower.length; omega) allowed
      exact ⟨⟨.lowerReleased, [], value, retry_finish active path source (.lower first second head) mode value (.old _ _)
        (by change 0 + lower.length ≤ lower.length; omega)
        (congrArg (fun whole : W.Monitor => whole.exchange.forward) value.observed)⟩⟩
    | allReleased =>
      obtain ⟨value⟩ := N.old_at core path dispatch known (by change 0 + lower.length ≤ (lower ++ upper).length; simp only [List.length_append]; omega) allowed
      exact ⟨⟨.allReleased, [], value, retry_finish active path source (.lower first second head) mode value (.old _ _)
        (by change 0 + lower.length ≤ (lower ++ upper).length; simp only [List.length_append]; omega)
        (congrArg (fun whole : W.Monitor => whole.exchange.forward) value.observed)⟩⟩
  | upper first second head =>
    have bounded := core.retired
    have positive := List.length_pos_iff.mpr initial.lowerNonempty
    cases beforeStage with
    | empty | upperHeld => change lower.length ≤ 0 at bounded; omega
    | lowerReleased =>
      obtain ⟨value⟩ := N.upper_at core path dispatch known allowed
      exact ⟨⟨.allReleased, upper, value, retry_finish active path source (.upper first second head) mode value .upper
        (by change lower.length + upper.length ≤ (lower ++ upper).length; simp only [List.length_append, Nat.le_refl])
        (congrArg (fun whole : W.Monitor => whole.exchange.forward) value.observed)⟩⟩
    | allReleased =>
      obtain ⟨value⟩ := N.old_at core path dispatch known (by change lower.length + upper.length ≤ (lower ++ upper).length; simp only [List.length_append, Nat.le_refl]) allowed
      exact ⟨⟨.allReleased, [], value, retry_finish active path source (.upper first second head) mode value (.old _ _)
        (by change lower.length + upper.length ≤ (lower ++ upper).length; simp only [List.length_append, Nat.le_refl])
        (congrArg (fun whole : W.Monitor => whole.exchange.forward) value.observed)⟩⟩

end Netlib.Check.CampusTCPTwoTransferDataReceiveProgress
