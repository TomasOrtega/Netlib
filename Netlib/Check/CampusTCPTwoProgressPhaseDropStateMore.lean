import Netlib.Check.CampusTCPTwoProgressPhaseDropState

namespace Netlib.Check.CampusTCPTwoProgressPhaseDropState

open Protocol Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart CampusTCPTwoProgressPhaseBase
open CampusTCPTwoProgressPhaseState CampusTCPTwoProgressPaths
open CampusTCPTwoProgressSetup (config)

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current : Cut input complete} {sender : Actor} {gateway : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {native : NativeEnv cut gateway initial.gatewayState.session.entry} {quantum allowance : Nat}
variable {monitor : M.Monitor} {sent : S.Stage initial} {received : R.Stage} {actual : Step input}
variable {core : Core initial native quantum allowance current monitor sent received}
variable {produced : Produced input.active input.passive} {packetID : Nat} {part : S.Part} {lane : M.Lane}
variable {head : Recovery.Outstanding} {rest : List Recovery.Outstanding}

private theorem retry_mode (active : Active core) (live : monitor.retry.phase ≠ .done) : monitor.mode = .recovery := by
  rcases active.mode with mode | mode
  · exact False.elim (live (active.originals mode).1)
  · exact mode

private theorem retry_ack (active : Active core) (live : monitor.retry.phase ≠ .done) : monitor.ack = none := by
  cases found : monitor.ack with
  | none => rfl
  | some lane => exact False.elim (live (active.serial (by rw [found]; rfl)))

private theorem retry_waiting (active : Active core) (live : monitor.retry.phase ≠ .done) : monitor.waiting = false := by
  cases waiting : monitor.waiting with
  | false => rfl
  | true => exact False.elim (live (active.waiting waiting).2)

private theorem role_eq {other : S.Part} {otherHead : Recovery.Outstanding} {otherRest : List Recovery.Outstanding}
    (first : CampusTCPTwoProgressRetry.HeadRange sent part head rest)
    (second : CampusTCPTwoProgressRetry.HeadRange sent other otherHead otherRest) : part = other := by
  cases first <;> cases second <;> rfl

private def retry_lost (active : Active core) (drop : P.Dropped core produced packetID .retry actual)
    (credit : P.Credited drop part) (selected : CampusTCPTwoProgressRetry.HeadRange sent part head rest)
    (live : monitor.retry.phase ≠ .done) : Active credit.result.next := by
  let raw := { monitor with drops := monitor.drops ++ [drop.item.id], retry := { monitor.retry with phase := .done } }
  have mode := retry_mode active live
  have ackNone := retry_ack active live
  have waitingFalse := retry_waiting active live
  have shape : Scalar received raw := {
    mode := .inr mode
    originals := fun impossible => by rw [mode] at impossible; cases impossible
    recovery := fun _ => active.recovery mode
    serial := fun pending => by rw [ackNone] at pending
    ackNonempty := fun pending => by rw [ackNone] at pending; cases pending
    waiting := fun waiting => by change monitor.waiting = true at waiting; rw [waitingFalse] at waiting; cases waiting }
  have normal := normalized active credit.result shape (observed_drop drop)
  apply assemble active drop credit.result normal
    (.done (by rw [normal.lowerLane]; exact (active.recovery mode).1))
    (.done (by rw [normal.upperLane]; exact (active.recovery mode).2))
    (.done (by rw [normal.retryLane]))
  · unfold AckState
    rw [normal.ack]
    change (match monitor.ack with | none => PUnit | some lane => AckWork credit.result.next lane)
    rw [ackNone]
    exact PUnit.unit
  · intro role head rest chosen
    have same := role_eq selected chosen
    subst role
    refine ⟨.cause core.losses.book.losses.length ?_⟩
    rw [credit.result.bookEq]
    cases part <;> rfl
  · intro retired missing _
    cases part with
    | lower =>
      obtain ⟨position, chosen⟩ := active.upperMissing retired missing (active.recovery mode).2
      exact ⟨position, by rw [credit.result.bookEq]; exact chosen⟩
    | upper => exact ⟨core.losses.book.losses.length, by rw [credit.result.bookEq]; rfl⟩
  · intro lane pending
    exact pending

def retry_ingress (active : Active core) (path : DataIngress initial current part monitor.retry)
    (selected : CampusTCPTwoProgressRetry.HeadRange sent part head rest)
    (drop : P.Dropped core path.output.produced path.packetID .retry actual) (credit : P.Credited drop part) :
    Active credit.result.next := retry_lost active drop credit selected (by rw [path.phase]; decide)

def retry_link (active : Active core) (path : DataLink initial current part monitor.retry)
    (selected : CampusTCPTwoProgressRetry.HeadRange sent part head rest)
    (drop : P.Dropped core path.served.ticket.value.produced path.packetID .retry actual) (credit : P.Credited drop part) :
    Active credit.result.next := retry_lost active drop credit selected (by rw [path.phase]; decide)

private theorem ack_shape (active : Active core) (pending : monitor.ack = some lane) (id : Nat) :
    Scalar received { monitor with drops := monitor.drops ++ [id], ack := none } := by
  refine ⟨active.mode, active.originals, active.recovery, ?_, ?_, ?_⟩
  · intro impossible; cases impossible
  · intro impossible; cases impossible
  · intro waiting
    have absent := (active.waiting waiting).1
    rw [pending] at absent
    cases absent

private def retain_ack_original (before : OriginalLane initial native current core.live.gatewayState received part lane)
    (drop : P.Dropped core produced packetID .ack actual)
    {book : CampusTCPTwoProgressLossHistory.Book initial (config initial native quantum allowance)}
    (result : CampusTCPTwoProgressPhaseDrop.Result drop.selected book) (ack : produced.actor = sender.other) :
    OriginalLane initial native drop.selected.appended.move.after result.next.live.gatewayState received part lane :=
  keepOriginalLane before drop result.next.live.gatewayState
    (fun other actor _ => (actors_ne other produced actor ack).symm)

private def ack_credit_lost (active : Active core) (drop : P.Dropped core produced packetID .ack actual)
    (credit : P.Credited drop part) (selected : CampusTCPTwoProgressRetry.HeadRange sent part head rest)
    (ack : produced.actor = sender.other) (pending : monitor.ack = some lane) : Active credit.result.next := by
  let raw := { monitor with drops := monitor.drops ++ [drop.item.id], ack := none }
  have normal := normalized active credit.result (ack_shape active pending drop.item.id) (observed_drop drop)
  apply assemble active drop credit.result normal
  · rw [normal.lowerLane]
    exact retain_ack_original active.lowerLane drop credit.result ack
  · rw [normal.upperLane]
    exact retain_ack_original active.upperLane drop credit.result ack
  · exact .done (by rw [normal.retryLane]; exact active.serial (by rw [pending]; rfl))
  · unfold AckState
    rw [normal.ack]
    exact PUnit.unit
  · intro role head rest chosen
    have same := role_eq selected chosen
    subst role
    refine ⟨.cause core.losses.book.losses.length ?_⟩
    rw [credit.result.bookEq]
    cases part <;> rfl
  · intro retired missing done
    cases part with
    | lower =>
      obtain ⟨position, chosen⟩ := active.upperMissing retired missing (by rw [normal.upperLane] at done; exact done)
      exact ⟨position, by rw [credit.result.bookEq]; exact chosen⟩
    | upper => exact ⟨core.losses.book.losses.length, by rw [credit.result.bookEq]; rfl⟩
  · intro lane impossible
    cases impossible

private def ack_unassigned_lost (active : Active core) (drop : P.Dropped core produced packetID .ack actual)
    (selected : CampusTCPTwoProgressRetry.HeadRange sent part head rest)
    (ack : produced.actor = sender.other) (pending : monitor.ack = some lane)
    (uncovered : ¬part.offset lower + (part.bytes lower upper).length ≤ (received.bytes lower upper).length) :
    Active drop.unassigned.next := by
  let raw := { monitor with drops := monitor.drops ++ [drop.item.id], ack := none }
  have normal := normalized active drop.unassigned (ack_shape active pending drop.item.id) (observed_drop drop)
  have lowerLane : OriginalLane initial native drop.selected.appended.move.after drop.unassigned.next.live.gatewayState received .lower
      (M.observe (config initial native quantum allowance) monitor actual).lower := by
    rw [normal.lowerLane]
    exact retain_ack_original active.lowerLane drop drop.unassigned ack
  have upperLane : OriginalLane initial native drop.selected.appended.move.after drop.unassigned.next.live.gatewayState received .upper
      (M.observe (config initial native quantum allowance) monitor actual).upper := by
    rw [normal.upperLane]
    exact retain_ack_original active.upperLane drop drop.unassigned ack
  apply assemble active drop drop.unassigned normal lowerLane upperLane
    (.done (by rw [normal.retryLane]; exact active.serial (by rw [pending]; rfl)))
  · unfold AckState
    rw [normal.ack]
    exact PUnit.unit
  · intro role head rest chosen
    have same := role_eq selected chosen
    subst role
    obtain ⟨debt⟩ := active.debt part head rest chosen
    cases debt with
    | cause position cause => exact ⟨.cause position (by rw [drop.unassigned.bookEq]; exact cause)⟩
    | lower same work => exact ⟨.lower same (CampusTCPTwoProgressPhaseNetworkState.OriginalLane.work lowerLane (by
        rw [normal.lowerLane]; exact work.not_done))⟩
    | upper same work => exact ⟨.upper same (CampusTCPTwoProgressPhaseNetworkState.OriginalLane.work upperLane (by
        rw [normal.upperLane]; exact work.not_done))⟩
    | retry work => exact False.elim (work.not_done (active.serial (by rw [pending]; rfl)))
    | ack _ _ covered => exact False.elim (uncovered covered)
  · intro retired missing done
    obtain ⟨position, chosen⟩ := active.upperMissing retired missing (by rw [normal.upperLane] at done; exact done)
    exact ⟨position, by rw [drop.unassigned.bookEq]; exact chosen⟩
  · intro lane impossible
    cases impossible

def ack_ingress_credited (active : Active core) (path : AckIngress initial current (received.bytes lower upper).length lane)
    (pending : monitor.ack = some lane) (selected : CampusTCPTwoProgressRetry.HeadRange sent part head rest)
    (drop : P.Dropped core path.output.produced path.packetID .ack actual) (credit : P.Credited drop part) :
    Active credit.result.next := ack_credit_lost active drop credit selected path.output.actor pending

def ack_link_credited (active : Active core) (path : AckLink initial current (received.bytes lower upper).length lane)
    (pending : monitor.ack = some lane) (selected : CampusTCPTwoProgressRetry.HeadRange sent part head rest)
    (drop : P.Dropped core path.served.ticket.value.produced path.packetID .ack actual) (credit : P.Credited drop part) :
    Active credit.result.next := ack_credit_lost active drop credit selected path.actor pending

def ack_ingress_unassigned (active : Active core) (path : AckIngress initial current (received.bytes lower upper).length lane)
    (pending : monitor.ack = some lane) (selected : CampusTCPTwoProgressRetry.HeadRange sent part head rest)
    (uncovered : ¬part.offset lower + (part.bytes lower upper).length ≤ (received.bytes lower upper).length)
    (drop : P.Dropped core path.output.produced path.packetID .ack actual) : Active drop.unassigned.next :=
  ack_unassigned_lost active drop selected path.output.actor pending uncovered

def ack_link_unassigned (active : Active core) (path : AckLink initial current (received.bytes lower upper).length lane)
    (pending : monitor.ack = some lane) (selected : CampusTCPTwoProgressRetry.HeadRange sent part head rest)
    (uncovered : ¬part.offset lower + (part.bytes lower upper).length ≤ (received.bytes lower upper).length)
    (drop : P.Dropped core path.served.ticket.value.produced path.packetID .ack actual) : Active drop.unassigned.next :=
  ack_unassigned_lost active drop selected path.actor pending uncovered

theorem received_bound (stage : R.Stage) : (stage.bytes lower upper).length ≤ lower.length + upper.length := by
  cases stage <;> simp only [CampusTCPTwoProgressReceiver.Stage.bytes, List.length_nil, List.length_append] <;> omega

theorem ack_covered (drop : P.Dropped core produced packetID .ack actual) (credit : P.Credited drop part)
    (fields : CampusTCPTwoProgressWire.AckFields initial (received.bytes lower upper).length produced) :
    part.offset lower + (part.bytes lower upper).length ≤ (received.bytes lower upper).length := by
  have actualFields : CampusTCPTwoProgressWire.AckFields initial (received.bytes lower upper).length drop.selected.loss.source := by
    rw [drop.sourceEq]
    exact fields
  cases credit.support with
  | lower different _ _ => change (.ack : M.DropTarget) = .lower at different; cases different
  | upper different _ _ => change (.ack : M.DropTarget) = .upper at different; cases different
  | retry _ different _ _ _ => change (.ack : M.DropTarget) = .retry at different; cases different
  | ack role _ _ _ _ fields within covered =>
    have same := CampusTCPTwoProgressLossHistory.ack_count_unique fields actualFields within (received_bound received)
    exact same ▸ covered

theorem ack_ingress_covered (path : AckIngress initial current (received.bytes lower upper).length lane)
    (drop : P.Dropped core path.output.produced path.packetID .ack actual) (credit : P.Credited drop part) :
    part.offset lower + (part.bytes lower upper).length ≤ (received.bytes lower upper).length :=
  ack_covered drop credit path.output.fields

theorem ack_link_covered (path : AckLink initial current (received.bytes lower upper).length lane)
    (drop : P.Dropped core path.served.ticket.value.produced path.packetID .ack actual) (credit : P.Credited drop part) :
    part.offset lower + (part.bytes lower upper).length ≤ (received.bytes lower upper).length :=
  ack_covered drop credit path.fields

theorem gap_uncovered (initial : TwoWriteInitial cut sender gateway lower upper) (part : S.Part)
    (zero : (received.bytes lower upper).length = 0) :
    ¬part.offset lower + (part.bytes lower upper).length ≤ (received.bytes lower upper).length := by
  have first := List.length_pos_iff.mpr initial.lowerNonempty
  have second := List.length_pos_iff.mpr initial.upperNonempty
  rw [zero]
  cases part <;> simp only [CampusTCPTwoProgressSender.Part.offset, CampusTCPTwoProgressSender.Part.bytes] <;> omega

def gap_ack_ingress (active : Active core) (path : AckIngress initial current (received.bytes lower upper).length lane)
    (pending : monitor.ack = some lane) (selected : CampusTCPTwoProgressRetry.HeadRange sent part head rest)
    (zero : (received.bytes lower upper).length = 0)
    (drop : P.Dropped core path.output.produced path.packetID .ack actual) : Active drop.unassigned.next :=
  ack_ingress_unassigned active path pending selected (gap_uncovered initial part zero) drop

def gap_ack_link (active : Active core) (path : AckLink initial current (received.bytes lower upper).length lane)
    (pending : monitor.ack = some lane) (selected : CampusTCPTwoProgressRetry.HeadRange sent part head rest)
    (zero : (received.bytes lower upper).length = 0)
    (drop : P.Dropped core path.served.ticket.value.produced path.packetID .ack actual) : Active drop.unassigned.next :=
  ack_link_unassigned active path pending selected (gap_uncovered initial part zero) drop

end Netlib.Check.CampusTCPTwoProgressPhaseDropState
