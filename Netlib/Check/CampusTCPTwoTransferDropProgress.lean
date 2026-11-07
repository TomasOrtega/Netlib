import Netlib.Check.CampusTCPTwoTransferDropWorkFrames
import Netlib.Check.CampusTCPTwoProgressPhaseNormalize

namespace Netlib.Check.CampusTCPTwoTransferDropProgress

open Protocol Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart
open CampusTCPTwoProgressPhaseBase (Arrived)
open CampusTCPTwoTransferNative (Checks Routing)
open CampusTCPTwoTransferLocatedCore (Core config)
open CampusTCPTwoTransferPhaseState CampusTCPTwoTransferWork CampusTCPTwoProgressPaths
open CampusTCPTwoTransferDropWorkFrames
open CampusTCPTwoProgressPhaseNormalize (Resolved normalize_unresolved)

namespace M
export CampusTCPTwoProgressMonitor (Monitor Lane DropTarget normalize)
end M
namespace W
export CampusTCPTwoTransferMonitor (observe Allowed)
end W
namespace S
export CampusTCPTwoProgressSender (Stage Part)
end S
namespace R
export CampusTCPTwoProgressReceiver (Stage)
end R
namespace D
export CampusTCPTwoTransferPhaseState (Debt)
end D
namespace P
export CampusTCPTwoTransferLocatedDrop (Dropped Credited originalTarget creditBook)
end P

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current : Cut input complete} {sender : Actor} {gateway location : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {checks : Checks cut initial.gatewayState.session.entry} {routing : Routing cut gateway}
variable {quantum allowance : Nat} {reverseLower reverseUpper : List UInt8}
variable {monitor : CampusTCPTwoTransferMonitor.Monitor} {raw updated : M.Monitor}
variable {sent : S.Stage initial} {received : R.Stage} {actual : Step input}
variable {core : Core initial checks routing quantum allowance reverseLower reverseUpper current monitor location sent received}
variable {produced : Produced input.active input.passive} {packetID : Nat} {target : M.DropTarget}
variable {part : S.Part} {lane : M.Lane} {head : Recovery.Outstanding} {rest : List Recovery.Outstanding}

local notation "cfg" => config initial checks routing quantum allowance reverseLower reverseUpper

private theorem normalize_cases
    {next : Cut input complete} {nextMonitor : CampusTCPTwoTransferMonitor.Monitor}
    (value : Core initial checks routing quantum allowance reverseLower reverseUpper next nextMonitor location sent received)
    (nonempty : sent.ledger ≠ []) (config : CampusTCPTwoProgressMonitor.Config) (source : config.sender = sender) :
    (¬Resolved raw ∧ M.normalize config next.report.final raw = raw) ∨
      (Resolved raw ∧ M.normalize config next.report.final raw = { raw with mode := .recovery, waiting := true }) := by
  by_cases resolved : Resolved raw
  · apply Or.inr
    refine ⟨resolved, ?_⟩
    have runtime : CampusTCPGapProgressMonitor.senderRecovery config.toConfig next.report.final = some value.live.senderFlight.recovery := by
      simp only [CampusTCPGapProgressMonitor.senderRecovery, next.connection, source, value.live.senderFlight.runtime]
    have present : value.live.senderFlight.recovery.outstanding.isEmpty = false := by
      rw [value.live.senderFlight.ledger]
      cases ledger : sent.ledger with
      | nil => exact False.elim (nonempty ledger)
      | cons entry tail => rfl
    simp (config := { zetaHave := true }) only [M.normalize, runtime, present, Bool.false_eq_true, ite_false]
    obtain ⟨ack, original | recovery⟩ := resolved
    · obtain ⟨mode, lower, upper⟩ := original
      rw [ack, mode, lower, upper]
      rfl
    · obtain ⟨mode, retry⟩ := recovery
      rw [ack, mode, retry]
      rfl
  · exact Or.inl ⟨resolved, normalize_unresolved _ _ _ resolved⟩

structure Scalar (received : R.Stage) (raw : M.Monitor) : Prop where
  mode : raw.mode = .originals ∨ raw.mode = .recovery
  originals : raw.mode = .originals → raw.retry.phase = .done ∧ raw.waiting = false ∧ raw.retries = 0
  recovery : raw.mode = .recovery → raw.lower.phase = .done ∧ raw.upper.phase = .done
  serial : raw.ack.isSome = true → raw.retry.phase = .done
  ackNonempty : raw.ack.isSome = true → received ≠ .empty
  waiting : raw.waiting = true → raw.ack = none ∧ raw.retry.phase = .done

structure Normal (received : R.Stage) (raw updated : M.Monitor) : Prop where
  shape : Scalar received updated
  lowerLane : updated.lower = raw.lower
  upperLane : updated.upper = raw.upper
  retryLane : updated.retry = raw.retry
  ack : updated.ack = raw.ack
  retries : updated.retries = raw.retries
  runnable : updated.mode = .recovery → updated.waiting = false → updated.ack = none → updated.retry.phase ≠ .done
  originalOpen : updated.mode = .originals → updated.ack = none → ¬(updated.lower.phase = .done ∧ updated.upper.phase = .done)

theorem normalized (active : Active core)
    {item : Theory.PacketCustody.Item (Transit input)} {selected : CampusTCPTwoTransferLocatedDrop.Selected core item target actual}
    {book : CampusTCPTwoTransferLoss.Book initial cfg}
    (result : CampusTCPTwoTransferLocatedDrop.Result selected book) (shape : Scalar received raw)
    (observed : (W.observe cfg monitor actual).exchange.forward =
      M.normalize (((cfg).at current.report.final).forward) selected.appended.move.after.report.final raw) :
    Normal received raw (W.observe cfg monitor actual).exchange.forward := by
  rcases normalize_cases (raw := raw) result.next active.nonempty (((cfg).at current.report.final).forward) rfl with
    ⟨unresolved, same⟩ | ⟨resolved, same⟩
  · rw [observed, same]
    refine ⟨shape, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
    · intro mode _ ack done
      exact unresolved ⟨ack, .inr ⟨mode, done⟩⟩
    · intro mode ack done
      exact unresolved ⟨ack, .inl ⟨mode, done.1, done.2⟩⟩
  · have fields : raw.ack = none ∧ raw.lower.phase = .done ∧ raw.upper.phase = .done ∧ raw.retry.phase = .done := by
      obtain ⟨ack, first | second⟩ := resolved
      · exact ⟨ack, first.2.1, first.2.2, (shape.originals first.1).1⟩
      · exact ⟨ack, (shape.recovery second.1).1, (shape.recovery second.1).2, second.2⟩
    rw [observed, same]
    refine ⟨?_, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
    · refine ⟨.inr rfl, ?_, fun _ => ⟨fields.2.1, fields.2.2.1⟩, ?_, ?_, fun _ => ⟨fields.1, fields.2.2.2⟩⟩
      · intro impossible; cases impossible
      · intro pending; rw [fields.1] at pending; cases pending
      · intro pending; rw [fields.1] at pending; cases pending
    · intro _ impossible; cases impossible
    · intro impossible; cases impossible

theorem observed_drop (drop : P.Dropped core produced packetID target actual) :
    (W.observe cfg monitor actual).exchange.forward =
      M.normalize (((cfg).at current.report.final).forward) drop.selected.appended.move.after.report.final
        (CampusTCPTwoTransferLocatedDrop.rawDrop monitor.exchange.forward drop.item.id target) :=
  drop.selected.local_observed

theorem recovery_fields (drop : P.Dropped core produced packetID target actual)
    (mode : (W.observe cfg monitor actual).exchange.forward.mode = .recovery)
    (waiting : (W.observe cfg monitor actual).exchange.forward.waiting = false) :
    monitor.exchange.forward.mode = .recovery ∧ monitor.exchange.forward.waiting = false := by
  rw [observed_drop drop] at mode waiting
  have same := CampusTCPTwoProgressRecoveryHead.normalize_nonwaiting_eq _ _ _ mode waiting
  rw [same] at mode waiting
  cases target <;> exact ⟨mode, waiting⟩

private def assemble (active : Active core) (drop : P.Dropped core produced packetID target actual)
    {book : CampusTCPTwoTransferLoss.Book initial cfg}
    (result : CampusTCPTwoTransferLocatedDrop.Result drop.selected book)
    (normal : Normal received raw (W.observe cfg monitor actual).exchange.forward)
    (lowerLane : OriginalLane initial checks drop.selected.appended.move.after result.next.live.gatewayState received .lower
      (W.observe cfg monitor actual).exchange.forward.lower)
    (upperLane : OriginalLane initial checks drop.selected.appended.move.after result.next.live.gatewayState received .upper
      (W.observe cfg monitor actual).exchange.forward.upper)
    (retry : RetryLane initial checks drop.selected.appended.move.after result.next.live.gatewayState sent
      (W.observe cfg monitor actual).exchange.forward.retry)
    (ack : AckState checks result.next.live (W.observe cfg monitor actual).exchange.forward.ack)
    (debt : ∀ role head rest, CampusTCPTwoProgressRetry.HeadRange sent role head rest → Nonempty (D.Debt result.next role))
    (upperMissing : sent.retiredBytes = 0 → ¬Arrived received .upper →
      (W.observe cfg monitor actual).exchange.forward.upper.phase = .done →
      ∃ position, result.next.losses.book.cause .upper = some position)
    (ackFrom : ∀ lane, raw.ack = some lane → monitor.exchange.forward.ack = some lane) : Active result.next := by
  have runtime := result.sender_recovery
  have session := result.session
  exact {
    exchange := by rw [drop.selected.observed]; exact active.exchange
    mode := normal.shape.mode
    preparing := active.preparing, nonempty := active.nonempty
    lowerLane, upperLane, retry, ack
    originals := normal.shape.originals, recovery := normal.shape.recovery
    recoveryHead := fun mode waiting => active.recoveryHead (recovery_fields drop mode waiting).1
      (recovery_fields drop mode waiting).2
    serial := normal.shape.serial, ackNonempty := normal.shape.ackNonempty, waiting := normal.shape.waiting
    ackGateway := fun lane pending phase => by
      rw [session]
      exact active.ackGateway lane (ackFrom lane (normal.ack.symm ▸ pending)) phase
    runnable := normal.runnable, originalOpen := normal.originalOpen
    debt, upperMissing
    zeroAck := fun lane pending retired => by
      rw [runtime]
      exact active.zeroAck lane (ackFrom lane (normal.ack.symm ▸ pending)) retired
    sources := active.sources.non_delivery drop.selected.appended.move (by rw [drop.selected.appended.facts.event]; trivial) }


def keepAckState (active : Active core) (drop : P.Dropped core produced packetID target actual)
    {book : CampusTCPTwoTransferLoss.Book initial cfg}
    (result : CampusTCPTwoTransferLocatedDrop.Result drop.selected book) (data : produced.actor = sender)
    (same : (W.observe cfg monitor actual).exchange.forward.ack = monitor.exchange.forward.ack) : AckState checks result.next.live (W.observe cfg monitor actual).exchange.forward.ack := by
  unfold AckState
  rw [same]
  cases found : monitor.exchange.forward.ack with
  | none => exact PUnit.unit
  | some lane =>
    have before : AckWork checks core.live lane := by simpa only [AckState, found] using active.ack
    exact keepAckWork before drop result data

private theorem original_mode (active : Active core) (part : S.Part)
    (live : (match part with | .lower => monitor.exchange.forward.lower | .upper => monitor.exchange.forward.upper).phase ≠ .done) :
    monitor.exchange.forward.mode = .originals := by
  rcases active.mode with mode | mode
  · exact mode
  · obtain ⟨first, second⟩ := active.recovery mode
    cases part
    · exact False.elim (live first)
    · exact False.elim (live second)

private def lower_lost (active : Active core) (drop : P.Dropped core produced packetID .lower actual)
    (credit : P.Credited drop .lower) (data : produced.actor = sender)
    (fields : CampusTCPTwoProgressWire.DataFields initial 0 lower produced) (live : monitor.exchange.forward.lower.phase ≠ .done) :
    Active credit.result.next := by
  let raw := { monitor.exchange.forward with drops := monitor.exchange.forward.drops ++ [drop.item.id], lower := { monitor.exchange.forward.lower with phase := .done } }
  have mode := original_mode active .lower live
  have shape : Scalar received raw := {
    mode := .inl mode
    originals := fun _ => active.originals mode
    recovery := fun impossible => by rw [mode] at impossible; cases impossible
    serial := active.serial, ackNonempty := active.ackNonempty, waiting := active.waiting }
  have normal := normalized active credit.result shape (by simpa only [CampusTCPTwoTransferLocatedDrop.rawDrop] using observed_drop drop)
  have upperLane : OriginalLane initial checks drop.selected.appended.move.after credit.result.next.live.gatewayState received .upper
      (W.observe cfg monitor actual).exchange.forward.upper := by
    rw [normal.upperLane]
    exact keepOriginalLane active.upperLane drop credit.result
      (fun other _ otherFields => CampusTCPTwoProgressPathsDistinct.produced_ne fields otherFields)
  have ackSame : (W.observe cfg monitor actual).exchange.forward.ack = monitor.exchange.forward.ack := normal.ack
  apply assemble active drop credit.result normal
    (.done (by rw [normal.lowerLane])) upperLane
    (.done (by rw [normal.retryLane]; exact (active.originals mode).1))
    (keepAckState active drop credit.result data ackSame)
  · intro role head rest selected
    cases role with
    | lower =>
      exact ⟨.cause core.losses.book.losses.length (by rw [credit.result.bookEq]; rfl)⟩
    | upper =>
      obtain ⟨debt⟩ := active.debt .upper head rest selected
      cases debt with
      | cause position chosen => exact ⟨.cause position (by rw [credit.result.bookEq]; exact chosen)⟩
      | lower same _ => cases same
      | upper _ work => exact ⟨.upper rfl (CampusTCPTwoTransferWork.OriginalLane.work upperLane (by
          rw [normal.upperLane]; exact work.not_done))⟩
      | retry work => exact False.elim (work.not_done (active.originals mode).1)
      | ack lane pending work covered => exact ⟨.ack lane (ackSame.trans pending)
        (keepAckWork work drop credit.result data) covered⟩
  · intro retired missing done
    obtain ⟨position, chosen⟩ := active.upperMissing retired missing (by rw [normal.upperLane] at done; exact done)
    exact ⟨position, by rw [credit.result.bookEq]; exact chosen⟩
  · intro lane pending
    exact pending

private def upper_lost (active : Active core) (drop : P.Dropped core produced packetID .upper actual)
    (credit : P.Credited drop .upper) (data : produced.actor = sender)
    (fields : CampusTCPTwoProgressWire.DataFields initial lower.length upper produced) (live : monitor.exchange.forward.upper.phase ≠ .done) :
    Active credit.result.next := by
  let raw := { monitor.exchange.forward with drops := monitor.exchange.forward.drops ++ [drop.item.id], upper := { monitor.exchange.forward.upper with phase := .done } }
  have mode := original_mode active .upper live
  have shape : Scalar received raw := {
    mode := .inl mode
    originals := fun _ => active.originals mode
    recovery := fun impossible => by rw [mode] at impossible; cases impossible
    serial := active.serial, ackNonempty := active.ackNonempty, waiting := active.waiting }
  have normal := normalized active credit.result shape (by simpa only [CampusTCPTwoTransferLocatedDrop.rawDrop] using observed_drop drop)
  have lowerLane : OriginalLane initial checks drop.selected.appended.move.after credit.result.next.live.gatewayState received .lower
      (W.observe cfg monitor actual).exchange.forward.lower := by
    rw [normal.lowerLane]
    exact keepOriginalLane active.lowerLane drop credit.result
      (fun other _ otherFields => (CampusTCPTwoProgressPathsDistinct.produced_ne otherFields fields).symm)
  have ackSame : (W.observe cfg monitor actual).exchange.forward.ack = monitor.exchange.forward.ack := normal.ack
  apply assemble active drop credit.result normal lowerLane
    (.done (by rw [normal.upperLane]))
    (.done (by rw [normal.retryLane]; exact (active.originals mode).1))
    (keepAckState active drop credit.result data ackSame)
  · intro role head rest selected
    cases role with
    | lower =>
      obtain ⟨debt⟩ := active.debt .lower head rest selected
      cases debt with
      | cause position chosen => exact ⟨.cause position (by rw [credit.result.bookEq]; exact chosen)⟩
      | lower _ work => exact ⟨.lower rfl (CampusTCPTwoTransferWork.OriginalLane.work lowerLane (by
          rw [normal.lowerLane]; exact work.not_done))⟩
      | upper same _ => cases same
      | retry work => exact False.elim (work.not_done (active.originals mode).1)
      | ack lane pending work covered => exact ⟨.ack lane (ackSame.trans pending)
        (keepAckWork work drop credit.result data) covered⟩
    | upper =>
      exact ⟨.cause core.losses.book.losses.length (by rw [credit.result.bookEq]; rfl)⟩
  · intro _ _ _
    exact ⟨core.losses.book.losses.length, by rw [credit.result.bookEq]; rfl⟩
  · intro lane pending
    exact pending

def lower_ingress (active : Active core) (path : DataIngress initial current .lower monitor.exchange.forward.lower)
    (drop : P.Dropped core path.output.produced path.packetID .lower actual) (credit : P.Credited drop .lower) :
    Active credit.result.next :=
  lower_lost active drop credit path.output.actor path.output.fields (by rw [path.phase]; decide)

def lower_link (active : Active core) (path : DataLink initial current .lower monitor.exchange.forward.lower)
    (drop : P.Dropped core path.served.ticket.value.produced path.packetID .lower actual) (credit : P.Credited drop .lower) :
    Active credit.result.next :=
  lower_lost active drop credit path.actor path.fields (by rw [path.phase]; decide)

def upper_ingress (active : Active core) (path : DataIngress initial current .upper monitor.exchange.forward.upper)
    (drop : P.Dropped core path.output.produced path.packetID .upper actual) (credit : P.Credited drop .upper) :
    Active credit.result.next :=
  upper_lost active drop credit path.output.actor path.output.fields (by rw [path.phase]; decide)

def upper_link (active : Active core) (path : DataLink initial current .upper monitor.exchange.forward.upper)
    (drop : P.Dropped core path.served.ticket.value.produced path.packetID .upper actual) (credit : P.Credited drop .upper) :
    Active credit.result.next :=
  upper_lost active drop credit path.actor path.fields (by rw [path.phase]; decide)

private theorem retry_mode (active : Active core) (live : monitor.exchange.forward.retry.phase ≠ .done) : monitor.exchange.forward.mode = .recovery := by
  rcases active.mode with mode | mode
  · exact False.elim (live (active.originals mode).1)
  · exact mode

private theorem retry_ack (active : Active core) (live : monitor.exchange.forward.retry.phase ≠ .done) : monitor.exchange.forward.ack = none := by
  cases found : monitor.exchange.forward.ack with
  | none => rfl
  | some lane => exact False.elim (live (active.serial (by rw [found]; rfl)))

private theorem retry_waiting (active : Active core) (live : monitor.exchange.forward.retry.phase ≠ .done) : monitor.exchange.forward.waiting = false := by
  cases waiting : monitor.exchange.forward.waiting with
  | false => rfl
  | true => exact False.elim (live (active.waiting waiting).2)

private theorem role_eq {other : S.Part} {otherHead : Recovery.Outstanding} {otherRest : List Recovery.Outstanding}
    (first : CampusTCPTwoProgressRetry.HeadRange sent part head rest)
    (second : CampusTCPTwoProgressRetry.HeadRange sent other otherHead otherRest) : part = other := by
  cases first <;> cases second <;> rfl

private def retry_lost (active : Active core) (drop : P.Dropped core produced packetID .retry actual)
    (credit : P.Credited drop part) (selected : CampusTCPTwoProgressRetry.HeadRange sent part head rest)
    (live : monitor.exchange.forward.retry.phase ≠ .done) : Active credit.result.next := by
  let raw := { monitor.exchange.forward with drops := monitor.exchange.forward.drops ++ [drop.item.id], retry := { monitor.exchange.forward.retry with phase := .done } }
  have mode := retry_mode active live
  have ackNone := retry_ack active live
  have waitingFalse := retry_waiting active live
  have shape : Scalar received raw := {
    mode := .inr mode
    originals := fun impossible => by rw [mode] at impossible; cases impossible
    recovery := fun _ => active.recovery mode
    serial := fun pending => by rw [ackNone] at pending
    ackNonempty := fun pending => by rw [ackNone] at pending; cases pending
    waiting := fun waiting => by change monitor.exchange.forward.waiting = true at waiting; rw [waitingFalse] at waiting; cases waiting }
  have normal := normalized active credit.result shape (by simpa only [CampusTCPTwoTransferLocatedDrop.rawDrop] using observed_drop drop)
  apply assemble active drop credit.result normal
    (.done (by rw [normal.lowerLane]; exact (active.recovery mode).1))
    (.done (by rw [normal.upperLane]; exact (active.recovery mode).2))
    (.done (by rw [normal.retryLane]))
  · unfold AckState
    rw [normal.ack]
    change (match monitor.exchange.forward.ack with | none => PUnit | some lane => AckWork checks credit.result.next.live lane)
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

def retry_ingress (active : Active core) (path : DataIngress initial current part monitor.exchange.forward.retry)
    (selected : CampusTCPTwoProgressRetry.HeadRange sent part head rest)
    (drop : P.Dropped core path.output.produced path.packetID .retry actual) (credit : P.Credited drop part) :
    Active credit.result.next := retry_lost active drop credit selected (by rw [path.phase]; decide)

def retry_link (active : Active core) (path : DataLink initial current part monitor.exchange.forward.retry)
    (selected : CampusTCPTwoProgressRetry.HeadRange sent part head rest)
    (drop : P.Dropped core path.served.ticket.value.produced path.packetID .retry actual) (credit : P.Credited drop part) :
    Active credit.result.next := retry_lost active drop credit selected (by rw [path.phase]; decide)

private theorem ack_shape (active : Active core) (pending : monitor.exchange.forward.ack = some lane) (id : Nat) :
    Scalar received { monitor.exchange.forward with drops := monitor.exchange.forward.drops ++ [id], ack := none } := by
  refine ⟨active.mode, active.originals, active.recovery, ?_, ?_, ?_⟩
  · intro impossible; cases impossible
  · intro impossible; cases impossible
  · intro waiting
    have absent := (active.waiting waiting).1
    rw [pending] at absent
    cases absent

private def retain_ack_original (before : OriginalLane initial checks current core.live.gatewayState received part lane)
    (drop : P.Dropped core produced packetID .ack actual)
    {book : CampusTCPTwoTransferLoss.Book initial cfg}
    (result : CampusTCPTwoTransferLocatedDrop.Result drop.selected book) (ack : produced.actor = sender.other) :
    OriginalLane initial checks drop.selected.appended.move.after result.next.live.gatewayState received part lane :=
  keepOriginalLane before drop result
    (fun other actor _ => (actors_ne other produced actor ack).symm)

private def ack_credit_lost (active : Active core) (drop : P.Dropped core produced packetID .ack actual)
    (credit : P.Credited drop part) (selected : CampusTCPTwoProgressRetry.HeadRange sent part head rest)
    (ack : produced.actor = sender.other) (pending : monitor.exchange.forward.ack = some lane) : Active credit.result.next := by
  let raw := { monitor.exchange.forward with drops := monitor.exchange.forward.drops ++ [drop.item.id], ack := none }
  have normal := normalized active credit.result (ack_shape active pending drop.item.id) (by simpa only [CampusTCPTwoTransferLocatedDrop.rawDrop] using observed_drop drop)
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
    (ack : produced.actor = sender.other) (pending : monitor.exchange.forward.ack = some lane)
    (uncovered : ¬part.offset lower + (part.bytes lower upper).length ≤ (received.bytes lower upper).length) :
    Active drop.unassigned.next := by
  let raw := { monitor.exchange.forward with drops := monitor.exchange.forward.drops ++ [drop.item.id], ack := none }
  have normal := normalized active drop.unassigned (ack_shape active pending drop.item.id) (by simpa only [CampusTCPTwoTransferLocatedDrop.rawDrop] using observed_drop drop)
  have lowerLane : OriginalLane initial checks drop.selected.appended.move.after drop.unassigned.next.live.gatewayState received .lower
      (W.observe cfg monitor actual).exchange.forward.lower := by
    rw [normal.lowerLane]
    exact retain_ack_original active.lowerLane drop drop.unassigned ack
  have upperLane : OriginalLane initial checks drop.selected.appended.move.after drop.unassigned.next.live.gatewayState received .upper
      (W.observe cfg monitor actual).exchange.forward.upper := by
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
    | lower same work => exact ⟨.lower same (CampusTCPTwoTransferWork.OriginalLane.work lowerLane (by
        rw [normal.lowerLane]; exact work.not_done))⟩
    | upper same work => exact ⟨.upper same (CampusTCPTwoTransferWork.OriginalLane.work upperLane (by
        rw [normal.upperLane]; exact work.not_done))⟩
    | retry work => exact False.elim (work.not_done (active.serial (by rw [pending]; rfl)))
    | ack _ _ _ covered => exact False.elim (uncovered covered)
  · intro retired missing done
    obtain ⟨position, chosen⟩ := active.upperMissing retired missing (by rw [normal.upperLane] at done; exact done)
    exact ⟨position, by rw [drop.unassigned.bookEq]; exact chosen⟩
  · intro lane impossible
    cases impossible

def ack_ingress_credited (active : Active core) (path : AckIngress initial current (received.bytes lower upper).length lane)
    (pending : monitor.exchange.forward.ack = some lane) (selected : CampusTCPTwoProgressRetry.HeadRange sent part head rest)
    (drop : P.Dropped core path.output.produced path.packetID .ack actual) (credit : P.Credited drop part) :
    Active credit.result.next := ack_credit_lost active drop credit selected path.output.actor pending

def ack_link_credited (active : Active core) (path : AckLink initial current (received.bytes lower upper).length lane)
    (pending : monitor.exchange.forward.ack = some lane) (selected : CampusTCPTwoProgressRetry.HeadRange sent part head rest)
    (drop : P.Dropped core path.served.ticket.value.produced path.packetID .ack actual) (credit : P.Credited drop part) :
    Active credit.result.next := ack_credit_lost active drop credit selected path.actor pending

def ack_ingress_unassigned (active : Active core) (path : AckIngress initial current (received.bytes lower upper).length lane)
    (pending : monitor.exchange.forward.ack = some lane) (selected : CampusTCPTwoProgressRetry.HeadRange sent part head rest)
    (uncovered : ¬part.offset lower + (part.bytes lower upper).length ≤ (received.bytes lower upper).length)
    (drop : P.Dropped core path.output.produced path.packetID .ack actual) : Active drop.unassigned.next :=
  ack_unassigned_lost active drop selected path.output.actor pending uncovered

def ack_link_unassigned (active : Active core) (path : AckLink initial current (received.bytes lower upper).length lane)
    (pending : monitor.exchange.forward.ack = some lane) (selected : CampusTCPTwoProgressRetry.HeadRange sent part head rest)
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
    have same := CampusTCPTwoTransferLoss.ack_count_unique fields actualFields within (received_bound received)
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
    (pending : monitor.exchange.forward.ack = some lane) (selected : CampusTCPTwoProgressRetry.HeadRange sent part head rest)
    (zero : (received.bytes lower upper).length = 0)
    (drop : P.Dropped core path.output.produced path.packetID .ack actual) : Active drop.unassigned.next :=
  ack_ingress_unassigned active path pending selected (gap_uncovered initial part zero) drop

def gap_ack_link (active : Active core) (path : AckLink initial current (received.bytes lower upper).length lane)
    (pending : monitor.exchange.forward.ack = some lane) (selected : CampusTCPTwoProgressRetry.HeadRange sent part head rest)
    (zero : (received.bytes lower upper).length = 0)
    (drop : P.Dropped core path.served.ticket.value.produced path.packetID .ack actual) : Active drop.unassigned.next :=
  ack_link_unassigned active path pending selected (gap_uncovered initial part zero) drop

def fundingBook (drop : P.Dropped core produced packetID target actual) : Option S.Part → CampusTCPTwoTransferLoss.Book initial cfg
  | none => core.losses.book.appendLoss drop.selected.loss
  | some part => P.creditBook drop.selected part

structure Advanced (core : Core initial checks routing quantum allowance reverseLower reverseUpper current monitor location sent received)
    (id : Nat) (actual : Step input) where
  produced : Produced input.active input.passive
  target : M.DropTarget
  drop : P.Dropped core produced id target actual
  funding : Option S.Part
  result : CampusTCPTwoTransferLocatedDrop.Result drop.selected (fundingBook drop funding)
  active : Active result.next
  support : ∀ part, funding = some part → CampusTCPTwoTransferLoss.Supports drop.selected.loss part

private def ofCredit (drop : P.Dropped core produced packetID target actual) (credit : P.Credited drop part)
    (active : Active credit.result.next) : Advanced core packetID actual where
  produced := produced
  target := target
  drop := drop
  funding := some part
  result := credit.result
  active := active
  support := fun _role same => (Option.some.inj same) ▸ credit.support

private def ofUnassigned (drop : P.Dropped core produced packetID target actual) (active : Active drop.unassigned.next) :
    Advanced core packetID actual where
  produced := produced
  target := target
  drop := drop
  funding := none
  result := drop.unassigned
  active := active
  support := by intro _role impossible; cases impossible

theorem Advanced.event {id : Nat} (value : Advanced core id actual) : actual.event = .dropPacket id := value.drop.event

theorem Advanced.healthy {id : Nat} (value : Advanced core id actual) : (W.observe cfg monitor actual).mode ≠ .invalid :=
  value.drop.selected.healthy

theorem Advanced.no_gap_funding {id : Nat} (value : Advanced core id actual) (target : value.target = .ack)
    (fields : CampusTCPTwoProgressWire.AckFields initial 0 value.produced) : value.funding = none := by
  cases funding : value.funding with
  | none => rfl
  | some part =>
    have unsupported : ¬CampusTCPTwoTransferLoss.Supports value.drop.selected.loss part :=
      CampusTCPTwoTransferLoss.Supports.no_gap_ack target (by rw [value.drop.sourceEq]; exact fields)
    exact False.elim (unsupported (value.support part funding))

theorem Advanced.upper_cause {id : Nat} (value : Advanced core id actual) (unfunded : value.funding ≠ some .upper) :
    value.result.next.losses.book.upper = core.losses.book.upper := by
  rw [value.result.bookEq]
  cases funding : value.funding with
  | none => rfl
  | some part =>
    cases part
    · rfl
    · exact False.elim (unfunded funding)

theorem Advanced.lower_cause {id : Nat} (value : Advanced core id actual) (unfunded : value.funding ≠ some .lower) :
    value.result.next.losses.book.lower = core.losses.book.lower := by
  rw [value.result.bookEq]
  cases funding : value.funding with
  | none => rfl
  | some part =>
    cases part
    · exact False.elim (unfunded funding)
    · rfl

private def currentHead (selection : CampusTCPTwoProgressRetry.HeadRange sent part head rest) :
    CampusTCPTwoProgressLossHistory.Head initial current part where
  recovery := core.live.senderFlight.recovery
  runtime := core.live.senderFlight.runtime
  entry := head
  tail := rest
  ledger := core.live.senderFlight.ledger.trans selection.ledger
  identity := selection.identity core.live.senderFlight
  position := by cases selection <;> exact congrArg Recovery.Outstanding.start core.live.senderFlight.headFixed
  count := selection.count core.live.senderFlight

private theorem exposed_none (config : CampusTCPTwoProgressMonitor.Config) (state : State input) (lane : M.Lane)
    (empty : CampusTCPGapProgressMonitor.packetAt lane.toGap = none) :
    CampusTCPTwoProgressMonitor.exposedPacket config state lane = none := by
  unfold CampusTCPTwoProgressMonitor.exposedPacket
  cases action : CampusTCPGapProgressMonitor.nextAction config.toConfig state lane.toGap <;> simp only [bind, Option.bind, empty]

private theorem exposed_done (config : CampusTCPTwoProgressMonitor.Config) (lane : M.Lane) (phase : lane.phase = .done) :
    CampusTCPTwoProgressMonitor.exposedPacket config current.report.final lane = none :=
  exposed_none config _ lane (by simp only [CampusTCPGapProgressMonitor.packetAt, CampusTCPTwoProgressMonitor.Lane.toGap, phase])

private theorem lower_at (active : Active core) (id : Nat)
    (chosen : CampusTCPTwoProgressMonitor.dropTarget (((cfg).at current.report.final).forward)
      current.report.final monitor.exchange.forward id = some .lower)
    (allowed : W.Allowed cfg current.report.final monitor (.dropPacket id)) : ∃ actual, Nonempty (Advanced core id actual) := by
  have exposed := CampusTCPTwoProgressMonitorFacts.dropTarget_packet _ _ _ _ chosen
  cases active.lowerLane with
  | done phase => rw [exposed_done _ _ phase] at exposed; cases exposed
  | active work missing =>
    cases work with
    | ingress path source =>
      have same : path.packetID = id := Option.some.inj ((path.exposed_packet _).symm.trans exposed)
      obtain ⟨actual, drop, ⟨credit⟩⟩ := CampusTCPTwoTransferLocatedDrop.original_ingress_at core active.exchange path
        (by rw [same]; exact chosen) (by rw [same]; exact allowed)
      exact ⟨actual, ⟨same ▸ ofCredit drop credit (lower_ingress active path drop credit)⟩⟩
    | ticket path _ _ => rw [path.exposed_packet _] at exposed; cases exposed
    | link path source covered =>
      have same : path.packetID = id := Option.some.inj ((path.exposed_packet _).symm.trans exposed)
      obtain ⟨actual, drop, ⟨credit⟩⟩ := CampusTCPTwoTransferLocatedDrop.original_link_at core active.exchange path
        (by rw [same]; exact chosen) (by rw [same]; exact allowed)
      exact ⟨actual, ⟨same ▸ ofCredit drop credit (lower_link active path drop credit)⟩⟩

private theorem upper_at (active : Active core) (id : Nat)
    (chosen : CampusTCPTwoProgressMonitor.dropTarget (((cfg).at current.report.final).forward)
      current.report.final monitor.exchange.forward id = some .upper)
    (allowed : W.Allowed cfg current.report.final monitor (.dropPacket id)) : ∃ actual, Nonempty (Advanced core id actual) := by
  have exposed := CampusTCPTwoProgressMonitorFacts.dropTarget_packet _ _ _ _ chosen
  cases active.upperLane with
  | done phase => rw [exposed_done _ _ phase] at exposed; cases exposed
  | active work missing =>
    cases work with
    | ingress path source =>
      have same : path.packetID = id := Option.some.inj ((path.exposed_packet _).symm.trans exposed)
      obtain ⟨actual, drop, ⟨credit⟩⟩ := CampusTCPTwoTransferLocatedDrop.original_ingress_at core active.exchange path
        (by rw [same]; exact chosen) (by rw [same]; exact allowed)
      exact ⟨actual, ⟨same ▸ ofCredit drop credit (upper_ingress active path drop credit)⟩⟩
    | ticket path _ _ => rw [path.exposed_packet _] at exposed; cases exposed
    | link path source covered =>
      have same : path.packetID = id := Option.some.inj ((path.exposed_packet _).symm.trans exposed)
      obtain ⟨actual, drop, ⟨credit⟩⟩ := CampusTCPTwoTransferLocatedDrop.original_link_at core active.exchange path
        (by rw [same]; exact chosen) (by rw [same]; exact allowed)
      exact ⟨actual, ⟨same ▸ ofCredit drop credit (upper_link active path drop credit)⟩⟩

private theorem retry_at (active : Active core) (id : Nat)
    (chosen : CampusTCPTwoProgressMonitor.dropTarget (((cfg).at current.report.final).forward)
      current.report.final monitor.exchange.forward id = some .retry)
    (allowed : W.Allowed cfg current.report.final monitor (.dropPacket id)) : ∃ actual, Nonempty (Advanced core id actual) := by
  have exposed := CampusTCPTwoProgressMonitorFacts.dropTarget_packet _ _ _ _ chosen
  cases active.retry with
  | done phase => rw [exposed_done _ _ phase] at exposed; cases exposed
  | active part head rest selection work =>
    cases work with
    | ingress path source =>
      have same : path.packetID = id := Option.some.inj ((path.exposed_packet _).symm.trans exposed)
      obtain ⟨actual, drop, ⟨credit⟩⟩ := CampusTCPTwoTransferLocatedDrop.retry_ingress_at core active.exchange path
        (currentHead (core := core) selection) (by rw [same]; exact chosen) (by rw [same]; exact allowed)
      exact ⟨actual, ⟨same ▸ ofCredit drop credit (retry_ingress active path selection drop credit)⟩⟩
    | ticket path _ _ => rw [path.exposed_packet _] at exposed; cases exposed
    | link path source covered =>
      have same : path.packetID = id := Option.some.inj ((path.exposed_packet _).symm.trans exposed)
      obtain ⟨actual, drop, ⟨credit⟩⟩ := CampusTCPTwoTransferLocatedDrop.retry_link_at core active.exchange path
        (currentHead (core := core) selection) (by rw [same]; exact chosen) (by rw [same]; exact allowed)
      exact ⟨actual, ⟨same ▸ ofCredit drop credit (retry_link active path selection drop credit)⟩⟩

private theorem ack_at (active : Active core) (id : Nat)
    (chosen : CampusTCPTwoProgressMonitor.dropTarget (((cfg).at current.report.final).forward)
      current.report.final monitor.exchange.forward id = some .ack)
    (allowed : W.Allowed cfg current.report.final monitor (.dropPacket id)) : ∃ actual, Nonempty (Advanced core id actual) := by
  obtain ⟨lane, pending, exposed⟩ := CampusTCPTwoProgressMonitorFacts.dropTarget_packet _ _ _ _ chosen
  have work : AckWork checks core.live lane := by simpa only [AckState, pending] using active.ack
  obtain ⟨part, head, rest, selection⟩ := active.current_head
  cases work with
  | pending phase _ =>
    have absent := exposed_none (((cfg).at current.report.final).forward) current.report.final lane
      (by simp only [CampusTCPGapProgressMonitor.packetAt, CampusTCPTwoProgressMonitor.Lane.toGap, phase])
    rw [absent] at exposed
    cases exposed
  | ticket path _ => rw [path.exposed_packet _] at exposed; cases exposed
  | ingress path =>
    have same : path.packetID = id := Option.some.inj ((path.exposed_packet _).symm.trans exposed)
    by_cases covered : part.offset lower + (part.bytes lower upper).length ≤ (received.bytes lower upper).length
    · obtain ⟨actual, drop, ⟨credit⟩⟩ := CampusTCPTwoTransferLocatedDrop.ack_ingress_at core active.exchange path
        (currentHead (core := core) selection) (received_bound received) covered (by rw [same]; exact chosen) (by rw [same]; exact allowed)
      exact ⟨actual, ⟨same ▸ ofCredit drop credit (ack_ingress_credited active path pending selection drop credit)⟩⟩
    · obtain ⟨actual, ⟨drop⟩⟩ := CampusTCPTwoTransferLocatedDrop.ingress_at core active.exchange path.toIngress
        (by rw [same]; exact chosen) (by rw [same]; exact allowed)
      exact ⟨actual, ⟨same ▸ ofUnassigned drop (ack_ingress_unassigned active path pending selection covered drop)⟩⟩
  | link path =>
    have same : path.packetID = id := Option.some.inj ((path.exposed_packet _).symm.trans exposed)
    by_cases covered : part.offset lower + (part.bytes lower upper).length ≤ (received.bytes lower upper).length
    · obtain ⟨actual, drop, ⟨credit⟩⟩ := CampusTCPTwoTransferLocatedDrop.ack_link_at core active.exchange path
        (currentHead (core := core) selection) (received_bound received) covered (by rw [same]; exact chosen) (by rw [same]; exact allowed)
      exact ⟨actual, ⟨same ▸ ofCredit drop credit (ack_link_credited active path pending selection drop credit)⟩⟩
    · obtain ⟨actual, ⟨drop⟩⟩ := CampusTCPTwoTransferLocatedDrop.link_at core active.exchange path.toLink
        (by rw [same]; exact chosen) (by rw [same]; exact allowed)
      exact ⟨actual, ⟨same ▸ ofUnassigned drop (ack_link_unassigned active path pending selection covered drop)⟩⟩

theorem drop_at (active : Active core) (id : Nat) (target : M.DropTarget)
    (chosen : CampusTCPTwoProgressMonitor.dropTarget (((cfg).at current.report.final).forward)
      current.report.final monitor.exchange.forward id = some target)
    (allowed : W.Allowed cfg current.report.final monitor (.dropPacket id)) : ∃ actual, Nonempty (Advanced core id actual) := by
  cases target
  · exact lower_at active id chosen allowed
  · exact upper_at active id chosen allowed
  · exact retry_at active id chosen allowed
  · exact ack_at active id chosen allowed

theorem Step.selected_drop (active : Active core) (id : Nat) (target : M.DropTarget)
    (chosen : CampusTCPTwoProgressMonitor.dropTarget (((cfg).at current.report.final).forward)
      current.report.final monitor.exchange.forward id = some target)
    (allowed : W.Allowed cfg current.report.final monitor (.dropPacket id))
    (actual : Step input) (before : actual.before = current.report.final) (event : actual.event = .dropPacket id) :
    Nonempty (Advanced core id actual) := by
  obtain ⟨enabled, ⟨value⟩⟩ := drop_at active id target chosen allowed
  have same := CampusTCPRoundPhaseBase.Step.eq_of_before_event enabled actual
    (value.drop.selected.appended.move.beforeEq.trans before.symm) (value.event.trans event.symm)
  exact ⟨same ▸ value⟩

end Netlib.Check.CampusTCPTwoTransferDropProgress
