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
variable {produced : Produced input.active input.passive} {packetID : Nat} {target : M.DropTarget}

def keepAckState (active : Active core) (drop : P.Dropped core produced packetID target actual)
    {book : CampusTCPTwoProgressLossHistory.Book initial (config initial native quantum allowance)}
    (result : CampusTCPTwoProgressPhaseDrop.Result drop.selected book) (data : produced.actor = sender)
    (same : (M.observe (config initial native quantum allowance) monitor actual).ack = monitor.ack) : AckState result.next := by
  unfold AckState
  rw [same]
  cases found : monitor.ack with
  | none => exact PUnit.unit
  | some lane =>
    have before : AckWork core lane := by simpa only [AckState, found] using active.ack
    exact keepAckWork before drop result data

private theorem original_mode (active : Active core) (part : S.Part)
    (live : (match part with | .lower => monitor.lower | .upper => monitor.upper).phase ≠ .done) :
    monitor.mode = .originals := by
  rcases active.mode with mode | mode
  · exact mode
  · obtain ⟨first, second⟩ := active.recovery mode
    cases part
    · exact False.elim (live first)
    · exact False.elim (live second)

private def lower_lost (active : Active core) (drop : P.Dropped core produced packetID .lower actual)
    (credit : P.Credited drop .lower) (data : produced.actor = sender)
    (fields : CampusTCPTwoProgressWire.DataFields initial 0 lower produced) (live : monitor.lower.phase ≠ .done) :
    Active credit.result.next := by
  let raw := { monitor with drops := monitor.drops ++ [drop.item.id], lower := { monitor.lower with phase := .done } }
  have mode := original_mode active .lower live
  have shape : Scalar received raw := {
    mode := .inl mode
    originals := fun _ => active.originals mode
    recovery := fun impossible => by rw [mode] at impossible; cases impossible
    serial := active.serial, ackNonempty := active.ackNonempty, waiting := active.waiting }
  have normal := normalized active credit.result shape (observed_drop drop)
  have upperLane : OriginalLane initial native drop.selected.appended.move.after credit.result.next.live.gatewayState received .upper
      (M.observe (config initial native quantum allowance) monitor actual).upper := by
    rw [normal.upperLane]
    exact keepOriginalLane active.upperLane drop credit.result.next.live.gatewayState
      (fun other _ otherFields => CampusTCPTwoProgressPathsDistinct.produced_ne fields otherFields)
  have ackSame : (M.observe (config initial native quantum allowance) monitor actual).ack = monitor.ack := normal.ack
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
      | upper _ work => exact ⟨.upper rfl (CampusTCPTwoProgressPhaseNetworkState.OriginalLane.work upperLane (by
          rw [normal.upperLane]; exact work.not_done))⟩
      | retry work => exact False.elim (work.not_done (active.originals mode).1)
      | ack lane pending covered => exact ⟨.ack lane (ackSame.trans pending) covered⟩
  · intro retired missing done
    obtain ⟨position, chosen⟩ := active.upperMissing retired missing (by rw [normal.upperLane] at done; exact done)
    exact ⟨position, by rw [credit.result.bookEq]; exact chosen⟩
  · intro lane pending
    exact pending

private def upper_lost (active : Active core) (drop : P.Dropped core produced packetID .upper actual)
    (credit : P.Credited drop .upper) (data : produced.actor = sender)
    (fields : CampusTCPTwoProgressWire.DataFields initial lower.length upper produced) (live : monitor.upper.phase ≠ .done) :
    Active credit.result.next := by
  let raw := { monitor with drops := monitor.drops ++ [drop.item.id], upper := { monitor.upper with phase := .done } }
  have mode := original_mode active .upper live
  have shape : Scalar received raw := {
    mode := .inl mode
    originals := fun _ => active.originals mode
    recovery := fun impossible => by rw [mode] at impossible; cases impossible
    serial := active.serial, ackNonempty := active.ackNonempty, waiting := active.waiting }
  have normal := normalized active credit.result shape (observed_drop drop)
  have lowerLane : OriginalLane initial native drop.selected.appended.move.after credit.result.next.live.gatewayState received .lower
      (M.observe (config initial native quantum allowance) monitor actual).lower := by
    rw [normal.lowerLane]
    exact keepOriginalLane active.lowerLane drop credit.result.next.live.gatewayState
      (fun other _ otherFields => (CampusTCPTwoProgressPathsDistinct.produced_ne otherFields fields).symm)
  have ackSame : (M.observe (config initial native quantum allowance) monitor actual).ack = monitor.ack := normal.ack
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
      | lower _ work => exact ⟨.lower rfl (CampusTCPTwoProgressPhaseNetworkState.OriginalLane.work lowerLane (by
          rw [normal.lowerLane]; exact work.not_done))⟩
      | upper same _ => cases same
      | retry work => exact False.elim (work.not_done (active.originals mode).1)
      | ack lane pending covered => exact ⟨.ack lane (ackSame.trans pending) covered⟩
    | upper =>
      exact ⟨.cause core.losses.book.losses.length (by rw [credit.result.bookEq]; rfl)⟩
  · intro _ _ _
    exact ⟨core.losses.book.losses.length, by rw [credit.result.bookEq]; rfl⟩
  · intro lane pending
    exact pending

def lower_ingress (active : Active core) (path : DataIngress initial current .lower monitor.lower)
    (drop : P.Dropped core path.output.produced path.packetID .lower actual) (credit : P.Credited drop .lower) :
    Active credit.result.next :=
  lower_lost active drop credit path.output.actor path.output.fields (by rw [path.phase]; decide)

def lower_link (active : Active core) (path : DataLink initial current .lower monitor.lower)
    (drop : P.Dropped core path.served.ticket.value.produced path.packetID .lower actual) (credit : P.Credited drop .lower) :
    Active credit.result.next :=
  lower_lost active drop credit path.actor path.fields (by rw [path.phase]; decide)

def upper_ingress (active : Active core) (path : DataIngress initial current .upper monitor.upper)
    (drop : P.Dropped core path.output.produced path.packetID .upper actual) (credit : P.Credited drop .upper) :
    Active credit.result.next :=
  upper_lost active drop credit path.output.actor path.output.fields (by rw [path.phase]; decide)

def upper_link (active : Active core) (path : DataLink initial current .upper monitor.upper)
    (drop : P.Dropped core path.served.ticket.value.produced path.packetID .upper actual) (credit : P.Credited drop .upper) :
    Active credit.result.next :=
  upper_lost active drop credit path.actor path.fields (by rw [path.phase]; decide)

end Netlib.Check.CampusTCPTwoProgressPhaseDropState
