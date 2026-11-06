import Netlib.Check.CampusTCPTwoExchangeBoundedMode
import Netlib.Check.CampusTCPTwoExchangeComplete
import Netlib.Check.CampusTCPTwoExchangePermissions
import Netlib.Check.CampusTCPTwoExchangeOrder
import Netlib.Check.CampusTCPTwoExchangeClockBound
import Netlib.Check.CampusTCPTwoExchangeActionCheck
import Netlib.Check.CampusTCPTwoExchangeServiceCheck

/-!
# Bounded completion of one actual two-way exchange

One service condition covers both legs and the intervening write.
The result retains the same report prefix and both completion histories.
-/

namespace Netlib.Check.CampusTCPTwoExchangeBounded

open Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart
open CampusTCPTwoExchangeSetup (config)

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut : Cut input complete} {sender : Actor} {gateway : Gateway} {lower upper : List UInt8}

abbrev boundSlots (initial : TwoWriteInitial cut sender gateway lower upper) (quantum allowance bound : Nat) : Nat :=
  CampusTCPTwoExchangeBoundSetup.boundSlots initial quantum allowance bound

structure Result (initial : TwoWriteInitial cut sender gateway lower upper)
    (native : NativeEnv cut gateway initial.gatewayState.session.entry) (quantum allowance bound : Nat)
    (reverseLower reverseUpper : List UInt8) (steps : List (Step input)) where
  current : Cut input complete
  final : current.report.final = CampusTCPSchedule.stateAt cut.report.final steps (boundSlots initial quantum allowance bound)
  history : current.report.steps = cut.report.steps ++ steps.take (boundSlots initial quantum allowance bound)
  value : CampusTCPTwoExchangeComplete.Complete initial native quantum allowance reverseLower reverseUpper current
    (CampusTCPTwoExchangeMonitor.monitorAt (config initial native quantum allowance reverseLower reverseUpper)
      .initial steps (boundSlots initial quantum allowance bound))

variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {native : NativeEnv cut gateway initial.gatewayState.session.entry} {quantum allowance bound : Nat}
variable {reverseLower reverseUpper : List UInt8}
variable {events remaining : List Event} {steps : List (Step input)} {final : State input}

def Result.monitor (_result : Result initial native quantum allowance bound reverseLower reverseUpper steps) :
    CampusTCPTwoExchangeMonitor.Monitor :=
  CampusTCPTwoExchangeMonitor.monitorAt (config initial native quantum allowance reverseLower reverseUpper)
    .initial steps (boundSlots initial quantum allowance bound)

private theorem monitorAt_take_length (cfg : CampusTCPTwoExchangeMonitor.Config)
    (monitor : CampusTCPTwoExchangeMonitor.Monitor) (steps : List (Step input)) (count : Nat) :
    CampusTCPTwoExchangeMonitor.monitorAt cfg monitor (steps.take count) (steps.take count).length =
      CampusTCPTwoExchangeMonitor.monitorAt cfg monitor steps count := by
  induction steps generalizing monitor count with
  | nil => simp only [List.take_nil, CampusTCPTwoExchangeMonitor.monitorAt]
  | cons actual rest ih =>
    cases count with
    | zero => rfl
    | succ count =>
      simpa only [List.take_succ_cons, List.length_cons, CampusTCPTwoExchangeMonitor.monitorAt] using
        ih (CampusTCPTwoExchangeMonitor.observe cfg monitor actual) count

theorem Result.mode (result : Result initial native quantum allowance bound reverseLower reverseUpper steps) :
    (CampusTCPTwoExchangeMonitor.monitorAt (config initial native quantum allowance reverseLower reverseUpper)
      .initial steps (boundSlots initial quantum allowance bound)).mode = .done := result.value.mode

theorem Result.counters (result : Result initial native quantum allowance bound reverseLower reverseUpper steps) :
    result.monitor.drops = (steps.take (boundSlots initial quantum allowance bound)).filterMap CampusTCPTwoProgressLossHistory.dropID ∧
      result.monitor.timeouts =
        ((steps.take (boundSlots initial quantum allowance bound)).filter CampusTCPTwoExchangeLoss.isTimeoutOutput).length ∧
      result.monitor.slots = (steps.take (boundSlots initial quantum allowance bound)).length := by
  let cfg := config initial native quantum allowance reverseLower reverseUpper
  have folded : (steps.take (boundSlots initial quantum allowance bound)).foldl
      (CampusTCPTwoExchangeMonitor.observe cfg) .initial = result.monitor := by
    rw [← CampusTCPTwoExchangeMonitor.monitorAt_length]
    exact monitorAt_take_length _ _ _ _
  have healthy : ((steps.take (boundSlots initial quantum allowance bound)).foldl
      (CampusTCPTwoExchangeMonitor.observe cfg) .initial).mode ≠ .invalid := by
    rw [folded]
    change (CampusTCPTwoExchangeMonitor.monitorAt cfg .initial steps (boundSlots initial quantum allowance bound)).mode ≠ .invalid
    rw [result.mode]
    decide
  have counters := CampusTCPTwoExchangeAccounting.initial_accounting cfg (steps.take (boundSlots initial quantum allowance bound)) healthy
  rw [folded] at counters
  exact counters

theorem Result.drop_ids (result : Result initial native quantum allowance bound reverseLower reverseUpper steps) :
    result.monitor.drops = result.monitor.forward.drops ++ result.monitor.reverse.drops := by
  have localIDs := result.value.drop_ids
  rw [← result.value.recorded_eq result.history] at localIDs
  exact result.counters.1.trans localIDs

theorem Result.budget (result : Result initial native quantum allowance bound reverseLower reverseUpper steps) :
    ((steps.take (boundSlots initial quantum allowance bound)).filter CampusTCPTwoExchangeLoss.isTimeoutOutput).length ≤
        ((steps.take (boundSlots initial quantum allowance bound)).filter CampusTCPTwoProgressLossHistory.isDrop).length ∧
      ((steps.take (boundSlots initial quantum allowance bound)).filter CampusTCPTwoProgressLossHistory.isDrop).length ≤ allowance :=
  result.value.recorded_budget result.history

theorem Result.forward_bytes (result : Result initial native quantum allowance bound reverseLower reverseUpper steps) :
    result.value.forward.completed.reader.result.read = lower ++ upper := result.value.forward.completed.returned

theorem Result.reverse_bytes (result : Result initial native quantum allowance bound reverseLower reverseUpper steps) :
    result.value.reverse.completed.reader.result.read = reverseLower ++ reverseUpper := result.value.reverse.completed.returned

theorem Result.reverse_writer_recorded (result : Result initial native quantum allowance bound reverseLower reverseUpper steps) :
    result.value.actual.result.application = some (sender.other, result.value.start.reverseInitial.write.writer) :=
  result.value.reverse_writer_recorded

theorem Result.reader_slots (result : Result initial native quantum allowance bound reverseLower reverseUpper steps) :
    ∃ forwardSlot writeSlot reverseSlot,
      forwardSlot < writeSlot ∧ writeSlot < reverseSlot ∧ reverseSlot < boundSlots initial quantum allowance bound ∧
        steps[forwardSlot]? = some result.value.forward.completed.reader ∧
        steps[writeSlot]? = some result.value.actual ∧ steps[reverseSlot]? = some result.value.reverse.completed.reader := by
  obtain ⟨f, w, r, fw, wr, within, first, write, last⟩ := result.value.reader_slots result.history
  have length : (steps.take (boundSlots initial quantum allowance bound)).length ≤ boundSlots initial quantum allowance bound :=
    List.length_take_le _ _
  have rWithin : r < boundSlots initial quantum allowance bound := by omega
  refine ⟨f, w, r, fw, wr, rWithin, ?_, ?_, ?_⟩
  · simpa only [List.getElem?_take, show f < boundSlots initial quantum allowance bound by omega, ite_true] using first
  · simpa only [List.getElem?_take, show w < boundSlots initial quantum allowance bound by omega, ite_true] using write
  · simpa only [List.getElem?_take, rWithin, ite_true] using last

theorem Result.final_idle (result : Result initial native quantum allowance bound reverseLower reverseUpper steps) (actor : Actor) :
    Nonempty (IdleEndpoint (endpoint result.current.endpoints actor)) := by
  have writer := CampusTCPTwoReverseEndpoints.sender_idle result.value.reverse.completed result.value.reverse.senderDuplicate
  have reader := CampusTCPTwoReverseEndpoints.receiver_idle result.value.reverse.completed
  cases sender <;> cases actor
  all_goals first | exact ⟨writer⟩ | exact ⟨reader⟩

theorem Result.forward_read_permissions (result : Result initial native quantum allowance bound reverseLower reverseUpper steps)
    (prior : cut.report.compliant = true) (index : Nat) (byte : UInt8) (selected : (lower ++ upper)[index]? = some byte) :
    ∃ origin : CampusTCPTwoProgressReadSuffix.SuffixReadOrigin result.value.forward.completed index byte,
      Nonempty (CampusTCPTwoProgressWriteOrigins.SelectedWriteOrigin initial origin.attempt origin.read.origin.localIndex byte) ∧
        CampusTCPRoundOrigins.ServicePermissions origin.delivery.service.joint.step origin.delivery.receive.receipt.served :=
  result.value.forward_read_permissions prior index byte selected

theorem Result.reverse_read_permissions (result : Result initial native quantum allowance bound reverseLower reverseUpper steps)
    (prior : cut.report.compliant = true) (index : Nat) (byte : UInt8)
    (selected : (reverseLower ++ reverseUpper)[index]? = some byte) :
    ∃ origin : CampusTCPTwoProgressReadSuffix.SuffixReadOrigin result.value.reverse.completed index byte,
      Nonempty (CampusTCPTwoProgressWriteOrigins.SelectedWriteOrigin result.value.start.reverseInitial
        origin.attempt origin.read.origin.localIndex byte) ∧
        CampusTCPRoundOrigins.ServicePermissions origin.delivery.service.joint.step origin.delivery.receive.receipt.served :=
  result.value.reverse_read_permissions prior index byte selected

theorem Result.now_le (result : Result initial native quantum allowance bound reverseLower reverseUpper steps)
    (budget : allowance ≤ 2)
    (endpointReserve : CampusTCPTwoReverseReserves.Initial initial reverseLower reverseUpper)
    (gatewayReserve : CampusTCPTwoReverseGeometry.Initial initial reverseLower reverseUpper)
    (lowerNonempty : reverseLower ≠ []) (upperNonempty : reverseUpper ≠ [])
    (trace : Trace input cut.report.final events steps final remaining)
    (actions : CampusTCPTwoExchangeRecorded.Actions initial native quantum allowance reverseLower reverseUpper steps)
    (enough : boundSlots initial quantum allowance bound ≤ steps.length) (actor : Actor) :
    (endpoint result.current.endpoints actor).now ≤ (endpoint cut.endpoints actor).now +
      boundSlots initial quantum allowance bound * quantum := by
  have clock := CampusTCPTwoExchangeClockBound.trace_now_le trace actions budget endpointReserve gatewayReserve
    lowerNonempty upperNonempty (boundSlots initial quantum allowance bound) enough actor
  rw [← result.final, CampusTCPTwoProgressSuffixAge.nowAt_cut] at clock
  exact clock

theorem complete_by (budget : allowance ≤ 2) (positive : 0 < quantum)
    (endpointReserve : CampusTCPTwoReverseReserves.Initial initial reverseLower reverseUpper)
    (gatewayReserve : CampusTCPTwoReverseGeometry.Initial initial reverseLower reverseUpper)
    (lowerNonempty : reverseLower ≠ []) (upperNonempty : reverseUpper ≠ [])
    (trace : Trace input cut.report.final events steps final remaining)
    (actions : CampusTCPTwoExchangeRecorded.Actions initial native quantum allowance reverseLower reverseUpper steps)
    (service : CampusTCPTwoExchangeMonitor.Serviced (config initial native quantum allowance reverseLower reverseUpper)
      cut.report.final .initial steps bound)
    (enough : boundSlots initial quantum allowance bound ≤ steps.length) :
    Nonempty (Result initial native quantum allowance bound reverseLower reverseUpper steps) := by
  have done := CampusTCPTwoExchangeBoundedMode.done_by budget positive endpointReserve gatewayReserve
    lowerNonempty upperNonempty trace actions service enough
  obtain ⟨current, same, history, ⟨evidence⟩⟩ := CampusTCPTwoExchangeRecorded.trace_at budget endpointReserve gatewayReserve
    lowerNonempty upperNonempty trace actions (boundSlots initial quantum allowance bound) enough
  obtain ⟨value⟩ := CampusTCPTwoExchangeComplete.of_done evidence done
  exact ⟨⟨current, same, history, value⟩⟩

theorem complete_by_checked (budget : allowance ≤ 2) (positive : 0 < quantum)
    (endpointReserve : CampusTCPTwoReverseReserves.Initial initial reverseLower reverseUpper)
    (gatewayReserve : CampusTCPTwoReverseGeometry.Initial initial reverseLower reverseUpper)
    (lowerNonempty : reverseLower ≠ []) (upperNonempty : reverseUpper ≠ [])
    (trace : Trace input cut.report.final events steps final remaining)
    (actions : CampusTCPTwoExchangeMonitor.actions (config initial native quantum allowance reverseLower reverseUpper)
      cut.report.final .initial steps = true)
    (service : CampusTCPTwoExchangeMonitor.check (config initial native quantum allowance reverseLower reverseUpper)
      cut.report.final .initial steps bound = true)
    (enough : boundSlots initial quantum allowance bound ≤ steps.length) :
    Nonempty (Result initial native quantum allowance bound reverseLower reverseUpper steps) :=
  complete_by budget positive endpointReserve gatewayReserve lowerNonempty upperNonempty trace
    ((CampusTCPTwoExchangeMonitor.actions_correct _ _ _ _).mp actions)
    ((CampusTCPTwoExchangeMonitor.check_correct _ _ _ _ _).mp service) enough

theorem complete_by_cached (budget : allowance ≤ 2) (positive : 0 < quantum)
    (endpointReserve : CampusTCPTwoReverseReserves.Initial initial reverseLower reverseUpper)
    (gatewayReserve : CampusTCPTwoReverseGeometry.Initial initial reverseLower reverseUpper)
    (lowerNonempty : reverseLower ≠ []) (upperNonempty : reverseUpper ≠ [])
    (trace : Trace input cut.report.final events steps final remaining)
    (actions : CampusTCPTwoExchangeActionCheck.actions (config initial native quantum allowance reverseLower reverseUpper)
      cut.report.final .initial steps = true)
    (service : CampusTCPTwoExchangeServiceCheck.check (config initial native quantum allowance reverseLower reverseUpper)
      cut.report.final .initial steps bound = true)
    (enough : boundSlots initial quantum allowance bound ≤ steps.length) :
    Nonempty (Result initial native quantum allowance bound reverseLower reverseUpper steps) :=
  complete_by budget positive endpointReserve gatewayReserve lowerNonempty upperNonempty trace
    ((CampusTCPTwoExchangeActionCheck.actions_correct _ _ _ _).mp actions)
    ((CampusTCPTwoExchangeServiceCheck.check_correct _ _ _ _ _).mp service) enough

end Netlib.Check.CampusTCPTwoExchangeBounded
