import Netlib.Check.CampusTCPTwoTransferReverseResult
import Netlib.Check.CampusTCPTwoTransferExchangeBound
import Netlib.Check.CampusTCPTwoTransferExchangeLossPositions
import Netlib.Check.CampusTCPTwoTransferControlTrace

/-!
# Bounded completion of the actual transfer exchange

One trace and one service condition supply both reads and the intervening write.
The result retains the same report, selected writers, permissions and loss budget.
-/

namespace Netlib.Check.CampusTCPTwoTransferExchangeResult

open Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart
open CampusTCPTwoTransferNative (Checks Routing)
open CampusTCPTwoTransferLocatedCore (config)
open CampusTCPTwoTransferForwardWriteBounded (ReadWrite)

namespace W
export CampusTCPTwoTransferMonitor (Monitor Allowed monitorAt actions check)
end W
namespace B
export CampusTCPTwoTransferExchangeBound (wholeSlots after_write_fits)
end B
namespace L
export CampusTCPTwoTransferExchangeLoss (recorded actual_global_ids actual_drop_steps timeout_le_drops drop_budget)
end L

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut : Cut input complete} {sender : Actor} {gateway : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {checks : Checks cut initial.gatewayState.session.entry} {routing : Routing cut gateway}
variable {quantum allowance bound : Nat} {reverseLower reverseUpper : List UInt8} {steps : List (Step input)}
variable {events remaining : List Event} {final : State input}

local notation "cfg" => config initial checks routing quantum allowance reverseLower reverseUpper

structure Result (initial : TwoWriteInitial cut sender gateway lower upper)
    (checks : Checks cut initial.gatewayState.session.entry) (routing : Routing cut gateway)
    (quantum allowance : Nat) (reverseLower reverseUpper : List UInt8) (bound : Nat) (steps : List (Step input)) where
  readWrite : ReadWrite initial checks routing quantum allowance reverseLower reverseUpper steps
  reverse : CampusTCPTwoTransferReverseResult.Result readWrite bound
  deadline : readWrite.writeSlot + 1 + CampusTCPTwoTransferReverseResult.legSlots readWrite bound ≤
    B.wholeSlots initial quantum allowance bound

variable (result : Result initial checks routing quantum allowance reverseLower reverseUpper bound steps)

def Result.slot : Nat := result.readWrite.writeSlot + 1 + CampusTCPTwoTransferReverseResult.legSlots result.readWrite bound

def Result.current : Cut input complete := result.reverse.point.current

def Result.monitor : W.Monitor := W.monitorAt cfg .initial steps result.slot

theorem Result.history : result.current.report.steps = cut.report.steps ++ steps.take result.slot := result.reverse.history

theorem Result.final_state : result.current.report.final = CampusTCPSchedule.stateAt cut.report.final steps result.slot := result.reverse.point.final

theorem Result.done : result.monitor.mode = .finished ∧ result.monitor.exchange.mode = .done :=
  ⟨result.reverse.point.value.finished, result.reverse.done⟩

theorem Result.standby_routing : Routing result.current .standby := result.reverse.point.currentRouting

theorem Result.recorded_eq : result.reverse.point.value.recorded.suffix = L.recorded result.readWrite result.reverse.mixed :=
  CampusTCPTwoTransferExchangeLoss.recorded_eq result.readWrite result.reverse.mixed result.reverse.point.value.recorded.history

theorem Result.accounting :
    result.monitor.exchange.drops = (L.recorded result.readWrite result.reverse.mixed).filterMap CampusTCPTwoProgressLossHistory.dropID ∧
      result.monitor.exchange.timeouts = ((L.recorded result.readWrite result.reverse.mixed).filter CampusTCPTwoExchangeLoss.isTimeoutOutput).length ∧
      result.monitor.exchange.slots = (L.recorded result.readWrite result.reverse.mixed).length := by
  have counters := result.reverse.point.value.recorded.accounting result.reverse.point.healthy
  rw [result.recorded_eq] at counters
  exact counters

theorem Result.shared_budget :
    result.monitor.exchange.timeouts ≤ result.monitor.exchange.drops.length ∧ result.monitor.exchange.drops.length ≤ allowance := by
  have identityCount : ((L.recorded result.readWrite result.reverse.mixed).filterMap CampusTCPTwoProgressLossHistory.dropID).length =
      ((L.recorded result.readWrite result.reverse.mixed).filter CampusTCPTwoProgressLossHistory.isDrop).length := by
    rw [L.actual_global_ids, L.actual_drop_steps, List.length_map, List.length_map]
  rw [result.accounting.1, result.accounting.2.1, identityCount]
  exact ⟨L.timeout_le_drops result.readWrite result.reverse.mixed, L.drop_budget result.readWrite result.reverse.mixed⟩

theorem Result.distinct_packet_ids : result.monitor.exchange.drops.Nodup := by
  rw [result.accounting.1]
  exact CampusTCPTwoTransferExchangeLoss.packet_ids_nodup result.readWrite result.reverse.mixed

theorem Result.read_order :
    ∃ slot, result.readWrite.readSlot < result.readWrite.writeSlot ∧ result.readWrite.writeSlot < slot ∧
      slot < B.wholeSlots initial quantum allowance bound ∧ steps[slot]? = some result.reverse.value.completed.reader := by
  obtain ⟨slot, afterWrite, before, reader⟩ := result.reverse.reader_slot
  exact ⟨slot, result.readWrite.ordered, afterWrite, Nat.lt_of_lt_of_le before result.deadline, reader⟩

theorem Result.streams :
    result.readWrite.read.actual.result.read = lower ++ upper ∧
      result.reverse.value.completed.reader.result.read = reverseLower ++ reverseUpper :=
  ⟨result.readWrite.read.advance.value.value.returned, result.reverse.read_bytes⟩

theorem Result.controls :
    result.monitor.controls.map (·.1) = [.pause, .capture, .install, .clientRoute, .serverRoute, .fence, .resume] :=
  CampusTCPTwoTransferControlTrace.finished_controls result.reverse.point.value.recorded result.done.1

theorem Result.clock_bound (actor : Actor) :
    (endpoint result.current.endpoints actor).now ≤
      (endpoint cut.endpoints actor).now + B.wholeSlots initial quantum allowance bound * quantum := by
  have bounded := result.reverse.point.value.recorded.clock_bound result.reverse.point.healthy actor
  have suffix : result.reverse.point.value.recorded.suffix = steps.take result.slot :=
    List.append_cancel_left (result.reverse.point.value.recorded.history.symm.trans result.history)
  have length : result.reverse.point.value.recorded.suffix.length ≤ B.wholeSlots initial quantum allowance bound := by
    rw [suffix, List.length_take]
    exact Nat.le_trans (Nat.min_le_left _ _) result.deadline
  rw [(result.reverse.point.value.recorded.accounting result.reverse.point.healthy).2.2,
    show (cfg).exchange.forward.quantum = quantum by rfl] at bounded
  exact Nat.le_trans bounded (Nat.add_le_add_left (Nat.mul_le_mul_right quantum length) _)

theorem complete_by
    (initial : TwoWriteInitial cut sender .primary lower upper)
    (checks : Checks cut initial.gatewayState.session.entry) (routing : Routing cut .primary)
    (quantum allowance : Nat) (reverseLower reverseUpper : List UInt8)
    (primaryEmpty : cut.report.final.outstanding .primary = 0)
    (targetEmpty : cut.report.final.standby.transport = Checkpoint.Gateway.initial)
    (targetNS : cut.report.final.standby.guard.source.ns = (input.deployment .standby).executionNS)
    (endpointReserve : CampusTCPTwoReverseReserves.Initial initial reverseLower reverseUpper)
    (gatewayReserve : CampusTCPTwoReverseGeometry.Initial initial reverseLower reverseUpper)
    (lowerNonempty : reverseLower ≠ []) (upperNonempty : reverseUpper ≠ [])
    (budget : allowance ≤ 2) (positive : 0 < quantum)
    (trace : Trace input cut.report.final events steps final remaining)
    (actions : W.actions (config initial checks routing quantum allowance reverseLower reverseUpper) cut.report.final .initial steps = true)
    (service : W.check (config initial checks routing quantum allowance reverseLower reverseUpper) cut.report.final .initial steps bound = true)
    (enough : B.wholeSlots initial quantum allowance bound ≤ steps.length) :
    Nonempty (Result initial checks routing quantum allowance reverseLower reverseUpper bound steps) := by
  have forwardWithin : CampusTCPTwoTransferForwardWriteBounded.boundSlots initial quantum allowance bound ≤ steps.length := by
    unfold B.wholeSlots at enough
    omega
  obtain ⟨rw, written⟩ := CampusTCPTwoTransferForwardWriteBounded.start_by initial checks routing quantum allowance
    reverseLower reverseUpper primaryEmpty targetEmpty targetNS endpointReserve gatewayReserve lowerNonempty upperNonempty
    budget positive trace actions service forwardWithin
  have deadline := B.after_write_fits rw written
    ((W.monitorAt (config initial checks routing quantum allowance reverseLower reverseUpper) .initial steps rw.writeSlot).exchange.forward.drops.length)
  have reverseWithin : rw.writeSlot + 1 + CampusTCPTwoTransferReverseResult.legSlots rw bound ≤ steps.length :=
    Nat.le_trans deadline enough
  obtain ⟨reverse⟩ := CampusTCPTwoTransferReverseResult.complete_by_checked rw budget positive trace actions service reverseWithin
  exact ⟨⟨rw, reverse, deadline⟩⟩

end Netlib.Check.CampusTCPTwoTransferExchangeResult
