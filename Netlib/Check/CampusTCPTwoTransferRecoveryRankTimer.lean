import Netlib.Check.CampusTCPTwoTransferRecoveryRankClock
import Netlib.Check.CampusTCPTwoTransferTimeoutProgress

namespace Netlib.Check.CampusTCPTwoTransferRecoveryRankTimer

open Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart
open CampusTCPTwoTransferNative (Checks Routing)
open CampusTCPTwoTransferLocatedCore (Core config)
open CampusTCPTwoTransferPhaseState (Active)
open CampusTCPTwoTransferLocatedClock (Clocked)

namespace R
export CampusTCPTwoTransferRecoveryRank (rank sender_runtime sender_now active_waiting_credit)
end R
namespace K
export CampusTCPTwoProgressRecoveryRank (timerSlots work)
end K
namespace M
export CampusTCPTwoProgressMonitor (Lane nextDemand laneDemand timerDemand)
end M
namespace W
export CampusTCPTwoTransferMonitor (Monitor observe)
end W

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current : Cut input complete} {sender : Actor} {gateway location : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {checks : Checks cut initial.gatewayState.session.entry} {routing : Routing cut gateway}
variable {quantum allowance : Nat} {reverseLower reverseUpper : List UInt8}
variable {monitor : W.Monitor} {sent : CampusTCPTwoProgressSender.Stage initial} {received : CampusTCPTwoProgressReceiver.Stage}
variable {core : Core initial checks routing quantum allowance reverseLower reverseUpper current monitor location sent received}
variable {actor : Actor} {millis : Nat} {actual : Step input}

local notation "cfg" => config initial checks routing quantum allowance reverseLower reverseUpper

private theorem lane_not_tick (packetConfig : CampusTCPTwoProgressMonitor.Config) (state : State input)
    (localMonitor : CampusTCPTwoProgressMonitor.Monitor) (lane : M.Lane)
    (selected : M.laneDemand packetConfig state localMonitor lane = some (.tick actor millis)) : False := by
  obtain ⟨_, _, ordinary | ⟨_, resolution⟩⟩ := CampusTCPTwoProgressMonitorFacts.laneDemand_action _ _ _ _ selected
  · cases ordinary
  · cases resolution

theorem selected_tick (mode : monitor.exchange.forward.mode = .recovery)
    (next : M.nextDemand ((cfg).at current.report.final).forward current.report.final monitor.exchange.forward =
      some (.single (.tick actor millis))) :
    monitor.exchange.forward.waiting = true ∧ monitor.exchange.forward.ack = none ∧
      M.timerDemand ((cfg).at current.report.final).forward current.report.final = some (.tick actor millis) := by
  simp only [M.nextDemand, mode] at next
  cases pending : monitor.exchange.forward.ack with
  | some lane =>
    simp only [pending] at next
    cases chosen : M.laneDemand ((cfg).at current.report.final).forward current.report.final monitor.exchange.forward lane with
    | none => simp only [chosen, Option.map_none] at next; cases next
    | some demand =>
      have same : demand = .tick actor millis := by
        simpa only [chosen, Option.map_some, Option.some.injEq, CampusTCPTwoProgressMonitor.Demand.single.injEq] using next
      subst demand
      exact False.elim (lane_not_tick _ _ _ lane chosen)
  | none =>
    simp only [pending] at next
    cases waiting : monitor.exchange.forward.waiting with
    | false =>
      simp only [waiting, Bool.false_eq_true, ite_false] at next
      cases chosen : M.laneDemand ((cfg).at current.report.final).forward current.report.final monitor.exchange.forward monitor.exchange.forward.retry with
      | none => simp only [chosen, Option.map_none] at next; cases next
      | some demand =>
        have same : demand = .tick actor millis := by
          simpa only [chosen, Option.map_some, Option.some.injEq, CampusTCPTwoProgressMonitor.Demand.single.injEq] using next
        subst demand
        exact False.elim (lane_not_tick _ _ _ _ chosen)
    | true =>
      simp only [waiting, ite_true] at next
      cases chosen : M.timerDemand ((cfg).at current.report.final).forward current.report.final with
      | none => simp only [chosen, Option.map_none] at next; cases next
      | some demand =>
        have same : demand = .tick actor millis := by
          simpa only [chosen, Option.map_some, Option.some.injEq, CampusTCPTwoProgressMonitor.Demand.single.injEq] using next
        subst demand
        exact ⟨rfl, rfl, rfl⟩

theorem selected_tick_strict (active : Active core) (mode : monitor.exchange.forward.mode = .recovery)
    (bound : Nat) (positive : 0 < quantum) (clocked : Clocked core actor millis actual)
    (allowed : CampusTCPTwoTransferMonitor.Allowed cfg current.report.final monitor (.advanceClock actor millis))
    (next : M.nextDemand ((cfg).at current.report.final).forward current.report.final monitor.exchange.forward =
      some (.single (.tick actor millis))) :
    R.rank cfg bound allowance clocked.move.after.report.final (W.observe cfg monitor actual) <
      R.rank cfg bound allowance current.report.final monitor := by
  obtain ⟨waiting, _, pending⟩ := selected_tick mode next
  obtain ⟨recovery, _, _, _, target, runtime, timer, _, _, _, early, selectedActor, tick⟩ :=
    CampusTCPTwoProgressTimer.timerDemand_tick pending
  have same : recovery = core.live.senderFlight.recovery :=
    Option.some.inj (runtime.symm.trans (R.sender_runtime core))
  subst recovery
  have actorEq : actor = sender := selectedActor
  clear selectedActor
  subst actor
  have endpointFields := CampusTCPTwoTransferRecoveryRankClock.clock_endpoints active.exchange clocked allowed
  have time : clocked.next.live.senderFlight.recovery.now = min (core.live.senderFlight.recovery.now + quantum) target := by
    rw [← R.sender_now clocked.next, endpointFields.1, Endpoint.clockState_now _ _ core.live.senderFlight.runtime, tick]
    rfl
  have decrease : K.timerSlots (cfg).exchange.forward clocked.move.after.report.final <
      K.timerSlots (cfg).exchange.forward current.report.final := by
    rw [CampusTCPTwoProgressRecoveryRank.timerSlots_of_runtime _ _ _ (R.sender_runtime clocked.next),
      CampusTCPTwoProgressRecoveryRank.timerSlots_of_runtime _ _ _ (R.sender_runtime core)]
    exact CampusTCPTwoProgressTimer.clock_tick_slots_lt (clocked.placement.frame.endpointFrame sender)
      core.live.senderFlight.runtime clocked.next.live.senderFlight.runtime timer positive early time
  change CampusTCPTwoProgressRecoveryRank.rank _ _ _ _ _ < _
  rw [clocked.observed]
  exact CampusTCPTwoProgressRecoveryRank.waiting_step _ _ _ _ _ _ _ mode mode waiting waiting rfl decrease

theorem timeout_exact (active : Active core) (bound : Nat)
    {part : CampusTCPTwoProgressSender.Part} {head : Recovery.Outstanding} {rest : List Recovery.Outstanding} {position : Nat}
    (value : CampusTCPTwoTransferTimeoutProgress.Retried core part head rest position actual)
    (waiting : monitor.exchange.forward.waiting = true) :
    R.rank cfg bound allowance value.value.move.after.report.final (W.observe cfg monitor actual) + 1 =
      R.rank cfg bound allowance current.report.final monitor := by
  have mode := active.waiting_mode waiting
  have localAllowed := (CampusTCPTwoTransferTimeoutObserve.allowed_timeout_fields cfg current.report.final monitor sender
    (by rw [← value.value.facts.event]; exact value.allowed) active.exchange).2.2.2
  obtain ⟨target, timer, due⟩ := CampusTCPTwoTransferTimeoutProgress.due_of_allowed active waiting localAllowed
  have zero : K.timerSlots (cfg).exchange.forward current.report.final = 0 := by
    rw [CampusTCPTwoProgressRecoveryRank.timerSlots_of_runtime _ _ _ (R.sender_runtime core)]
    have remaining : CampusTCPTwoProgressTimer.remaining core.live.senderFlight.recovery = 0 := by
      rw [CampusTCPTwoProgressTimer.remaining_of_target timer]
      omega
    rw [CampusTCPTwoProgressTimer.slots, remaining]
    by_cases positive : 0 < quantum
    · exact CampusTCPRecoveryRoundMonitor.waitSlots_zero positive
    · have quantumZero : quantum = 0 := by omega
      change CampusTCPRecoveryRoundMonitor.waitSlots quantum 0 = 0
      rw [quantumZero]
      rfl
  change CampusTCPTwoProgressRecoveryRank.rank _ _ _ _ _ + 1 = _
  apply CampusTCPTwoProgressRecoveryRank.timeout_step _ _ _ _ _ _ _ mode
  · rw [value.observed]; exact mode
  · exact waiting
  · rw [value.observed]; rfl
  · rw [value.observed]; rfl
  · exact R.active_waiting_credit active waiting
  · exact zero
  · rw [value.observed]
    simp only [K.work, CampusTCPTwoTransferTimeoutObserve.afterTimeout, (active.waiting waiting).1,
      CampusTCPTwoTransferTimeoutObserve.ingressLane, CampusTCPTwoProgressOriginalRank.dataCost]

end Netlib.Check.CampusTCPTwoTransferRecoveryRankTimer
