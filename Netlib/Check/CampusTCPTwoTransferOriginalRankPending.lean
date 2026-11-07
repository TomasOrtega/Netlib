import Netlib.Check.CampusTCPTwoTransferOriginalRank

/-!
# Current original demands and actual clock persistence

Typed work supplies a present command. Transfer controls and primary drain keep
priority, and an actual clock keeps the same whole demand.
-/

namespace Netlib.Check.CampusTCPTwoTransferOriginalRank

open Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart
open CampusTCPTwoTransferNative (Checks Routing)
open CampusTCPTwoTransferLocatedCore (config)
open CampusTCPTwoTransferEvidence (Evidence)
open CampusTCPTwoTransferWork (DataWork OriginalLane AckWork AckState)

namespace T
export CampusTCPTwoTransferMonitor (Monitor Demand nextDemand controlDemand drainTicket observe)
end T
namespace M
export CampusTCPTwoProgressMonitor (Config Monitor Lane Demand nextDemand laneDemand)
end M
namespace G
export CampusTCPGapProgressMonitor (Demand nextAction packetAt)
end G

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current : Cut input complete} {sender : Actor} {gateway location : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {checks : Checks cut initial.gatewayState.session.entry} {routing : Routing cut gateway}
variable {quantum allowance : Nat} {reverseLower reverseUpper : List UInt8}
variable {monitor : T.Monitor} {actual : Step input} {actor : Actor} {millis : Nat}

local notation "cfg" => config initial checks routing quantum allowance reverseLower reverseUpper

private theorem lane_pending (packetConfig : M.Config) (state : State input) (localMonitor : M.Monitor) (lane : M.Lane)
    (action : CampusTCPRoundMonitor.Action) (present : G.nextAction packetConfig.toConfig state lane.toGap = some action) :
    ∃ demand, M.laneDemand packetConfig state localMonitor lane = some demand := by
  unfold M.laneDemand
  rw [present]
  simp only [bind, Option.bind]
  cases packet : G.packetAt lane.toGap with
  | none => exact ⟨.operation action, rfl⟩
  | some id =>
    by_cases budget : localMonitor.drops.length < packetConfig.lossAllowance
    · exact ⟨.resolution action id, by dsimp only; rw [ite_eq_left budget]; rfl⟩
    · exact ⟨.operation action, by dsimp only; rw [ite_eq_right budget]; rfl⟩

private theorem local_pending
    (evidence : Evidence initial checks routing quantum allowance reverseLower reverseUpper current monitor location)
    (mode : monitor.exchange.forward.mode = .originals) :
    ∃ demand, M.nextDemand ((cfg).at current.report.final).forward current.report.final monitor.exchange.forward = some demand := by
  let packetConfig := ((cfg).at current.report.final).forward
  change ∃ demand, M.nextDemand packetConfig current.report.final monitor.exchange.forward = some demand
  rcases evidence with ⟨sent, received, core, forward, controls, scope, armed, recorded⟩
  cases forward with
  | written state =>
    exact ⟨.single (.operation (.send packetConfig.sender packetConfig.lowerCount true)), by
      simp only [M.nextDemand, state.mode, state.lowerPending,
        show (CampusTCPRoundMonitor.Phase.needSend == .needSend) = true by rfl, ite_true]⟩
  | pending state =>
    have first : monitor.exchange.forward.lower.phase ≠ .needSend := by
      rcases state.lowerPath.phase with ingress | done
      · rw [ingress]; decide
      · rw [done]; decide
    exact ⟨.single (.operation (.send packetConfig.sender packetConfig.upperCount true)), by
      simp only [M.nextDemand, state.mode, (CampusTCPTwoProgressMonitorFacts.phase_beq_false _ _).mpr first,
        Bool.false_eq_true, ite_false, state.upperPending,
        show (CampusTCPRoundMonitor.Phase.needSend == .needSend) = true by rfl, ite_true]⟩
  | active active =>
    have first := active.lower_not_needSend
    have second := active.upper_not_needSend
    cases ack : monitor.exchange.forward.ack with
    | some lane =>
      have work : AckWork checks core.live lane := by simpa only [AckState, ack] using active.ack
      obtain ⟨demand, selected⟩ := lane_pending packetConfig current.report.final monitor.exchange.forward lane _ (work.command_next packetConfig)
      exact ⟨.single demand, by
        simp only [M.nextDemand, mode, (CampusTCPTwoProgressMonitorFacts.phase_beq_false _ _).mpr first,
          (CampusTCPTwoProgressMonitorFacts.phase_beq_false _ _).mpr second, Bool.false_eq_true, ite_false,
          ack, selected, Option.map_some]⟩
    | none =>
      have available : ((M.laneDemand packetConfig current.report.final monitor.exchange.forward monitor.exchange.forward.lower).isSome ||
          (M.laneDemand packetConfig current.report.final monitor.exchange.forward monitor.exchange.forward.upper).isSome) = true := by
        by_cases lowerDone : monitor.exchange.forward.lower.phase = .done
        · have upperOpen : monitor.exchange.forward.upper.phase ≠ .done := fun upperDone => active.originalOpen mode ack ⟨lowerDone, upperDone⟩
          let work := active.upperLane.work upperOpen
          obtain ⟨demand, selected⟩ := lane_pending packetConfig current.report.final monitor.exchange.forward _ _ (work.command_next packetConfig)
          rw [selected]
          exact Bool.or_true _
        · let work := active.lowerLane.work lowerDone
          obtain ⟨demand, selected⟩ := lane_pending packetConfig current.report.final monitor.exchange.forward _ _ (work.command_next packetConfig)
          rw [selected]
          rfl
      exact ⟨.originalChoice (M.laneDemand packetConfig current.report.final monitor.exchange.forward monitor.exchange.forward.lower)
        (M.laneDemand packetConfig current.report.final monitor.exchange.forward monitor.exchange.forward.upper), by
          simp only [M.nextDemand, mode, (CampusTCPTwoProgressMonitorFacts.phase_beq_false _ _).mpr first,
            (CampusTCPTwoProgressMonitorFacts.phase_beq_false _ _).mpr second, Bool.false_eq_true, ite_false,
            ack, available, ite_true]⟩
  | readable _ _ ready _ _ _ => rw [ready] at mode; cases mode

theorem pending
    (evidence : Evidence initial checks routing quantum allowance reverseLower reverseUpper current monitor location)
    (mode : monitor.exchange.forward.mode = .originals) :
    ∃ demand, T.nextDemand cfg current.report.final monitor = some demand := by
  have valid := evidence.healthy
  simp only [T.nextDemand, valid, decide_false, Bool.false_eq_true, ite_false]
  cases drain : T.drainTicket current.report.final monitor with
  | some ticket => exact ⟨.drain ticket, rfl⟩
  | none =>
    cases selected : T.controlDemand monitor with
    | some control => exact ⟨.transfer control, rfl⟩
    | none =>
      obtain ⟨demand, selected⟩ := local_pending evidence mode
      exact ⟨.exchange (.forward demand), by
        simp only [CampusTCPTwoExchangeMonitor.nextDemand, evidence.forward.exchange, selected, Option.map_some]⟩

private theorem lane_clock (frame : CampusTCPTimedClock.Frame before endpoints after updated)
    (packetConfig : M.Config) (localMonitor : M.Monitor) (lane : M.Lane) :
    M.laneDemand packetConfig after localMonitor lane = M.laneDemand packetConfig before localMonitor lane := by
  unfold M.laneDemand
  rw [CampusTCPGapProgressMonitorFacts.Frame.nextAction frame packetConfig.toConfig lane.toGap]

private theorem local_clock (frame : CampusTCPTimedClock.Frame before endpoints after updated)
    (packetConfig : M.Config) (localMonitor : M.Monitor) (mode : localMonitor.mode = .originals) :
    M.nextDemand packetConfig after localMonitor = M.nextDemand packetConfig before localMonitor := by
  simp only [M.nextDemand, mode]
  split
  · rfl
  · split
    · rfl
    · cases ack : localMonitor.ack with
      | none => dsimp only; rw [lane_clock frame packetConfig localMonitor localMonitor.lower, lane_clock frame packetConfig localMonitor localMonitor.upper]
      | some lane => dsimp only; rw [lane_clock frame packetConfig localMonitor lane]

theorem clock_pending
    (evidence : Evidence initial checks routing quantum allowance reverseLower reverseUpper current monitor location)
    (clocked : CampusTCPTwoTransferLocatedClock.Clocked evidence.core actor millis actual)
    (mode : monitor.exchange.forward.mode = .originals) :
    T.nextDemand cfg clocked.move.after.report.final (T.observe cfg monitor actual) = T.nextDemand cfg current.report.final monitor := by
  have configuration : (cfg).at clocked.move.after.report.final = (cfg).at current.report.final := by
    simp only [CampusTCPTwoTransferMonitor.Config.at, State.owner, clocked.placement.frame.owners]
  have demand := local_clock clocked.placement.frame ((cfg).at current.report.final).forward monitor.exchange.forward mode
  have drained : T.drainTicket clocked.move.after.report.final (T.observe cfg monitor actual) = T.drainTicket current.report.final monitor := by
    rw [clocked.observed]
    simp only [T.drainTicket, clocked.placement.frame.work]
  have control : T.controlDemand (T.observe cfg monitor actual) = T.controlDemand monitor := by rw [clocked.observed]; rfl
  have valid := evidence.healthy
  unfold T.nextDemand
  rw [drained, control]
  simp only [clocked.observed, valid, decide_false, Bool.false_eq_true, ite_false]
  cases T.drainTicket current.report.final monitor with
  | some ticket => rfl
  | none =>
    cases T.controlDemand monitor with
    | some control => rfl
    | none =>
      rw [configuration]
      simp only [CampusTCPTwoExchangeMonitor.nextDemand, evidence.forward.exchange]
      rw [demand]

end Netlib.Check.CampusTCPTwoTransferOriginalRank
