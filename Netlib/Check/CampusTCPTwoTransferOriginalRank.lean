import Netlib.Check.CampusTCPTwoTransferEvidenceHandoff
import Netlib.Check.CampusTCPTwoProgressOriginalRank

/-!
# Original work and reserved transfer work

Current typed paths provide the original rank shape.
The rank reserves transfer work before the first control demand.
-/

namespace Netlib.Check.CampusTCPTwoTransferOriginalRank

open Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart
open CampusTCPTwoTransferNative (Checks Routing)
open CampusTCPTwoTransferLocatedCore (Core config)
open CampusTCPTwoTransferEvidence (Evidence Forward)
open CampusTCPTwoTransferWork (OriginalLane AckWork AckState)

namespace O
export CampusTCPTwoProgressOriginalRank
  (RankShape DataPhase RetryPhase AckPhase dataCost ackCost ackWork originalRank)
end O
namespace B
export CampusTCPTwoTransferControlBound (potential remainingControls)
end B
namespace W
export CampusTCPTwoTransferMonitor (Monitor)
end W
namespace S
export CampusTCPTwoProgressSender (Stage Part)
end S
namespace R
export CampusTCPTwoProgressReceiver (Stage)
end R

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current : Cut input complete} {sender : Actor} {gateway location : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {checks : Checks cut initial.gatewayState.session.entry} {routing : Routing cut gateway}
variable {quantum allowance : Nat} {reverseLower reverseUpper : List UInt8}
variable {monitor : W.Monitor} {sent : S.Stage initial} {received : R.Stage}
variable {core : Core initial checks routing quantum allowance reverseLower reverseUpper current monitor location sent received}

private theorem original_phase {part : S.Part} {lane : CampusTCPTwoProgressMonitor.Lane}
    (path : OriginalLane initial checks current core.live.gatewayState received part lane) : O.DataPhase lane.phase := by
  cases path with
  | active work _ =>
    cases work with
    | ingress path _ => exact .inr (.inl path.phase)
    | ticket path _ _ => exact .inr (.inr (.inl path.phase))
    | link path _ _ => exact .inr (.inr (.inr (.inl path.phase)))
  | done phase => exact .inr (.inr (.inr (.inr phase)))

private theorem original_cost {part : S.Part} {lane : CampusTCPTwoProgressMonitor.Lane}
    (path : OriginalLane initial checks current core.live.gatewayState received part lane) : O.dataCost lane.phase ≤ 7 := by
  cases path with
  | active work _ =>
    cases work with
    | ingress path _ => rw [path.phase]; decide
    | ticket path _ _ => rw [path.phase]; decide
    | link path _ _ => rw [path.phase]; decide
  | done phase => rw [phase]; decide

private theorem ack_phase (active : CampusTCPTwoTransferPhaseState.Active core)
    (selected : monitor.exchange.forward.ack = some lane) : O.AckPhase lane.phase := by
  have work : AckWork checks core.live lane := by simpa only [AckState, selected] using active.ack
  cases work with
  | pending phase _ => exact .inl phase
  | ingress path => exact .inr (.inl path.phase)
  | ticket path _ => exact .inr (.inr (.inl path.phase))
  | link path => exact .inr (.inr (.inr path.phase))

private theorem ack_resolved (active : CampusTCPTwoTransferPhaseState.Active core)
    (selected : monitor.exchange.forward.ack = some lane) :
    monitor.exchange.forward.lower.phase = .done ∨ monitor.exchange.forward.upper.phase = .done := by
  have nonempty := active.ackNonempty (by rw [selected]; rfl)
  cases received with
  | empty => exact False.elim (nonempty rfl)
  | upperHeld =>
    right
    cases active.upperLane with
    | active _ missing => exact False.elim (missing trivial)
    | done phase => exact phase
  | lowerReleased | allReleased =>
    left
    cases active.lowerLane with
    | active _ missing => exact False.elim (missing trivial)
    | done phase => exact phase

theorem shape (evidence : Evidence initial checks routing quantum allowance reverseLower reverseUpper current monitor location)
    (mode : monitor.exchange.forward.mode = .originals) : O.RankShape monitor.exchange.forward := by
  rcases evidence with ⟨sent, received, core, forward, controls, scope, armed, recorded⟩
  cases forward with
  | written state =>
    exact {
      lower := .inl state.lowerPending, upper := .inl state.upperPending
      retry := .inr (.inr (.inr state.retry)), originalRetry := fun _ => state.retry
      ack := by intro lane selected; rw [state.ack] at selected; cases selected
      handoff := by intro different; exact False.elim (different mode) }
  | pending state =>
    have lowerPhase : O.DataPhase monitor.exchange.forward.lower.phase := by
      rcases state.lowerPath.phase with ingress | done
      · exact .inr (.inl ingress)
      · exact .inr (.inr (.inr (.inr done)))
    exact {
      lower := lowerPhase, upper := .inl state.upperPending
      retry := .inr (.inr (.inr state.retry)), originalRetry := fun _ => state.retry
      ack := by intro lane selected; rw [state.ack] at selected; cases selected
      handoff := by intro different; exact False.elim (different mode) }
  | active active =>
    have retry := (active.originals mode).1
    exact ⟨original_phase active.lowerLane, original_phase active.upperLane, .inr (.inr (.inr retry)),
      fun _ => retry, fun _ selected => ack_phase active selected,
      by intro different; exact False.elim (different mode)⟩
  | readable _ _ ready _ _ _ => rw [ready] at mode; cases mode

private theorem active_local_bound (active : CampusTCPTwoTransferPhaseState.Active core)
    (mode : monitor.exchange.forward.mode = .originals) : O.originalRank monitor.exchange.forward ≤ 16 := by
  have lowerCost := original_cost active.lowerLane
  have upperCost := original_cost active.upperLane
  rw [O.originalRank, mode]
  cases selected : monitor.exchange.forward.ack with
  | none => simp only [O.ackWork]; omega
  | some lane =>
    have ackCost : O.ackCost lane.phase ≤ 4 := by
      rcases ack_phase active selected with phase | phase | phase | phase <;> rw [phase] <;> decide
    simp only [O.ackWork]
    rcases ack_resolved active selected with done | done
    · rw [done]
      change 0 + O.dataCost monitor.exchange.forward.upper.phase + O.ackCost lane.phase ≤ 16
      omega
    · rw [done]
      change O.dataCost monitor.exchange.forward.lower.phase + 0 + O.ackCost lane.phase ≤ 16
      omega

theorem local_bound (evidence : Evidence initial checks routing quantum allowance reverseLower reverseUpper current monitor location) :
    O.originalRank monitor.exchange.forward ≤ 16 := by
  by_cases mode : monitor.exchange.forward.mode = .originals
  · rcases evidence with ⟨sent, received, core, forward, controls, scope, armed, recorded⟩
    cases forward with
    | written state => rw [O.originalRank, mode, state.lowerPending, state.upperPending, state.ack]; decide
    | pending state =>
      rw [O.originalRank, mode, state.upperPending, state.ack]
      rcases state.lowerPath.phase with phase | phase <;> rw [phase] <;> decide
    | active active => exact active_local_bound active mode
    | readable _ _ ready _ _ _ => rw [ready] at mode; cases mode
  · rw [CampusTCPTwoProgressOriginalRank.rank_zero_of_nonoriginal mode]
    decide

theorem local_positive (evidence : Evidence initial checks routing quantum allowance reverseLower reverseUpper current monitor location)
    (mode : monitor.exchange.forward.mode = .originals) : 0 < O.originalRank monitor.exchange.forward := by
  by_cases positive : 0 < O.originalRank monitor.exchange.forward
  · exact positive
  · have zero : O.originalRank monitor.exchange.forward = 0 := by omega
    have resolved := CampusTCPTwoProgressOriginalRank.zero_resolved (shape evidence mode) (by rw [mode]; decide) zero
    rcases evidence with ⟨sent, received, core, forward, controls, scope, armed, recorded⟩
    cases forward with
    | written state => rw [state.lowerPending] at resolved; cases resolved.1
    | pending state => rw [state.upperPending] at resolved; cases resolved.2.1
    | active active => exact False.elim (active.originalOpen mode (resolved.2.2 mode) ⟨resolved.1, resolved.2.1⟩)
    | readable _ _ ready _ _ _ => rw [ready] at mode; cases mode

def reserve (state : State input) (monitor : W.Monitor) : Nat :=
  match monitor.mode with
  | .armed => 8
  | .finished | .invalid => 0
  | _ => B.potential state monitor

def rank (state : State input) (monitor : W.Monitor) : Nat :=
  if monitor.mode ≠ .invalid ∧ monitor.exchange.mode = .forward ∧ monitor.exchange.forward.mode = .originals then
    O.originalRank monitor.exchange.forward + reserve state monitor
  else 0

theorem initial_rank (state : State input) : rank state .initial = 24 := rfl

theorem reserve_bound (evidence : Evidence initial checks routing quantum allowance reverseLower reverseUpper current monitor location) :
    reserve current.report.final monitor ≤ 8 := by
  cases mode : monitor.mode with
  | armed | finished | invalid => simp only [reserve, mode]; decide
  | capture | install | clientRoute | serverRoute | fence | resume =>
    have scope := evidence.scope (by rw [mode]; decide) (by rw [mode]; decide)
    have queue := scope.primary_count evidence.core
    simp only [reserve, mode, B.potential, B.remainingControls, reduceCtorEq, or_self, ite_false]
    all_goals omega

theorem current_rank (evidence : Evidence initial checks routing quantum allowance reverseLower reverseUpper current monitor location)
    (mode : monitor.exchange.forward.mode = .originals) :
    rank current.report.final monitor = O.originalRank monitor.exchange.forward + reserve current.report.final monitor := by
  rw [rank, ite_eq_left ⟨evidence.healthy, evidence.forward.exchange, mode⟩]

theorem bound (evidence : Evidence initial checks routing quantum allowance reverseLower reverseUpper current monitor location) :
    rank current.report.final monitor ≤ 24 := by
  have original := local_bound evidence
  have transfer := reserve_bound evidence
  unfold rank
  split <;> omega

theorem positive (evidence : Evidence initial checks routing quantum allowance reverseLower reverseUpper current monitor location)
    (mode : monitor.exchange.forward.mode = .originals) : 0 < rank current.report.final monitor := by
  rw [current_rank evidence mode]
  have original := local_positive evidence mode
  omega

theorem zero_iff (evidence : Evidence initial checks routing quantum allowance reverseLower reverseUpper current monitor location) :
    rank current.report.final monitor = 0 ↔ monitor.exchange.forward.mode ≠ .originals := by
  constructor
  · intro zero mode
    have positive := positive evidence mode
    omega
  · intro mode
    simp only [rank, mode, and_false, ite_false]

end Netlib.Check.CampusTCPTwoTransferOriginalRank
