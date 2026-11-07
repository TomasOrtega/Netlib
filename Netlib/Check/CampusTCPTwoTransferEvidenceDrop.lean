import Netlib.Check.CampusTCPTwoTransferEvidence
import Netlib.Check.CampusTCPTwoTransferDropProgress
import Netlib.Check.CampusTCPTwoTransferOrdinaryPhase

namespace Netlib.Check.CampusTCPTwoTransferEvidence

open Protocol Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart
open CampusTCPTwoTransferNative (Checks Routing)
open CampusTCPTwoTransferLocatedCore (Core config)

namespace M
export CampusTCPTwoProgressMonitor (Config Monitor Demand DropTarget Allowed nextDemand serves laneDemand exposedPacket dropTarget timerDemand)
end M
namespace F
export CampusTCPTwoProgressMonitorFacts (allowed_iff)
end F
namespace G
export CampusTCPGapProgressMonitor (Demand serves nextAction packetAt senderRecovery)
end G
namespace DP
export CampusTCPTwoTransferDropProgress (Advanced)
end DP

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current : Cut input complete} {sender : Actor} {gateway location : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {checks : Checks cut initial.gatewayState.session.entry} {routing : Routing cut gateway}
variable {quantum allowance : Nat} {reverseLower reverseUpper : List UInt8}
variable {monitor : W.Monitor} {actual : Step input} {id : Nat}

local notation "cfg" => config initial checks routing quantum allowance reverseLower reverseUpper

private theorem action_not_drop (action : CampusTCPRoundMonitor.Action) (id : Nat) : Event.dropPacket id ≠ action.event := by
  cases action <;> intro impossible <;> cases impossible

private theorem lane_drop (packetConfig : M.Config) (state : State input) (value : M.Monitor) (lane : CampusTCPTwoProgressMonitor.Lane)
    (selected : M.laneDemand packetConfig state value lane = some demand) (served : G.serves demand (.dropPacket id) = true) :
    value.drops.length < packetConfig.lossAllowance ∧ M.exposedPacket packetConfig state lane = some id := by
  unfold M.laneDemand at selected
  cases next : G.nextAction packetConfig.toConfig state lane.toGap with
  | none => simp only [next, bind, Option.bind] at selected; cases selected
  | some action =>
    simp only [next, bind, Option.bind] at selected
    cases packet : G.packetAt lane.toGap with
    | none =>
      have same : demand = .operation action := by simpa only [packet, pure, Option.some.injEq] using selected.symm
      exact False.elim (action_not_drop action id ((CampusTCPGapProgressMonitorFacts.serves_operation _ _).mp (same ▸ served)))
    | some packetID =>
      simp only [packet] at selected
      split at selected
      · rename_i budget
        have same : demand = .resolution action packetID := (Option.some.inj selected).symm
        rcases (CampusTCPGapProgressMonitorFacts.serves_resolution action packetID (.dropPacket id)).mp (same ▸ served) with ordinary | drop
        · exact False.elim (action_not_drop action id ordinary)
        · have identity := Event.dropPacket.inj drop
          exact ⟨budget, by simp only [M.exposedPacket, next, bind, Option.bind, packet]; exact congrArg some identity.symm⟩
      · have same : demand = .operation action := (Option.some.inj selected).symm
        exact False.elim (action_not_drop action id ((CampusTCPGapProgressMonitorFacts.serves_operation _ _).mp (same ▸ served)))

private theorem target_exists (packetConfig : M.Config) (state : State input) (value : M.Monitor)
    (mode : value.mode = .originals ∨ value.mode = .recovery) (budget : value.drops.length < packetConfig.lossAllowance)
    (exposed : M.exposedPacket packetConfig state value.lower = some id ∨
      M.exposedPacket packetConfig state value.upper = some id ∨
      M.exposedPacket packetConfig state value.retry = some id ∨
      ∃ lane, value.ack = some lane ∧ M.exposedPacket packetConfig state lane = some id) :
    ∃ target, M.dropTarget packetConfig state value id = some target := by
  have valid : (value.mode == .originals || value.mode == .recovery) = true := by
    rcases mode with mode | mode <;> rw [mode] <;> rfl
  unfold M.dropTarget
  rw [valid]
  simp only [ite_true, ite_eq_left budget]
  by_cases lower : M.exposedPacket packetConfig state value.lower = some id
  · exact ⟨.lower, by simp only [lower, beq_self_eq_true, ite_true]⟩
  · by_cases upper : M.exposedPacket packetConfig state value.upper = some id
    · exact ⟨.upper, by simp only [beq_iff_eq, lower, upper, ite_false, ite_true]⟩
    · by_cases retry : M.exposedPacket packetConfig state value.retry = some id
      · exact ⟨.retry, by simp only [beq_iff_eq, lower, upper, retry, ite_false, ite_true]⟩
      · obtain ⟨lane, pending, packet⟩ := exposed.resolve_left lower |>.resolve_left upper |>.resolve_left retry
        exact ⟨.ack, by simp only [beq_iff_eq, lower, upper, retry, ite_false, pending, packet, ite_true]⟩

private theorem timer_not_drop (packetConfig : M.Config) (state : State input)
    (selected : M.timerDemand packetConfig state = some demand) : G.serves demand (.dropPacket id) = false := by
  unfold M.timerDemand at selected
  cases runtime : G.senderRecovery packetConfig.toConfig state with
  | none => simp only [runtime, bind, Option.bind] at selected; cases selected
  | some recovery =>
    simp only [runtime, bind, Option.bind] at selected
    cases target : CampusTCPTwoProgressMonitor.timerTarget recovery with
    | none => simp only [target] at selected; cases selected
    | some millis =>
      simp only [target] at selected
      split at selected <;> cases selected <;> rfl

theorem local_allowed_drop_target (packetConfig : M.Config) (state : State input) (value : M.Monitor)
    (allowed : M.Allowed packetConfig state value (.dropPacket id)) :
    ∃ target, M.dropTarget packetConfig state value id = some target := by
  obtain ⟨_, chosen | dropped | free, _⟩ := (F.allowed_iff _ _ _ _).mp allowed
  · obtain ⟨demand, next, served⟩ := chosen
    cases mode : value.mode with
    | invalid | done => simp only [M.nextDemand, mode] at next; cases next
    | needRead =>
      simp only [M.nextDemand, mode] at next
      cases next
      cases served
    | originals =>
      simp only [M.nextDemand, mode] at next
      split at next
      · cases next; cases served
      · split at next
        · cases next; cases served
        · cases ack : value.ack with
          | some lane =>
            simp only [ack] at next
            cases selected : M.laneDemand packetConfig state value lane with
            | none => simp only [selected, Option.map_none] at next; cases next
            | some laneDemand =>
              simp only [selected, Option.map_some] at next
              cases next
              obtain ⟨budget, exposed⟩ := lane_drop packetConfig state value lane selected served
              exact target_exists packetConfig state value (.inl mode) budget (.inr (.inr (.inr ⟨lane, ack, exposed⟩)))
          | none =>
            simp only [ack] at next
            split at next
            · cases next
              rcases CampusTCPTwoProgressMonitorFacts.originalChoice_branch _ _ _ served with lower | upper
              · obtain ⟨laneDemand, selected, served⟩ := lower
                obtain ⟨budget, exposed⟩ := lane_drop packetConfig state value value.lower selected served
                exact target_exists packetConfig state value (.inl mode) budget (.inl exposed)
              · obtain ⟨laneDemand, selected, served⟩ := upper
                obtain ⟨budget, exposed⟩ := lane_drop packetConfig state value value.upper selected served
                exact target_exists packetConfig state value (.inl mode) budget (.inr (.inl exposed))
            · cases next
    | recovery =>
      simp only [M.nextDemand, mode] at next
      cases ack : value.ack with
      | some lane =>
        simp only [ack] at next
        cases selected : M.laneDemand packetConfig state value lane with
        | none => simp only [selected, Option.map_none] at next; cases next
        | some laneDemand =>
          simp only [selected, Option.map_some] at next
          cases next
          obtain ⟨budget, exposed⟩ := lane_drop packetConfig state value lane selected served
          exact target_exists packetConfig state value (.inr mode) budget (.inr (.inr (.inr ⟨lane, ack, exposed⟩)))
      | none =>
        simp only [ack] at next
        split at next
        · cases selected : M.timerDemand packetConfig state with
          | none => simp only [selected, Option.map_none] at next; cases next
          | some timer =>
            simp only [selected, Option.map_some] at next
            cases next
            change G.serves timer (.dropPacket id) = true at served
            rw [timer_not_drop packetConfig state selected] at served
            cases served
        · cases selected : M.laneDemand packetConfig state value value.retry with
          | none => simp only [selected, Option.map_none] at next; cases next
          | some laneDemand =>
            simp only [selected, Option.map_some] at next
            cases next
            obtain ⟨budget, exposed⟩ := lane_drop packetConfig state value value.retry selected served
            exact target_exists packetConfig state value (.inr mode) budget (.inr (.inr (.inl exposed)))
  · obtain ⟨other, target, same, selected⟩ := dropped
    exact ⟨target, (Event.dropPacket.inj same) ▸ selected⟩
  · obtain ⟨_, _, impossible, _⟩ := CampusTCPTwoProgressMonitorFacts.freeClock_event _ _ _ _ free
    cases impossible

theorem armed_unresolved (exchange : monitor.exchange.mode = .forward) (original : monitor.exchange.forward.mode = .originals)
    (ordinary : W.controlDemand monitor = none) (armed : monitor.mode = .armed) :
    monitor.exchange.forward.lower.phase ≠ .done ∧ monitor.exchange.forward.upper.phase ≠ .done := by
  have unresolved : ¬(monitor.exchange.forward.lower.phase = .done ∨ monitor.exchange.forward.upper.phase = .done) := by
    intro resolved
    have due := (show CampusTCPTwoTransferScope.TransferScope monitor from ⟨exchange, original, resolved⟩).due
    simp only [W.controlDemand, armed, due, ite_true] at ordinary
    cases ordinary
  exact ⟨fun lower => unresolved (.inl lower), fun upper => unresolved (.inr upper)⟩

private theorem inactive_exposed (packetConfig : M.Config) (state : State input) (lane : CampusTCPTwoProgressMonitor.Lane)
    (phase : lane.phase = .needSend ∨ lane.phase = .done) : M.exposedPacket packetConfig state lane = none := by
  rcases phase with phase | phase <;>
    simp only [M.exposedPacket, G.nextAction, CampusTCPTwoProgressMonitor.Lane.toGap, phase, bind, Option.bind]

variable {sent : S.Stage initial} {received : R.Stage}
variable {core : Core initial checks routing quantum allowance reverseLower reverseUpper current monitor location sent received}

private theorem active_empty (active : A.Active core)
    (lower : monitor.exchange.forward.lower.phase ≠ .done) (upper : monitor.exchange.forward.upper.phase ≠ .done) :
    received = .empty := by
  cases received with
  | empty => rfl
  | upperHeld =>
    cases active.upperLane with
    | done phase => exact False.elim (upper phase)
    | active _ missing => exact False.elim (missing trivial)
  | lowerReleased | allReleased =>
    cases active.lowerLane with
    | done phase => exact False.elim (lower phase)
    | active _ missing => exact False.elim (missing trivial)

theorem armed_drop_original (active : A.Active core)
    (original : monitor.exchange.forward.mode = .originals) (ordinary : W.controlDemand monitor = none)
    (armed : monitor.mode = .armed) (value : DP.Advanced core id actual) :
    (W.observe cfg monitor actual).exchange.forward.mode = .originals := by
  obtain ⟨lower, upper⟩ := armed_unresolved active.exchange original ordinary armed
  have empty := active_empty active lower upper
  have noAck : monitor.exchange.forward.ack = none := by
    cases pending : monitor.exchange.forward.ack with
    | none => rfl
    | some lane => exact False.elim (active.ackNonempty (by rw [pending]; rfl) empty)
  have retry := (active.originals original).1
  have chosen := value.drop.selected.selected
  have observed := value.drop.selected.local_observed
  cases target : value.target with
  | lower =>
    rw [observed]
    simp (config := { zetaHave := true }) only [CampusTCPTwoTransferLocatedDrop.rawDrop, target,
      CampusTCPTwoProgressMonitor.normalize, original, CampusTCPTwoProgressMonitorFacts.phase_beq,
      upper, decide_false, Bool.and_false, Bool.false_eq_true, ite_false]
  | upper =>
    rw [observed]
    simp (config := { zetaHave := true }) only [CampusTCPTwoTransferLocatedDrop.rawDrop, target,
      CampusTCPTwoProgressMonitor.normalize, original, CampusTCPTwoProgressMonitorFacts.phase_beq,
      lower, decide_false, Bool.false_and, Bool.and_false, Bool.false_eq_true, ite_false]
  | retry =>
    have selected : M.dropTarget (((cfg).at current.report.final).forward) current.report.final monitor.exchange.forward
        value.drop.item.id = some .retry := by simpa only [target] using chosen
    have exposed := CampusTCPTwoProgressMonitorFacts.dropTarget_packet _ _ _ _ selected
    rw [inactive_exposed _ _ _ (.inr retry)] at exposed
    cases exposed
  | ack =>
    have selected : M.dropTarget (((cfg).at current.report.final).forward) current.report.final monitor.exchange.forward
        value.drop.item.id = some .ack := by simpa only [target] using chosen
    obtain ⟨lane, pending, _⟩ := CampusTCPTwoProgressMonitorFacts.dropTarget_packet _ _ _ _ selected
    rw [noAck] at pending
    cases pending

private theorem pending_drop_target
    {first : S.Original initial .lower}
    (state : P.PendingUpper initial checks routing quantum allowance reverseLower reverseUpper current monitor location first)
    (chosen : M.dropTarget (((cfg).at current.report.final).forward) current.report.final monitor.exchange.forward id = some target) :
    target = .lower ∧ monitor.exchange.forward.lower.phase = .dataIngress := by
  have exposed := CampusTCPTwoProgressMonitorFacts.dropTarget_packet _ _ _ _ chosen
  cases target with
  | lower =>
    refine ⟨rfl, ?_⟩
    cases state.lowerPath with
    | ingress path _ => exact path.phase
    | lost phase _ _ _ _ _ => rw [inactive_exposed _ _ _ (.inr phase)] at exposed; cases exposed
  | upper => rw [inactive_exposed _ _ _ (.inl state.upperPending)] at exposed; cases exposed
  | retry => rw [inactive_exposed _ _ _ (.inr state.retry)] at exposed; cases exposed
  | ack => obtain ⟨lane, pending, _⟩ := exposed; rw [state.ack] at pending; cases pending

private theorem ordinary_scope (controls : C.Phase current.report.final monitor.mode location)
    (ordinary : W.controlDemand monitor = none) (updated : W.Monitor) (mode : updated.mode = monitor.mode) : Scoped updated := by
  intro armed finished
  rcases controls.ordinary_modes ordinary with first | last
  · exact False.elim (armed (mode.trans first))
  · exact False.elim (finished (mode.trans last))

variable (evidence : Evidence initial checks routing quantum allowance reverseLower reverseUpper current monitor location)

include evidence in
theorem Evidence.drop_target (allowed : W.Allowed cfg current.report.final monitor (.dropPacket id)) :
    ∃ target, M.dropTarget (((cfg).at current.report.final).forward) current.report.final monitor.exchange.forward id = some target := by
  have fields := CampusTCPTwoTransferDropObserve.allowed_drop_fields allowed evidence.forward.exchange
  exact local_allowed_drop_target _ _ _ fields.2.2.2

theorem Evidence.drop_step (actual : Step input) (before : actual.before = current.report.final)
    (event : actual.event = .dropPacket id) (allowed : W.Allowed cfg current.report.final monitor actual.event) :
    Nonempty (Advanced evidence actual) := by
  have dropAllowed : W.Allowed cfg current.report.final monitor (.dropPacket id) := by rw [← event]; exact allowed
  have fields := CampusTCPTwoTransferDropObserve.allowed_drop_fields dropAllowed evidence.forward.exchange
  have ordinary := fields.2.2.1
  obtain ⟨target, chosen⟩ := evidence.drop_target dropAllowed
  rcases evidence with ⟨sent, received, core, forward, controls, scope, armed, recorded⟩
  cases forward with
  | written state =>
    have exposed := CampusTCPTwoProgressMonitorFacts.dropTarget_packet _ _ _ _ chosen
    cases target with
    | lower => rw [inactive_exposed _ _ _ (.inl state.lowerPending)] at exposed; cases exposed
    | upper => rw [inactive_exposed _ _ _ (.inl state.upperPending)] at exposed; cases exposed
    | retry => rw [inactive_exposed _ _ _ (.inr state.retry)] at exposed; cases exposed
    | ack => obtain ⟨lane, pending, _⟩ := exposed; rw [state.ack] at pending; cases pending
  | pending state =>
    obtain ⟨same, pending⟩ := pending_drop_target state chosen
    subst target
    obtain ⟨value⟩ := state.lower_drop_step pending chosen dropAllowed actual before event
    have nextMode : (W.observe cfg monitor actual).mode = monitor.mode := by rw [value.observed]; rfl
    have nextControls : C.Phase value.selected.appended.move.after.report.final (W.observe cfg monitor actual).mode location := by
      rw [nextMode]
      exact controls.nonservice ordinary value.selected.appended.move (by rw [event]; trivial)
    exact ⟨{
      move := value.selected.appended.move, location
      next := {
        sent := _, received := .empty, core := value.next.core, forward := .pending value.next
        controls := nextControls
        scope := ordinary_scope controls ordinary _ nextMode
        armed := by intro _; rw [value.observed]; exact state.mode
        recorded := recorded.snoc value.selected.appended.move allowed } }⟩
  | active state =>
    obtain ⟨value⟩ := CampusTCPTwoTransferDropProgress.Step.selected_drop state id target chosen dropAllowed actual before event
    have nextMode : (W.observe cfg monitor actual).mode = monitor.mode := by rw [value.drop.selected.observed]; rfl
    have nextControls : C.Phase value.drop.selected.appended.move.after.report.final (W.observe cfg monitor actual).mode location := by
      rw [nextMode]
      exact controls.nonservice ordinary value.drop.selected.appended.move (by rw [event]; trivial)
    exact ⟨{
      move := value.drop.selected.appended.move, location
      next := {
        sent := _, received := _, core := value.result.next, forward := .active value.active
        controls := nextControls
        scope := ordinary_scope controls ordinary _ nextMode
        armed := fun nextArmed => by
          have oldArmed := nextMode.symm.trans nextArmed
          exact armed_drop_original state (armed oldArmed) ordinary oldArmed value
        recorded := recorded.snoc value.drop.selected.appended.move allowed } }⟩
  | readable core exchange mode sources _ _ =>
    have valid := CampusTCPTwoTransferDropObserve.drop_mode chosen
    rw [mode] at valid
    rcases valid with impossible | impossible <;> cases impossible

end Netlib.Check.CampusTCPTwoTransferEvidence
