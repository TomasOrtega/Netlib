import Netlib.Check.CampusTCPTwoProgressMonitorFacts
import Netlib.Check.CampusTCPTwoTransferMonitor

/-!
# Actual send selection from the current monitor

Only an unsent original can select a send operation.
Packet lanes, ACK work, and recovery timers cannot select one.
-/

namespace Netlib.Check.CampusTCPTwoTransferSendSelection

open CampusTCPModel CampusTCPEnabled

namespace M
export CampusTCPTwoProgressMonitor (Config Monitor Lane Demand Allowed nextDemand laneDemand timerDemand serves servesOption)
end M
namespace G
export CampusTCPGapProgressMonitor (Demand serves nextAction)
end G
namespace F
export CampusTCPTwoProgressMonitorFacts (allowed_iff freeClock_event laneDemand_action serves_operation)
end F
namespace A
export CampusTCPRoundMonitor (Action actionOf)
end A

variable {input : Input} {state : State input} {config : M.Config} {monitor : M.Monitor}
variable {actor : Actor} {count : Nat}

private theorem nextAction_not_send (config : CampusTCPGapProgressMonitor.Config) (state : State input)
    (lane : CampusTCPGapProgressMonitor.Monitor) (actor : Actor) (count : Nat) :
    G.nextAction config state lane ≠ some (.send actor count true) := by
  intro selected
  cases phase : lane.phase <;>
    simp only [G.nextAction, phase, CampusTCPRoundMonitor.ingressAction, CampusTCPRoundMonitor.ticketAction,
      CampusTCPRoundMonitor.linkAction] at selected
  all_goals repeat' first
    | (solve | cases selected)
    | (split at selected)
    | (dsimp only [bind, Option.bind, pure, Pure.pure] at selected)

private theorem lane_not_send (config : M.Config) (state : State input) (monitor : M.Monitor) (lane : M.Lane)
    (actor : Actor) (count : Nat) : M.servesOption (M.laneDemand config state monitor lane) (.send actor count true) ≠ true := by
  intro served
  obtain ⟨demand, selected, served⟩ := (CampusTCPTwoProgressMonitorFacts.servesOption_iff _ _).mp served
  obtain ⟨action, next, shape⟩ := F.laneDemand_action config state monitor lane selected
  have event : .send actor count true = action.event := by
    rcases shape with operation | ⟨id, resolution⟩
    · subst demand
      exact (CampusTCPGapProgressMonitorFacts.serves_operation action _).mp served
    · subst demand
      rcases (CampusTCPGapProgressMonitorFacts.serves_resolution action id _).mp served with ordinary | dropped
      · exact ordinary
      · cases dropped
  have same : action = .send actor count true := by cases action <;> cases event; rfl
  rw [same] at next
  exact nextAction_not_send _ _ _ _ _ next

private theorem timer_not_send (config : M.Config) (state : State input) (actor : Actor) (count : Nat) :
    M.servesOption (M.timerDemand config state) (.send actor count true) ≠ true := by
  unfold M.timerDemand
  cases recovery : CampusTCPGapProgressMonitor.senderRecovery config.toConfig state with
  | none => simp [M.servesOption]
  | some value =>
    cases target : CampusTCPTwoProgressMonitor.timerTarget value with
    | none => simp [target, M.servesOption]
    | some bound =>
      simp only [target, bind, Option.bind]
      split <;> simp [M.servesOption, G.serves]

theorem local_send (allowed : M.Allowed config state monitor (.send actor count true)) :
    monitor.mode = .originals ∧
      ((monitor.lower.phase = .needSend ∧ actor = config.sender ∧ count = config.lowerCount) ∨
        (monitor.lower.phase ≠ .needSend ∧ monitor.upper.phase = .needSend ∧
          actor = config.sender ∧ count = config.upperCount)) := by
  obtain ⟨_, selected | dropped | free, _⟩ := (F.allowed_iff config state monitor (.send actor count true)).mp allowed
  · obtain ⟨demand, pending, served⟩ := selected
    cases mode : monitor.mode with
    | originals =>
      simp only [M.nextDemand, mode] at pending
      split at pending
      · rename_i lowerReady
        have same : demand = .single (.operation (.send config.sender config.lowerCount true)) :=
          (Option.some.inj pending).symm
        subst demand
        have fields := Event.send.inj ((F.serves_operation _ _).mp served)
        exact ⟨rfl, Or.inl ⟨by simpa only [CampusTCPTwoProgressMonitorFacts.phase_beq, decide_eq_true_eq] using lowerReady, fields.1, fields.2.1⟩⟩
      · rename_i lowerAbsent
        split at pending
        · rename_i upperReady
          have same : demand = .single (.operation (.send config.sender config.upperCount true)) :=
            (Option.some.inj pending).symm
          subst demand
          have fields := Event.send.inj ((F.serves_operation _ _).mp served)
          exact ⟨rfl, Or.inr ⟨by simpa only [CampusTCPTwoProgressMonitorFacts.phase_beq, decide_eq_true_eq] using lowerAbsent,
            by simpa only [CampusTCPTwoProgressMonitorFacts.phase_beq, decide_eq_true_eq] using upperReady, fields.1, fields.2.1⟩⟩
        · cases ack : monitor.ack with
          | some lane =>
            simp only [ack] at pending
            cases chosen : M.laneDemand config state monitor lane with
            | none => simp [chosen] at pending
            | some item =>
              have same : demand = .single item := by simpa only [chosen, Option.map_some, Option.some.injEq] using pending.symm
              subst demand
              exact False.elim (lane_not_send config state monitor lane actor count (by simpa only [chosen, M.servesOption, M.serves] using served))
          | none =>
            simp only [ack] at pending
            split at pending
            · have same : demand = .originalChoice (M.laneDemand config state monitor monitor.lower)
                  (M.laneDemand config state monitor monitor.upper) := (Option.some.inj pending).symm
              subst demand
              rcases (CampusTCPTwoProgressMonitorFacts.serves_originalChoice _ _ _).mp served with lower | upper
              · exact False.elim (lane_not_send _ _ _ _ _ _ lower)
              · exact False.elim (lane_not_send _ _ _ _ _ _ upper)
            · cases pending
    | recovery =>
      simp only [M.nextDemand, mode] at pending
      cases ack : monitor.ack with
      | some lane =>
        simp only [ack] at pending
        cases chosen : M.laneDemand config state monitor lane with
        | none => simp [chosen] at pending
        | some item =>
          have same : demand = .single item := by simpa only [chosen, Option.map_some, Option.some.injEq] using pending.symm
          subst demand
          exact False.elim (lane_not_send config state monitor lane actor count (by simpa only [chosen, M.servesOption, M.serves] using served))
      | none =>
        simp only [ack] at pending
        split at pending
        · cases chosen : M.timerDemand config state with
          | none => simp [chosen] at pending
          | some item =>
            have same : demand = .single item := by simpa only [chosen, Option.map_some, Option.some.injEq] using pending.symm
            subst demand
            exact False.elim (timer_not_send config state actor count (by simpa only [chosen, M.servesOption, M.serves] using served))
        · cases chosen : M.laneDemand config state monitor monitor.retry with
          | none => simp [chosen] at pending
          | some item =>
            have same : demand = .single item := by simpa only [chosen, Option.map_some, Option.some.injEq] using pending.symm
            subst demand
            exact False.elim (lane_not_send config state monitor monitor.retry actor count (by simpa only [chosen, M.servesOption, M.serves] using served))
    | needRead =>
      simp only [M.nextDemand, mode, Option.some.injEq] at pending
      subst demand
      have impossible := (F.serves_operation _ _).mp served
      cases impossible
    | done | invalid => simp only [M.nextDemand, mode] at pending; cases pending
  · obtain ⟨id, target, event, _⟩ := dropped
    cases event
  · obtain ⟨actor, millis, event, _⟩ := F.freeClock_event config state monitor _ free
    cases event

end Netlib.Check.CampusTCPTwoTransferSendSelection
