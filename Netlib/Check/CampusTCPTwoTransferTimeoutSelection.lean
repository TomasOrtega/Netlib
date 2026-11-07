import Netlib.Check.CampusTCPTwoTransferTimeoutObserve

namespace Netlib.Check.CampusTCPTwoTransferTimeoutSelection

open CampusTCPModel

namespace M
export CampusTCPTwoProgressMonitor (Config Monitor Demand Allowed nextDemand laneDemand timerDemand)
end M
namespace G
export CampusTCPGapProgressMonitor (serves nextAction packetAt)
end G

private theorem action_not_timeout (action : CampusTCPRoundMonitor.Action) (actor : Actor) :
    Event.timeout actor true ≠ action.event := by
  cases action <;> intro impossible <;> cases impossible

private theorem lane_not_timeout (config : M.Config) (state : State input) (monitor : M.Monitor)
    (lane : CampusTCPTwoProgressMonitor.Lane) (selected : M.laneDemand config state monitor lane = some demand)
    (served : G.serves demand (.timeout actor true) = true) : False := by
  obtain ⟨action, next, operation | ⟨id, resolution⟩⟩ :=
    CampusTCPTwoProgressMonitorFacts.laneDemand_action _ _ _ _ selected
  · exact action_not_timeout action actor ((CampusTCPGapProgressMonitorFacts.serves_operation _ _).mp (operation ▸ served))
  · rcases (CampusTCPGapProgressMonitorFacts.serves_resolution _ _ _).mp (resolution ▸ served) with same | drop
    · exact action_not_timeout action actor same
    · cases drop

private theorem timer_actor (config : M.Config) (state : State input)
    (selected : M.timerDemand config state = some demand)
    (served : G.serves demand (.timeout actor true) = true) : actor = config.sender := by
  obtain ⟨recovery, head, rest, deadline, target, _, _, _, _, selected⟩ :=
    CampusTCPTwoProgressTimer.timerDemand_some selected
  rw [selected] at served
  split at served
  · have impossible := (CampusTCPGapProgressMonitorFacts.serves_tick _ _ _).mp served
    cases impossible
  · have same := (CampusTCPGapProgressMonitorFacts.serves_timeout _ _).mp served
    exact (Event.timeout.inj same).1

theorem allowed_timeout (config : M.Config) (state : State input) (monitor : M.Monitor)
    (allowed : M.Allowed config state monitor (.timeout actor true)) :
    monitor.mode = .recovery ∧ monitor.waiting = true ∧ actor = config.sender := by
  obtain ⟨_, chosen | dropped | free, _⟩ := (CampusTCPTwoProgressMonitorFacts.allowed_iff _ _ _ _).mp allowed
  · obtain ⟨demand, next, served⟩ := chosen
    cases mode : monitor.mode with
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
        · cases ack : monitor.ack with
          | some lane =>
            simp only [ack] at next
            cases selected : M.laneDemand config state monitor lane with
            | none => simp only [selected, Option.map_none] at next; cases next
            | some laneDemand =>
              simp only [selected, Option.map_some] at next
              cases next
              exact False.elim (lane_not_timeout config state monitor lane selected served)
          | none =>
            simp only [ack] at next
            split at next
            · cases next
              rcases CampusTCPTwoProgressMonitorFacts.originalChoice_branch _ _ _ served with lower | upper
              · obtain ⟨laneDemand, selected, served⟩ := lower
                exact False.elim (lane_not_timeout config state monitor monitor.lower selected served)
              · obtain ⟨laneDemand, selected, served⟩ := upper
                exact False.elim (lane_not_timeout config state monitor monitor.upper selected served)
            · cases next
    | recovery =>
      simp only [M.nextDemand, mode] at next
      cases ack : monitor.ack with
      | some lane =>
        simp only [ack] at next
        cases selected : M.laneDemand config state monitor lane with
        | none => simp only [selected, Option.map_none] at next; cases next
        | some laneDemand =>
          simp only [selected, Option.map_some] at next
          cases next
          exact False.elim (lane_not_timeout config state monitor lane selected served)
      | none =>
        simp only [ack] at next
        cases waiting : monitor.waiting with
        | false =>
          simp only [waiting, Bool.false_eq_true, ite_false] at next
          cases selected : M.laneDemand config state monitor monitor.retry with
          | none => simp only [selected, Option.map_none] at next; cases next
          | some laneDemand =>
            simp only [selected, Option.map_some] at next
            cases next
            exact False.elim (lane_not_timeout config state monitor monitor.retry selected served)
        | true =>
          simp only [waiting, ite_true] at next
          cases selected : M.timerDemand config state with
          | none => simp only [selected, Option.map_none] at next; cases next
          | some timer =>
            simp only [selected, Option.map_some] at next
            cases next
            exact ⟨rfl, rfl, timer_actor config state selected served⟩
  · obtain ⟨_, _, impossible, _⟩ := dropped
    cases impossible
  · obtain ⟨_, _, impossible, _⟩ := CampusTCPTwoProgressMonitorFacts.freeClock_event _ _ _ _ free
    cases impossible

end Netlib.Check.CampusTCPTwoTransferTimeoutSelection
