import Netlib.Check.CampusTCPTwoProgressPhaseNetworkState
import Netlib.Check.CampusTCPTwoProgressEvidenceHop

namespace Netlib.Check.CampusTCPTwoProgressEvidence

open Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart CampusTCPTwoProgressPhaseBase
open CampusTCPTwoProgressPhaseState
open CampusTCPTwoProgressSetup (config)

namespace C
export CampusTCPTwoProgressMonitor (Lane Demand Allowed nextDemand laneDemand exposedPacket dropTarget servesOption)
end C
namespace G
export CampusTCPGapProgressMonitor (Demand nextAction packetAt serves)
end G
namespace F
export CampusTCPTwoProgressMonitorFacts (allowed_iff freeClock_event phase_beq_false laneDemand_action
  serves_operation serves_resolution serves_timeout serves_tick servesOption_iff serves_originalChoice)
end F

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current : Cut input complete} {sender : Actor} {gateway : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {native : NativeEnv cut gateway initial.gatewayState.session.entry} {quantum allowance : Nat}
variable {monitor : M.Monitor} {sent : S.Stage initial} {received : R.Stage}
variable {core : Core initial native quantum allowance current monitor sent received} {event : Event}
variable {demand : C.Demand} {laneDemand : G.Demand} {lane : C.Lane} {id : Nat}

private inductive Selection (initial : TwoWriteInitial cut sender gateway lower upper)
    (native : NativeEnv cut gateway initial.gatewayState.session.entry) (quantum allowance : Nat)
    (current : Cut input complete) (monitor : M.Monitor) (event : Event) : Prop where
  | lower (demand : G.Demand) (mode : monitor.mode = .originals) (ack : monitor.ack = none)
      (selected : C.laneDemand (config initial native quantum allowance) current.report.final monitor monitor.lower = some demand)
      (served : G.serves demand event = true)
  | upper (demand : G.Demand) (mode : monitor.mode = .originals) (ack : monitor.ack = none)
      (first : C.servesOption (C.laneDemand (config initial native quantum allowance) current.report.final monitor monitor.lower) event = false)
      (selected : C.laneDemand (config initial native quantum allowance) current.report.final monitor monitor.upper = some demand)
      (served : G.serves demand event = true)
  | ack (lane : C.Lane) (demand : G.Demand) (pending : monitor.ack = some lane)
      (selected : C.laneDemand (config initial native quantum allowance) current.report.final monitor lane = some demand)
      (served : G.serves demand event = true)
  | retry (demand : G.Demand) (mode : monitor.mode = .recovery) (ack : monitor.ack = none) (waiting : monitor.waiting = false)
      (selected : C.laneDemand (config initial native quantum allowance) current.report.final monitor monitor.retry = some demand)
      (served : G.serves demand event = true)
  | timer (demand : G.Demand) (mode : monitor.mode = .recovery) (ack : monitor.ack = none) (waiting : monitor.waiting = true)
      (selected : CampusTCPTwoProgressMonitor.timerDemand (config initial native quantum allowance) current.report.final = some demand)
      (next : C.nextDemand (config initial native quantum allowance) current.report.final monitor = some (.single demand))
      (served : G.serves demand event = true)

private theorem selection (active : Active core)
    (next : C.nextDemand (config initial native quantum allowance) current.report.final monitor = some demand)
    (served : CampusTCPTwoProgressMonitor.serves demand event = true) :
    Selection initial native quantum allowance current monitor event := by
  have first := CampusTCPTwoProgressPhaseNetworkState.OriginalLane.not_needSend active.lowerLane
  have second := CampusTCPTwoProgressPhaseNetworkState.OriginalLane.not_needSend active.upperLane
  rcases active.mode with mode | mode
  · have selected := next
    simp only [C.nextDemand, mode, (F.phase_beq_false _ _).mpr first, (F.phase_beq_false _ _).mpr second,
      Bool.false_eq_true, ite_false] at selected
    cases ack : monitor.ack with
    | some lane =>
      simp only [ack] at selected
      cases pending : C.laneDemand (config initial native quantum allowance) current.report.final monitor lane with
      | none => simp only [pending, Option.map_none] at selected; cases selected
      | some chosen =>
        have same : (.single chosen : C.Demand) = demand := by simpa only [pending, Option.map_some, Option.some.injEq] using selected
        subst demand
        exact .ack lane chosen ack pending served
    | none =>
      simp only [ack] at selected
      split at selected
      · have same := Option.some.inj selected
        subst demand
        have choices := (F.serves_originalChoice _ _ _).mp served
        by_cases lower : C.servesOption (C.laneDemand (config initial native quantum allowance) current.report.final monitor monitor.lower) event = true
        · obtain ⟨chosen, pending, served⟩ := (F.servesOption_iff _ _).mp lower
          exact .lower chosen mode ack pending served
        · have upper := choices.resolve_left lower
          obtain ⟨chosen, pending, served⟩ := (F.servesOption_iff _ _).mp upper
          exact .upper chosen mode ack (Bool.eq_false_iff.mpr lower) pending served
      · cases selected
  · have selected := next
    simp only [C.nextDemand, mode] at selected
    cases ack : monitor.ack with
    | some lane =>
      simp only [ack] at selected
      cases pending : C.laneDemand (config initial native quantum allowance) current.report.final monitor lane with
      | none => simp only [pending, Option.map_none] at selected; cases selected
      | some chosen =>
        have same : (.single chosen : C.Demand) = demand := by simpa only [pending, Option.map_some, Option.some.injEq] using selected
        subst demand
        exact .ack lane chosen ack pending served
    | none =>
      simp only [ack] at selected
      cases waiting : monitor.waiting with
      | false =>
        simp only [waiting, Bool.false_eq_true, ite_false] at selected
        cases pending : C.laneDemand (config initial native quantum allowance) current.report.final monitor monitor.retry with
        | none => simp only [pending, Option.map_none] at selected; cases selected
        | some chosen =>
          have same : (.single chosen : C.Demand) = demand := by simpa only [pending, Option.map_some, Option.some.injEq] using selected
          subst demand
          exact .retry chosen mode ack waiting pending served
      | true =>
        simp only [waiting, ite_true] at selected
        cases pending : CampusTCPTwoProgressMonitor.timerDemand (config initial native quantum allowance) current.report.final with
        | none => simp only [pending, Option.map_none] at selected; cases selected
        | some chosen =>
          have same : (.single chosen : C.Demand) = demand := by simpa only [pending, Option.map_some, Option.some.injEq] using selected
          subst demand
          exact .timer chosen mode ack waiting pending next served

inductive ActionChoice (initial : TwoWriteInitial cut sender gateway lower upper)
    (native : NativeEnv cut gateway initial.gatewayState.session.entry) (quantum allowance : Nat)
    (current : Cut input complete) (monitor : M.Monitor) (event : Event) : Prop where
  | lower (action : CampusTCPRoundMonitor.Action) (mode : monitor.mode = .originals) (ack : monitor.ack = none)
      (next : G.nextAction (config initial native quantum allowance).toConfig current.report.final monitor.lower.toGap = some action)
      (selected : event = action.event)
  | upper (action : CampusTCPRoundMonitor.Action) (mode : monitor.mode = .originals) (ack : monitor.ack = none)
      (first : C.servesOption (C.laneDemand (config initial native quantum allowance) current.report.final monitor monitor.lower) event = false)
      (next : G.nextAction (config initial native quantum allowance).toConfig current.report.final monitor.upper.toGap = some action)
      (selected : event = action.event)
  | ack (lane : C.Lane) (action : CampusTCPRoundMonitor.Action) (pending : monitor.ack = some lane)
      (next : G.nextAction (config initial native quantum allowance).toConfig current.report.final lane.toGap = some action)
      (selected : event = action.event)
  | retry (action : CampusTCPRoundMonitor.Action) (mode : monitor.mode = .recovery) (ack : monitor.ack = none) (waiting : monitor.waiting = false)
      (next : G.nextAction (config initial native quantum allowance).toConfig current.report.final monitor.retry.toGap = some action)
      (selected : event = action.event)
  | timeout (mode : monitor.mode = .recovery) (ack : monitor.ack = none) (waiting : monitor.waiting = true)
      (next : C.nextDemand (config initial native quantum allowance) current.report.final monitor = some (.single (.timeout sender)))
      (selected : event = .timeout sender true)

private theorem lane_action
    (selected : C.laneDemand (config initial native quantum allowance) current.report.final monitor lane = some laneDemand)
    (served : G.serves laneDemand event = true) (nonDrop : ∀ id, event ≠ .dropPacket id) :
    ∃ action, G.nextAction (config initial native quantum allowance).toConfig current.report.final lane.toGap = some action ∧ event = action.event := by
  obtain ⟨action, next, operation | ⟨id, resolution⟩⟩ := F.laneDemand_action _ _ _ _ selected
  · exact ⟨action, next, (F.serves_operation action event).mp (operation ▸ served)⟩
  · rcases (F.serves_resolution action id event).mp (resolution ▸ served) with same | drop
    · exact ⟨action, next, same⟩
    · exact False.elim (nonDrop id drop)

private theorem timer_event
    (pending : CampusTCPTwoProgressMonitor.timerDemand (config initial native quantum allowance) current.report.final = some laneDemand)
    (served : G.serves laneDemand event = true) (nonClock : ∀ actor millis, event ≠ .advanceClock actor millis) :
    laneDemand = .timeout sender ∧ event = .timeout sender true := by
  obtain ⟨recovery, head, rest, deadline, target, _, _, _, _, demand⟩ := CampusTCPTwoProgressTimer.timerDemand_some pending
  by_cases early : recovery.now < target
  · rw [ite_eq_left early] at demand
    have same := (F.serves_tick _ _ event).mp (demand ▸ served)
    exact False.elim (nonClock _ _ same)
  · rw [ite_eq_right early] at demand
    have same := (F.serves_timeout _ event).mp (demand ▸ served)
    exact ⟨demand, same⟩

theorem allowed_choice (active : Active core)
    (allowed : C.Allowed (config initial native quantum allowance) current.report.final monitor event)
    (nonClock : ∀ actor millis, event ≠ .advanceClock actor millis) (nonDrop : ∀ id, event ≠ .dropPacket id) :
    ActionChoice initial native quantum allowance current monitor event := by
  obtain ⟨_, chosen | dropped | clocked, _⟩ := (F.allowed_iff _ _ _ _).mp allowed
  · obtain ⟨demand, next, served⟩ := chosen
    cases selection active next served with
    | lower _ mode ack selected served =>
      obtain ⟨action, next, same⟩ := lane_action selected served nonDrop
      exact .lower action mode ack next same
    | upper _ mode ack first selected served =>
      obtain ⟨action, next, same⟩ := lane_action selected served nonDrop
      exact .upper action mode ack first next same
    | ack lane _ pending selected served =>
      obtain ⟨action, next, same⟩ := lane_action selected served nonDrop
      exact .ack lane action pending next same
    | retry _ mode ack waiting selected served =>
      obtain ⟨action, next, same⟩ := lane_action selected served nonDrop
      exact .retry action mode ack waiting next same
    | timer demand mode ack waiting pending next served =>
      obtain ⟨same, event⟩ := timer_event pending served nonClock
      exact .timeout mode ack waiting (same ▸ next) event
  · obtain ⟨id, _, same, _⟩ := dropped
    exact False.elim (nonDrop id same)
  · obtain ⟨actor, millis, same, _⟩ := F.freeClock_event _ _ _ _ clocked
    exact False.elim (nonClock actor millis same)

private theorem action_not_drop (action : CampusTCPRoundMonitor.Action) (id : Nat) : Event.dropPacket id ≠ action.event := by
  intro impossible
  cases action <;> cases impossible

private theorem lane_drop
    (selected : C.laneDemand (config initial native quantum allowance) current.report.final monitor lane = some laneDemand)
    (served : G.serves laneDemand (.dropPacket id) = true) :
    monitor.drops.length < allowance ∧ C.exposedPacket (config initial native quantum allowance) current.report.final lane = some id := by
  unfold C.laneDemand at selected
  cases next : G.nextAction (config initial native quantum allowance).toConfig current.report.final lane.toGap with
  | none => simp only [next, bind, Option.bind] at selected; cases selected
  | some action =>
    simp only [next, bind, Option.bind] at selected
    cases packet : G.packetAt lane.toGap with
    | none =>
      have same : laneDemand = .operation action := by simpa only [packet, pure, Option.some.injEq] using selected.symm
      exact False.elim (action_not_drop action id ((F.serves_operation _ _).mp (same ▸ served)))
    | some packetID =>
      simp only [packet] at selected
      split at selected
      · rename_i budget
        have same : laneDemand = .resolution action packetID := (Option.some.inj selected).symm
        rcases (CampusTCPGapProgressMonitorFacts.serves_resolution action packetID (.dropPacket id)).mp (same ▸ served) with ordinary | drop
        · exact False.elim (action_not_drop action id ordinary)
        · have identity := Event.dropPacket.inj drop
          exact ⟨budget, by simp only [C.exposedPacket, next, bind, Option.bind, packet]; exact congrArg some identity.symm⟩
      · have same : laneDemand = .operation action := (Option.some.inj selected).symm
        exact False.elim (action_not_drop action id ((F.serves_operation _ _).mp (same ▸ served)))

private theorem target_exists (active : Active core) (budget : monitor.drops.length < allowance)
    (exposed : C.exposedPacket (config initial native quantum allowance) current.report.final monitor.lower = some id ∨
      C.exposedPacket (config initial native quantum allowance) current.report.final monitor.upper = some id ∨
      C.exposedPacket (config initial native quantum allowance) current.report.final monitor.retry = some id ∨
      ∃ lane, monitor.ack = some lane ∧ C.exposedPacket (config initial native quantum allowance) current.report.final lane = some id) :
    ∃ target, C.dropTarget (config initial native quantum allowance) current.report.final monitor id = some target := by
  have mode : (monitor.mode == .originals || monitor.mode == .recovery) = true := by
    rcases active.mode with mode | mode <;> rw [mode] <;> rfl
  unfold C.dropTarget
  have currentBudget : monitor.drops.length < (config initial native quantum allowance).lossAllowance := budget
  rw [mode]
  simp only [ite_true, ite_eq_left currentBudget]
  by_cases first : C.exposedPacket (config initial native quantum allowance) current.report.final monitor.lower = some id
  · exact ⟨.lower, by simp only [first, beq_self_eq_true, ite_true]⟩
  · by_cases second : C.exposedPacket (config initial native quantum allowance) current.report.final monitor.upper = some id
    · exact ⟨.upper, by simp only [beq_iff_eq, first, second, ite_false, ite_true]⟩
    · by_cases retry : C.exposedPacket (config initial native quantum allowance) current.report.final monitor.retry = some id
      · exact ⟨.retry, by simp only [beq_iff_eq, first, second, retry, ite_false, ite_true]⟩
      · obtain ⟨lane, pending, packet⟩ := exposed.resolve_left first |>.resolve_left second |>.resolve_left retry
        exact ⟨.ack, by simp only [beq_iff_eq, first, second, retry, ite_false, pending, packet, ite_true]⟩

theorem allowed_drop_target (active : Active core) (id : Nat)
    (allowed : C.Allowed (config initial native quantum allowance) current.report.final monitor (.dropPacket id)) :
    ∃ target, C.dropTarget (config initial native quantum allowance) current.report.final monitor id = some target := by
  obtain ⟨_, chosen | dropped | clocked, _⟩ := (F.allowed_iff _ _ _ _).mp allowed
  · obtain ⟨demand, next, served⟩ := chosen
    cases selection active next served with
    | lower _ _ _ selected served =>
      obtain ⟨budget, exposed⟩ := lane_drop selected served
      exact target_exists active budget (.inl exposed)
    | upper _ _ _ _ selected served =>
      obtain ⟨budget, exposed⟩ := lane_drop selected served
      exact target_exists active budget (.inr (.inl exposed))
    | ack lane _ pending selected served =>
      obtain ⟨budget, exposed⟩ := lane_drop selected served
      exact target_exists active budget (.inr (.inr (.inr ⟨lane, pending, exposed⟩)))
    | retry _ _ _ _ selected served =>
      obtain ⟨budget, exposed⟩ := lane_drop selected served
      exact target_exists active budget (.inr (.inr (.inl exposed)))
    | timer demand _ _ _ pending _ served =>
      have same := timer_event pending served (by intros; intro impossible; cases impossible)
      cases same.2
  · obtain ⟨other, target, same, selected⟩ := dropped
    have identity := Event.dropPacket.inj same
    exact ⟨target, identity ▸ selected⟩
  · obtain ⟨_, _, impossible, _⟩ := F.freeClock_event _ _ _ _ clocked
    cases impossible

end Netlib.Check.CampusTCPTwoProgressEvidence
