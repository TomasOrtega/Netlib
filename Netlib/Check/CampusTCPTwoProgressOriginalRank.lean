import Netlib.Check.CampusTCPTwoProgressMonitorFacts

/-!
# Remaining original-path work for two TCP records

This rank stops at the actual handoff to recovery or read.
Healthy evidence must establish the legal current phase shape separately.
-/

namespace Netlib.Check.CampusTCPTwoProgressOriginalRank

open CampusTCPModel CampusTCPTwoProgressMonitor
local notation "Config" => CampusTCPTwoProgressMonitor.Config
namespace R
export CampusTCPRoundMonitor (Phase Action)
end R
namespace G
export CampusTCPGapProgressMonitor (Monitor nextAction observeOutput observeAssignment observeService observeReceipt)
end G
namespace F
export CampusTCPTwoProgressMonitorFacts
  (phase_beq phase_beq_false phase_beq_self mode_beq output_phase assignment_phase service_phase receipt_phase
    normalize_frame normalize_lanes observe_clock observe_action allowed_iff freeClock_event laneDemand_action dropTarget_packet)
end F

variable {id : Nat}

def dataCost : R.Phase → Nat
  | .needSend => 8
  | .dataIngress => 7
  | .dataTicket => 6
  | .dataLink => 5
  | _ => 0

def ackCost : R.Phase → Nat
  | .needAck => 4
  | .ackIngress => 3
  | .ackTicket => 2
  | .ackLink => 1
  | _ => 0

def ackWork (ack : Option Lane) : Nat :=
  match ack with | none => 0 | some lane => ackCost lane.phase

def originalRank (monitor : Monitor) : Nat :=
  match monitor.mode with
  | .originals => dataCost monitor.lower.phase + dataCost monitor.upper.phase + ackWork monitor.ack
  | _ => 0

def DataPhase (phase : R.Phase) : Prop :=
  phase = .needSend ∨ phase = .dataIngress ∨ phase = .dataTicket ∨ phase = .dataLink ∨ phase = .done

def RetryPhase (phase : R.Phase) : Prop :=
  phase = .dataIngress ∨ phase = .dataTicket ∨ phase = .dataLink ∨ phase = .done

def AckPhase (phase : R.Phase) : Prop :=
  phase = .needAck ∨ phase = .ackIngress ∨ phase = .ackTicket ∨ phase = .ackLink

structure RankShape (monitor : Monitor) : Prop where
  lower : DataPhase monitor.lower.phase
  upper : DataPhase monitor.upper.phase
  retry : RetryPhase monitor.retry.phase
  originalRetry : monitor.mode = .originals → monitor.retry.phase = .done
  ack : ∀ lane, monitor.ack = some lane → AckPhase lane.phase
  handoff : monitor.mode ≠ .originals → monitor.mode ≠ .invalid →
    monitor.lower.phase = .done ∧ monitor.upper.phase = .done

theorem initial_shape : RankShape Monitor.initial := by
  refine ⟨Or.inl rfl, Or.inl rfl, Or.inr (Or.inr (Or.inr rfl)), fun _ => rfl, ?_, ?_⟩
  · intro lane absent
    cases absent
  · intro different
    exact False.elim (different rfl)

theorem initial_rank : originalRank Monitor.initial = 16 := rfl

theorem dataCost_zero (legal : DataPhase phase) : dataCost phase = 0 ↔ phase = .done := by
  rcases legal with rfl | rfl | rfl | rfl | rfl <;> simp [dataCost]

theorem ackCost_positive (legal : AckPhase phase) : 0 < ackCost phase := by
  rcases legal with rfl | rfl | rfl | rfl <;> decide

theorem invalid_rank (monitor : Monitor) : originalRank monitor.invalid = 0 := rfl

theorem rank_le_work (monitor : Monitor) :
    originalRank monitor ≤ dataCost monitor.lower.phase + dataCost monitor.upper.phase + ackWork monitor.ack := by
  cases mode : monitor.mode <;> simp [originalRank, mode]

theorem normalize_nonincrease (config : Config) (state : State input) (monitor : Monitor) :
    originalRank (normalize config state monitor) ≤ originalRank monitor := by
  generalize computed : normalize config state monitor = result
  unfold normalize at computed
  repeat' (first | split at computed | (dsimp (config := { zetaHave := true }) only at computed; split at computed))
  all_goals
    cases computed
    first | exact Nat.le_refl _ | exact Nat.zero_le _

theorem clock_rank (config : Config) (monitor : Monitor) (actual : Step input)
    (supported : actual.result.supported = true) (passed : actual.result.passed = true)
    (allowed : Allowed config actual.before monitor actual.event)
    (event : actual.event = .advanceClock actor millis) :
    originalRank (CampusTCPTwoProgressMonitor.observe config monitor actual) = originalRank monitor := by
  rw [F.observe_clock config monitor actual supported passed allowed event]

theorem zero_resolved (shape : RankShape monitor) (healthy : monitor.mode ≠ .invalid)
    (zero : originalRank monitor = 0) :
    monitor.lower.phase = .done ∧ monitor.upper.phase = .done ∧
      (monitor.mode = .originals → monitor.ack = none) := by
  by_cases originals : monitor.mode = .originals
  · simp only [originalRank, originals] at zero
    have lower := (dataCost_zero shape.lower).mp (by omega)
    have upper := (dataCost_zero shape.upper).mp (by omega)
    refine ⟨lower, upper, fun _ => ?_⟩
    cases ack : monitor.ack with
    | none => rfl
    | some lane =>
      have positive := ackCost_positive (shape.ack lane ack)
      simp only [ackWork, ack] at zero
      omega
  · obtain ⟨lower, upper⟩ := shape.handoff originals healthy
    exact ⟨lower, upper, fun same => False.elim (originals same)⟩

def dataWork (monitor : Monitor) : Nat := dataCost monitor.lower.phase + dataCost monitor.upper.phase

theorem recordData_work (monitor : Monitor) (lane : Lane) (actual : Step input) :
    dataWork (recordData monitor lane actual) = dataWork monitor := by
  cases receipt : lane.refs.dataReceipt <;> cases application : actual.result.application with
  | none => simp only [recordData, receipt, application]; rfl
  | some pair =>
    cases pair
    simp only [recordData, receipt, application]
    rfl

theorem data_lower_bound (config : Config) (monitor : Monitor) (actual : Step input) :
    originalRank (observeData config monitor actual .lower) ≤
      dataCost (dataLane config monitor.lower actual).phase + dataCost monitor.upper.phase +
        if (dataLane config monitor.lower actual).phase = .done then 4 else ackWork monitor.ack := by
  unfold observeData
  dsimp only
  split
  · exact Nat.zero_le _
  · split
    · rename_i done
      have done : (dataLane config monitor.lower actual).phase = .done := by
        simpa only [F.phase_beq, decide_eq_true_eq] using done
      have estimate := rank_le_work
        { recordData { monitor with lower := dataLane config monitor.lower actual, lastOriginal := some .lower }
            (dataLane config monitor.lower actual) actual with
          ack := some { phase := .needAck, refs := (dataLane config monitor.lower actual).refs }, waiting := false }
      have frame := recordData_work
        { monitor with lower := dataLane config monitor.lower actual, lastOriginal := some .lower }
        (dataLane config monitor.lower actual) actual
      change originalRank _ ≤ dataWork (recordData _ _ _) + 4 at estimate
      rw [frame] at estimate
      simpa only [dataWork, done, ite_true] using estimate
    · rename_i pending
      have notDone : (dataLane config monitor.lower actual).phase ≠ .done := by
        intro same
        simp only [same, F.phase_beq_self] at pending
        contradiction
      simpa only [notDone, ite_false] using
        rank_le_work { monitor with lower := dataLane config monitor.lower actual, lastOriginal := some .lower }

theorem data_upper_bound (config : Config) (monitor : Monitor) (actual : Step input) :
    originalRank (observeData config monitor actual .upper) ≤
      dataCost monitor.lower.phase + dataCost (dataLane config monitor.upper actual).phase +
        if (dataLane config monitor.upper actual).phase = .done then 4 else ackWork monitor.ack := by
  unfold observeData
  dsimp only
  split
  · exact Nat.zero_le _
  · split
    · rename_i done
      have done : (dataLane config monitor.upper actual).phase = .done := by
        simpa only [F.phase_beq, decide_eq_true_eq] using done
      have estimate := rank_le_work
        { recordData { monitor with upper := dataLane config monitor.upper actual, lastOriginal := some .upper }
            (dataLane config monitor.upper actual) actual with
          ack := some { phase := .needAck, refs := (dataLane config monitor.upper actual).refs }, waiting := false }
      have frame := recordData_work
        { monitor with upper := dataLane config monitor.upper actual, lastOriginal := some .upper }
        (dataLane config monitor.upper actual) actual
      change originalRank _ ≤ dataWork (recordData _ _ _) + 4 at estimate
      rw [frame] at estimate
      simpa only [dataWork, done, ite_true] using estimate
    · rename_i pending
      have notDone : (dataLane config monitor.upper actual).phase ≠ .done := by
        intro same
        simp only [same, F.phase_beq_self] at pending
        contradiction
      simpa only [notDone, ite_false] using
        rank_le_work { monitor with upper := dataLane config monitor.upper actual, lastOriginal := some .upper }

theorem dataLane_phase (config : Config) (lane : Lane) (actual : Step input) :
    (dataLane config lane actual).phase = (match lane.phase with
      | .dataIngress => .dataTicket | .dataTicket => .dataLink | .dataLink => .done | _ => .invalid) ∨
      (dataLane config lane actual).phase = .invalid := by
  cases phase : lane.phase <;> simp only [dataLane, phase, Lane.ofGap]
  case dataIngress => exact F.assignment_phase _ _ _ _
  case dataTicket => exact F.service_phase _ _ _ _
  case dataLink => exact F.receipt_phase _ _ _ _ _
  all_goals exact Or.inl rfl

theorem send_lower_strict (config : Config) (monitor : Monitor) (actual : Step input)
    (mode : monitor.mode = .originals) (pending : monitor.lower.phase = .needSend) :
    originalRank (observeSend config monitor actual .lower) < originalRank monitor := by
  rcases F.output_phase config.toConfig monitor.lower.toGap actual true .dataIngress with decoded | decoded
  · simp [observeSend, Lane.ofGap, decoded, F.phase_beq, originalRank, mode, pending, dataCost]
  · simp [observeSend, Lane.ofGap, decoded, F.phase_beq, originalRank, Monitor.invalid, mode, pending, dataCost] <;> omega

theorem send_upper_strict (config : Config) (monitor : Monitor) (actual : Step input)
    (mode : monitor.mode = .originals) (pending : monitor.upper.phase = .needSend) :
    originalRank (observeSend config monitor actual .upper) < originalRank monitor := by
  rcases F.output_phase config.toConfig monitor.upper.toGap actual true .dataIngress with decoded | decoded
  · simp [observeSend, Lane.ofGap, decoded, F.phase_beq, originalRank, mode, pending, dataCost]
  · simp [observeSend, Lane.ofGap, decoded, F.phase_beq, originalRank, Monitor.invalid, mode, pending, dataCost] <;> omega

def ActiveDataPhase (phase : R.Phase) : Prop :=
  phase = .dataIngress ∨ phase = .dataTicket ∨ phase = .dataLink

theorem data_lower_strict (config : Config) (monitor : Monitor) (actual : Step input)
    (mode : monitor.mode = .originals) (ack : monitor.ack = none) (active : ActiveDataPhase monitor.lower.phase) :
    originalRank (observeData config monitor actual .lower) < originalRank monitor := by
  have estimate := data_lower_bound config monitor actual
  have before : originalRank monitor = dataCost monitor.lower.phase + dataCost monitor.upper.phase := by
    simp only [originalRank, mode, ack, ackWork, Nat.add_zero]
  rw [before]
  rcases active with phase | phase | phase
  all_goals
    rcases dataLane_phase config monitor.lower actual with decoded | decoded
    all_goals
      try simp only [phase] at decoded
      simp [decoded, phase, dataCost, ack, ackWork] at estimate ⊢
      omega

theorem data_upper_strict (config : Config) (monitor : Monitor) (actual : Step input)
    (mode : monitor.mode = .originals) (ack : monitor.ack = none) (active : ActiveDataPhase monitor.upper.phase) :
    originalRank (observeData config monitor actual .upper) < originalRank monitor := by
  have estimate := data_upper_bound config monitor actual
  have before : originalRank monitor = dataCost monitor.lower.phase + dataCost monitor.upper.phase := by
    simp only [originalRank, mode, ack, ackWork, Nat.add_zero]
  rw [before]
  rcases active with phase | phase | phase
  all_goals
    rcases dataLane_phase config monitor.upper actual with decoded | decoded
    all_goals
      try simp only [phase] at decoded
      simp [decoded, phase, dataCost, ack, ackWork] at estimate ⊢
      omega

theorem ackLane_phase (config : Config) (lane : Lane) (actual : Step input) :
    (ackLane config lane actual).phase = (match lane.phase with
      | .needAck => .ackIngress | .ackIngress => .ackTicket | .ackTicket => .ackLink | .ackLink => .done | _ => .invalid) ∨
      (ackLane config lane actual).phase = .invalid := by
  cases phase : lane.phase <;> simp only [ackLane, phase, Lane.ofGap]
  case needAck => exact F.output_phase _ _ _ _ _
  case ackIngress => exact F.assignment_phase _ _ _ _
  case ackTicket => exact F.service_phase _ _ _ _
  case ackLink => exact F.receipt_phase _ _ _ _ _
  all_goals exact Or.inl rfl

theorem ack_bound (config : Config) (monitor : Monitor) (actual : Step input) (lane : Lane) :
    originalRank (observeAck config monitor actual lane) ≤
      dataCost monitor.lower.phase + dataCost monitor.upper.phase + ackCost (ackLane config lane actual).phase := by
  unfold observeAck
  dsimp only
  split
  · exact Nat.zero_le _
  · split
    · rename_i done
      have done : (ackLane config lane actual).phase = .done := by
        simpa only [F.phase_beq, decide_eq_true_eq] using done
      split
      · exact Nat.zero_le _
      · rename_i index present
        let updated : Monitor := { monitor with ack := none, ackReceipts := monitor.ackReceipts ++ [index] }
        have estimate := Nat.le_trans (normalize_nonincrease config actual.result.state updated) (rank_le_work updated)
        simpa only [updated, ackWork, done, ackCost] using estimate
    · exact rank_le_work _

theorem ack_strict (config : Config) (monitor : Monitor) (actual : Step input) (lane : Lane)
    (mode : monitor.mode = .originals) (ack : monitor.ack = some lane) (legal : AckPhase lane.phase) :
    originalRank (observeAck config monitor actual lane) < originalRank monitor := by
  have estimate := ack_bound config monitor actual lane
  have before : originalRank monitor = dataCost monitor.lower.phase + dataCost monitor.upper.phase + ackCost lane.phase := by
    simp only [originalRank, mode, ack, ackWork]
  rw [before]
  rcases legal with phase | phase | phase | phase
  all_goals
    rcases ackLane_phase config lane actual with decoded | decoded
    all_goals
      try simp only [phase] at decoded
      simp [decoded, phase, ackCost] at estimate ⊢
      omega

theorem active_of_served (config : Config) (state : State input) (monitor : Monitor) (lane : Lane) (event : Event)
    (legal : DataPhase lane.phase) (sent : lane.phase ≠ .needSend)
    (served : servesOption (laneDemand config state monitor lane) event = true) : ActiveDataPhase lane.phase := by
  rcases legal with pending | phase | phase | phase | done
  · exact False.elim (sent pending)
  · exact Or.inl phase
  · exact Or.inr (Or.inl phase)
  · exact Or.inr (Or.inr phase)
  · simp only [laneDemand, G.nextAction, Lane.toGap, done, bind, Option.bind, servesOption, Bool.false_eq_true] at served

theorem ordinary_strict (config : Config) (monitor : Monitor) (actual : Step input)
    (shape : RankShape monitor) (mode : monitor.mode = .originals) (positive : 0 < originalRank monitor) :
    originalRank (observeOrdinary config monitor actual) < originalRank monitor := by
  by_cases lower : monitor.lower.phase = .needSend
  · rw [CampusTCPTwoProgressMonitorFacts.observe_send_lower config monitor actual mode lower]
    exact send_lower_strict config monitor actual mode lower
  · by_cases upper : monitor.upper.phase = .needSend
    · rw [CampusTCPTwoProgressMonitorFacts.observe_send_upper config monitor actual mode lower upper]
      exact send_upper_strict config monitor actual mode upper
    · cases ack : monitor.ack with
      | some lane =>
        rw [CampusTCPTwoProgressMonitorFacts.observe_ack config monitor actual lane (Or.inl mode) lower upper ack]
        exact ack_strict config monitor actual lane mode ack (shape.ack lane ack)
      | none =>
        cases first : servesOption (laneDemand config actual.before monitor monitor.lower) actual.event with
        | true =>
          rw [CampusTCPTwoProgressMonitorFacts.observe_original_lower config monitor actual mode lower upper ack first]
          exact data_lower_strict config monitor actual mode ack
            (active_of_served config actual.before monitor monitor.lower actual.event shape.lower lower first)
        | false =>
          cases second : servesOption (laneDemand config actual.before monitor monitor.upper) actual.event with
          | true =>
            rw [CampusTCPTwoProgressMonitorFacts.observe_original_upper config monitor actual mode lower upper ack first second]
            exact data_upper_strict config monitor actual mode ack
              (active_of_served config actual.before monitor monitor.upper actual.event shape.upper upper second)
          | false =>
            simpa only [observeOrdinary, mode, (F.phase_beq_false _ _).mpr lower,
              (F.phase_beq_false _ _).mpr upper, Bool.false_eq_true, ite_false, ack, first, second, invalid_rank] using positive

theorem exposed_data_positive (config : Config) (state : State input) (lane : Lane)
    (legal : DataPhase lane.phase) (packet : exposedPacket config state lane = some id) : 0 < dataCost lane.phase := by
  apply Nat.pos_of_ne_zero
  intro zero
  have done := (dataCost_zero legal).mp zero
  simp only [exposedPacket, G.nextAction, Lane.toGap, done, bind, Option.bind] at packet
  cases packet

theorem drop_strict (config : Config) (monitor : Monitor) (actual : Step input) (id : Nat)
    (shape : RankShape monitor) (mode : monitor.mode = .originals)
    (target : dropTarget config actual.before monitor id = some selected) :
    originalRank (observeDrop config monitor actual id) < originalRank monitor := by
  have packet := F.dropTarget_packet config actual.before monitor id target
  rw [observeDrop, target]
  cases selected with
  | lower =>
    have positive := exposed_data_positive config actual.before monitor.lower shape.lower packet
    let updated : Monitor := { monitor with drops := monitor.drops ++ [id], lower := { monitor.lower with phase := .done } }
    apply Nat.lt_of_le_of_lt (normalize_nonincrease config actual.result.state updated)
    have after : originalRank updated = dataCost monitor.upper.phase + ackWork monitor.ack := by
      simp only [updated, originalRank, mode, dataCost, Nat.zero_add]
    rw [after]
    simp only [originalRank, mode]
    omega
  | upper =>
    have positive := exposed_data_positive config actual.before monitor.upper shape.upper packet
    let updated : Monitor := { monitor with drops := monitor.drops ++ [id], upper := { monitor.upper with phase := .done } }
    apply Nat.lt_of_le_of_lt (normalize_nonincrease config actual.result.state updated)
    have after : originalRank updated = dataCost monitor.lower.phase + ackWork monitor.ack := by
      simp only [updated, originalRank, mode, dataCost, Nat.add_zero]
    rw [after]
    simp only [originalRank, mode]
    omega
  | retry =>
    have done := shape.originalRetry mode
    simp only [exposedPacket, G.nextAction, Lane.toGap, done, bind, Option.bind] at packet
    cases packet
  | ack =>
    obtain ⟨lane, ack, _⟩ := packet
    have positive := ackCost_positive (shape.ack lane ack)
    let updated : Monitor := { monitor with drops := monitor.drops ++ [id], ack := none }
    apply Nat.lt_of_le_of_lt (normalize_nonincrease config actual.result.state updated)
    have after : originalRank updated = dataCost monitor.lower.phase + dataCost monitor.upper.phase := by
      simp only [updated, originalRank, mode, ackWork, Nat.add_zero]
    rw [after]
    simp only [originalRank, mode, ack, ackWork]
    omega

theorem normalize_nonoriginal (config : Config) (state : State input) (monitor : Monitor)
    (before : monitor.mode ≠ .originals) : (normalize config state monitor).mode ≠ .originals := by
  generalize computed : normalize config state monitor = result
  unfold normalize at computed
  repeat' (first | split at computed | (dsimp (config := { zetaHave := true }) only at computed; split at computed))
  all_goals
    cases computed
    first | exact before | (intro same; cases same)

theorem recordData_nonoriginal (monitor : Monitor) (lane : Lane) (actual : Step input)
    (before : monitor.mode ≠ .originals) : (recordData monitor lane actual).mode ≠ .originals := by
  cases receipt : lane.refs.dataReceipt <;> cases application : actual.result.application with
  | none =>
    simp only [recordData, receipt, application]
    first | exact before | (intro same; cases same)
  | some pair =>
    cases pair
    simp only [recordData, receipt, application]
    first | exact before | (intro same; cases same)

theorem data_nonoriginal (config : Config) (monitor : Monitor) (actual : Step input) (target : DropTarget)
    (before : monitor.mode ≠ .originals) : (observeData config monitor actual target).mode ≠ .originals := by
  cases target <;> unfold observeData
  all_goals
    dsimp only
    split
    · intro same; cases same
    · split
      · apply recordData_nonoriginal
        first | exact before | (intro same; cases same)
      · first | exact before | (intro same; cases same)

theorem ack_nonoriginal (config : Config) (monitor : Monitor) (actual : Step input) (lane : Lane)
    (before : monitor.mode ≠ .originals) : (observeAck config monitor actual lane).mode ≠ .originals := by
  unfold observeAck
  dsimp only
  split
  · intro same; cases same
  · split
    · split
      · intro same; cases same
      · exact normalize_nonoriginal _ _ _ before
    · exact before

theorem send_nonoriginal (config : Config) (monitor : Monitor) (actual : Step input) (target : Original)
    (before : monitor.mode ≠ .originals) : (observeSend config monitor actual target).mode ≠ .originals := by
  cases target <;> unfold observeSend
  all_goals dsimp only; split
  all_goals first | exact before | (intro same; cases same)

theorem read_nonoriginal (config : Config) (monitor : Monitor) (actual : Step input) :
    (observeRead config monitor actual).mode ≠ .originals := by
  cases application : actual.result.application with
  | none => simp only [observeRead, application]; intro same; cases same
  | some pair =>
    cases pair
    simp only [observeRead, application]
    split <;> intro same <;> cases same

theorem ordinary_nonoriginal (config : Config) (monitor : Monitor) (actual : Step input)
    (before : monitor.mode ≠ .originals) : (observeOrdinary config monitor actual).mode ≠ .originals := by
  cases mode : monitor.mode <;> simp only [observeOrdinary, mode]
  case originals => exact False.elim (before mode)
  case recovery =>
    split
    · exact ack_nonoriginal _ _ _ _ before
    · split
      · intro same; cases same
      · exact data_nonoriginal _ _ _ _ before
  case needRead => exact read_nonoriginal _ _ _
  all_goals intro same; cases same

theorem drop_nonoriginal (config : Config) (monitor : Monitor) (actual : Step input) (id : Nat)
    (before : monitor.mode ≠ .originals) : (observeDrop config monitor actual id).mode ≠ .originals := by
  unfold observeDrop
  split
  · intro same; cases same
  · rename_i target _
    cases target <;> exact normalize_nonoriginal _ _ _ before

theorem timeout_nonoriginal (config : Config) (monitor : Monitor) (actual : Step input)
    (before : monitor.mode ≠ .originals) : (observeTimeout config monitor actual).mode ≠ .originals := by
  unfold observeTimeout
  dsimp only
  split
  · intro same; cases same
  · exact before

theorem observe_nonoriginal (config : Config) (monitor : Monitor) (actual : Step input)
    (before : monitor.mode ≠ .originals) : (CampusTCPTwoProgressMonitor.observe config monitor actual).mode ≠ .originals := by
  unfold CampusTCPTwoProgressMonitor.observe
  split
  · cases event : actual.event
    case timeout actor policy =>
      cases policy
      · exact ordinary_nonoriginal config monitor actual before
      · exact timeout_nonoriginal config monitor actual before
    all_goals first
      | exact before
      | exact ordinary_nonoriginal config monitor actual before
      | exact drop_nonoriginal config monitor actual _ before
  · intro same; cases same

theorem rank_zero_of_nonoriginal (before : monitor.mode ≠ .originals) : originalRank monitor = 0 := by
  cases mode : monitor.mode <;> simp only [originalRank, mode]
  exact False.elim (before mode)

theorem pending_positive (config : Config) (state : State input) (monitor : Monitor)
    (shape : RankShape monitor) (mode : monitor.mode = .originals)
    (pending : nextDemand config state monitor = some demand) : 0 < originalRank monitor := by
  by_cases positive : 0 < originalRank monitor
  · exact positive
  · have zero : originalRank monitor = 0 := by omega
    have healthy : monitor.mode ≠ .invalid := by rw [mode]; intro same; cases same
    obtain ⟨lower, upper, ack⟩ := zero_resolved shape healthy zero
    have ack := ack mode
    simp [nextDemand, mode, lower, upper, ack, F.phase_beq, laneDemand, G.nextAction, Lane.toGap] at pending

theorem action_strict (config : Config) (monitor : Monitor) (actual : Step input)
    (shape : RankShape monitor) (mode : monitor.mode = .originals)
    (pending : nextDemand config actual.before monitor = some demand)
    (supported : actual.result.supported = true) (passed : actual.result.passed = true)
    (allowed : Allowed config actual.before monitor actual.event) (action : R.Action) (event : actual.event = action.event) :
    originalRank (CampusTCPTwoProgressMonitor.observe config monitor actual) < originalRank monitor := by
  rw [F.observe_action config monitor actual supported passed allowed action event]
  exact ordinary_strict config monitor actual shape mode (pending_positive config actual.before monitor shape mode pending)

theorem ordinary_nonincrease (config : Config) (monitor : Monitor) (actual : Step input)
    (shape : RankShape monitor) (mode : monitor.mode = .originals) :
    originalRank (observeOrdinary config monitor actual) ≤ originalRank monitor := by
  by_cases positive : 0 < originalRank monitor
  · exact Nat.le_of_lt (ordinary_strict config monitor actual shape mode positive)
  · have zero : originalRank monitor = 0 := by omega
    have healthy : monitor.mode ≠ .invalid := by rw [mode]; intro same; cases same
    obtain ⟨lower, upper, ack⟩ := zero_resolved shape healthy zero
    have ack := ack mode
    simp [observeOrdinary, mode, lower, upper, ack, F.phase_beq, servesOption,
      laneDemand, G.nextAction, Lane.toGap, invalid_rank]

theorem drop_nonincrease (config : Config) (monitor : Monitor) (actual : Step input) (id : Nat)
    (shape : RankShape monitor) (mode : monitor.mode = .originals) :
    originalRank (observeDrop config monitor actual id) ≤ originalRank monitor := by
  cases target : dropTarget config actual.before monitor id with
  | none => simp only [observeDrop, target, invalid_rank]; exact Nat.zero_le _
  | some selected => exact Nat.le_of_lt (drop_strict config monitor actual id shape mode target)

theorem timeout_nonincrease (config : Config) (monitor : Monitor) (actual : Step input) :
    originalRank (observeTimeout config monitor actual) ≤ originalRank monitor := by
  unfold observeTimeout
  dsimp only
  split
  · exact Nat.zero_le _
  · exact Nat.le_refl _

theorem observe_nonincrease (config : Config) (monitor : Monitor) (actual : Step input) (shape : RankShape monitor) :
    originalRank (CampusTCPTwoProgressMonitor.observe config monitor actual) ≤ originalRank monitor := by
  by_cases mode : monitor.mode = .originals
  · unfold CampusTCPTwoProgressMonitor.observe
    split
    · cases event : actual.event
      case advanceClock actor millis => exact Nat.le_refl _
      case dropPacket id => exact drop_nonincrease config monitor actual id shape mode
      case timeout actor policy =>
        cases policy
        · exact ordinary_nonincrease config monitor actual shape mode
        · exact timeout_nonincrease config monitor actual
      all_goals exact ordinary_nonincrease config monitor actual shape mode
    · exact Nat.zero_le _
  · rw [rank_zero_of_nonoriginal mode,
      rank_zero_of_nonoriginal (observe_nonoriginal config monitor actual mode)]
    exact Nat.le_refl _

theorem observed_drop_strict (config : Config) (monitor : Monitor) (actual : Step input) (id : Nat)
    (shape : RankShape monitor) (mode : monitor.mode = .originals)
    (target : dropTarget config actual.before monitor id = some selected)
    (supported : actual.result.supported = true) (passed : actual.result.passed = true)
    (allowed : Allowed config actual.before monitor actual.event) (event : actual.event = .dropPacket id) :
    originalRank (CampusTCPTwoProgressMonitor.observe config monitor actual) < originalRank monitor := by
  rw [CampusTCPTwoProgressMonitorFacts.observe_drop config monitor actual supported passed allowed event]
  exact drop_strict config monitor actual id shape mode target

end Netlib.Check.CampusTCPTwoProgressOriginalRank
