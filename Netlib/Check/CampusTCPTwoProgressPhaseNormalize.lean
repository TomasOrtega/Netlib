import Netlib.Check.CampusTCPTwoProgressPhaseBase

/-!
# Normalization from the current sender ledger

Resolved packet lanes hand off to the actual remaining flight.
Timer targets use that flight's deadline and head time.
-/

namespace Netlib.Check.CampusTCPTwoProgressPhaseNormalize

open Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart CampusTCPTwoProgressPhaseBase
open CampusTCPTwoProgressSetup (config)

namespace M
export CampusTCPTwoProgressMonitor (Monitor normalize timerTarget)
end M
namespace G
export CampusTCPGapProgressMonitor (senderRecovery)
end G
namespace S
export CampusTCPTwoProgressSender (Stage Original Retires)
end S
namespace R
export CampusTCPTwoProgressReceiver (Stage)
end R
namespace L
export CampusTCPTwoProgressLossHistory (Head)
end L

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current : Cut input complete} {sender : Actor} {gateway : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {native : NativeEnv cut gateway initial.gatewayState.session.entry} {quantum allowance : Nat}
variable {monitor raw : M.Monitor} {sent : S.Stage initial} {received : R.Stage}
variable {first : S.Original initial .lower} {second : S.Original initial .upper} {head : Recovery.Outstanding}

def Resolved (raw : M.Monitor) : Prop :=
  raw.ack = none ∧
    ((raw.mode = .originals ∧ raw.lower.phase = .done ∧ raw.upper.phase = .done) ∨
      (raw.mode = .recovery ∧ raw.retry.phase = .done))

theorem normalize_unresolved (cfg : CampusTCPTwoProgressMonitor.Config) (state : State input) (raw : M.Monitor)
    (unresolved : ¬Resolved raw) : M.normalize cfg state raw = raw := by
  cases mode : raw.mode <;> cases ack : raw.ack
  all_goals simp only [Resolved, mode, ack, reduceCtorEq, true_and, false_and, or_false, false_or,
    not_false_eq_true] at unresolved
  all_goals simp (config := { zetaHave := true }) [M.normalize, mode, ack,
    CampusTCPTwoProgressMonitorFacts.phase_beq, unresolved]

theorem sender_runtime (core : Core initial native quantum allowance current monitor sent received) :
    G.senderRecovery (config initial native quantum allowance).toConfig current.report.final = some core.live.senderFlight.recovery := by
  simp only [G.senderRecovery, current.connection, config, core.live.senderFlight.runtime]

theorem normalize_empty (core : Core initial native quantum allowance current monitor sent received)
    (shape : Resolved raw) (empty : sent.ledger = []) :
    M.normalize (config initial native quantum allowance) current.report.final raw =
      { raw with mode := .needRead, waiting := false } := by
  simp (config := { zetaHave := true }) only [M.normalize, ite_true,
    sender_runtime core, core.live.senderFlight.ledger, empty, List.isEmpty_nil]
  obtain ⟨ack, original | recovery⟩ := shape
  · obtain ⟨mode, lower, upper⟩ := original
    rw [ack, mode, lower, upper]
    rfl
  · obtain ⟨mode, retry⟩ := recovery
    rw [ack, mode, retry]
    rfl

theorem normalize_nonempty (core : Core initial native quantum allowance current monitor sent received)
    (shape : Resolved raw) (nonempty : sent.ledger ≠ []) :
    M.normalize (config initial native quantum allowance) current.report.final raw =
      { raw with mode := .recovery, waiting := true } := by
  have active : core.live.senderFlight.recovery.outstanding.isEmpty = false := by
    rw [core.live.senderFlight.ledger]
    cases ledger : sent.ledger with
    | nil => exact False.elim (nonempty ledger)
    | cons head rest => rfl
  simp (config := { zetaHave := true }) only [M.normalize,
    sender_runtime core, active, Bool.false_eq_true, ite_false]
  obtain ⟨ack, original | recovery⟩ := shape
  · obtain ⟨mode, lower, upper⟩ := original
    rw [ack, mode, lower, upper]
    rfl
  · obtain ⟨mode, retry⟩ := recovery
    rw [ack, mode, retry]
    rfl

theorem normalize_cases (core : Core initial native quantum allowance current monitor sent received)
    (nonempty : sent.ledger ≠ []) :
    (¬Resolved raw ∧ M.normalize (config initial native quantum allowance) current.report.final raw = raw) ∨
      (Resolved raw ∧ M.normalize (config initial native quantum allowance) current.report.final raw =
        { raw with mode := .recovery, waiting := true }) := by
  by_cases resolved : Resolved raw
  · exact .inr ⟨resolved, normalize_nonempty core resolved nonempty⟩
  · exact .inl ⟨resolved, normalize_unresolved _ _ _ resolved⟩

theorem normalize_both (core : Core initial native quantum allowance current monitor (.both first second head) received)
    (shape : Resolved raw) :
    M.normalize (config initial native quantum allowance) current.report.final raw =
      { raw with mode := .recovery, waiting := true } :=
  normalize_nonempty core shape (by intro impossible; cases impossible)

theorem normalize_tail (core : Core initial native quantum allowance current monitor (.tail first second head) received)
    (shape : Resolved raw) :
    M.normalize (config initial native quantum allowance) current.report.final raw =
      { raw with mode := .recovery, waiting := true } :=
  normalize_nonempty core shape (by intro impossible; cases impossible)

theorem normalize_retired (core : Core initial native quantum allowance current monitor (.retired first second) received)
    (shape : Resolved raw) :
    M.normalize (config initial native quantum allowance) current.report.final raw =
      { raw with mode := .needRead, waiting := false } :=
  normalize_empty core shape rfl

theorem retired_allReleased (core : Core initial native quantum allowance current monitor (.retired first second) received) :
    received = .allReleased := by
  have retired := core.retired
  have firstPositive := List.length_pos_iff.mpr initial.lowerNonempty
  have secondPositive := List.length_pos_iff.mpr initial.upperNonempty
  change lower.length + upper.length ≤ _ at retired
  cases received with
  | empty | upperHeld => change lower.length + upper.length ≤ 0 at retired; omega
  | lowerReleased => change lower.length + upper.length ≤ lower.length at retired; omega
  | allReleased => rfl

theorem retired_coordinate (core : Core initial native quantum allowance current monitor (.retired first second) received) :
    (CampusTCPTwoProgressSender.Stage.retired first second).retiredBytes = (received.bytes lower upper).length := by
  rw [retired_allReleased core]
  exact List.length_append.symm

theorem preparing_no_retire (preparing : sent.preparing = true) (retiring : S.Retires sent count after) : False := by
  cases retiring <;> cases preparing

def head_both (core : Core initial native quantum allowance current monitor (.both first second head) received) :
    L.Head initial current .lower where
  recovery := core.live.senderFlight.recovery
  runtime := core.live.senderFlight.runtime
  entry := head
  tail := [second.entry]
  ledger := core.live.senderFlight.ledger
  identity := congrArg Recovery.Outstanding.id core.live.senderFlight.headFixed
  position := congrArg Recovery.Outstanding.start core.live.senderFlight.headFixed
  count := congrArg Recovery.Outstanding.count core.live.senderFlight.headFixed

def head_tail (core : Core initial native quantum allowance current monitor (.tail first second head) received) :
    L.Head initial current .upper where
  recovery := core.live.senderFlight.recovery
  runtime := core.live.senderFlight.runtime
  entry := head
  tail := []
  ledger := core.live.senderFlight.ledger
  identity := congrArg Recovery.Outstanding.id core.live.senderFlight.headFixed
  position := congrArg Recovery.Outstanding.start core.live.senderFlight.headFixed
  count := congrArg Recovery.Outstanding.count core.live.senderFlight.headFixed

theorem retired_no_head (core : Core initial native quantum allowance current monitor (.retired first second) received)
    (currentHead : L.Head initial current role) : False := by
  have same : currentHead.recovery = core.live.senderFlight.recovery :=
    Option.some.inj (currentHead.runtime.symm.trans core.live.senderFlight.runtime)
  have ledger := currentHead.ledger
  rw [same, core.live.senderFlight.ledger] at ledger
  cases ledger

theorem retired_no_timer (core : Core initial native quantum allowance current monitor (.retired first second) received) :
    M.timerTarget core.live.senderFlight.recovery = none := by
  simp only [M.timerTarget, core.live.senderFlight.ledger, CampusTCPTwoProgressSender.Stage.ledger,
    List.head?_nil, bind, Option.bind]

theorem current_deadline (core : Core initial native quantum allowance current monitor sent received)
    (nonempty : sent.ledger ≠ []) : ∃ deadline, core.live.senderFlight.recovery.deadline = some deadline := by
  have armed := core.live.senderFlight.armed nonempty
  cases present : core.live.senderFlight.recovery.deadline with
  | none => rw [present] at armed; cases armed
  | some deadline => exact ⟨deadline, rfl⟩

theorem current_timer (core : Core initial native quantum allowance current monitor sent received)
    (currentHead : L.Head initial current role) :
    ∃ deadline, core.live.senderFlight.recovery.deadline = some deadline ∧
      M.timerTarget core.live.senderFlight.recovery =
        some (max deadline (currentHead.entry.lastAt + core.live.senderFlight.recovery.rto)) := by
  have same : currentHead.recovery = core.live.senderFlight.recovery :=
    Option.some.inj (currentHead.runtime.symm.trans core.live.senderFlight.runtime)
  have nonempty : sent.ledger ≠ [] := by
    intro empty
    have ledger := currentHead.ledger
    rw [same, core.live.senderFlight.ledger, empty] at ledger
    cases ledger
  obtain ⟨deadline, present⟩ := current_deadline core nonempty
  refine ⟨deadline, present, ?_⟩
  have ledger : core.live.senderFlight.recovery.outstanding = currentHead.entry :: currentHead.tail := by
    rw [← same]
    exact currentHead.ledger
  simp only [M.timerTarget, ledger, List.head?_cons, present, bind, Option.bind]
  rfl

theorem timer_both (core : Core initial native quantum allowance current monitor (.both first second head) received) :
    ∃ deadline, core.live.senderFlight.recovery.deadline = some deadline ∧
      M.timerTarget core.live.senderFlight.recovery =
        some (max deadline (head.lastAt + core.live.senderFlight.recovery.rto)) :=
  current_timer core (head_both core)

theorem timer_tail (core : Core initial native quantum allowance current monitor (.tail first second head) received) :
    ∃ deadline, core.live.senderFlight.recovery.deadline = some deadline ∧
      M.timerTarget core.live.senderFlight.recovery =
        some (max deadline (head.lastAt + core.live.senderFlight.recovery.rto)) :=
  current_timer core (head_tail core)

end Netlib.Check.CampusTCPTwoProgressPhaseNormalize
