import Netlib.Protocol.CampusWithdrawal

/-!
# Early ingress rejection of outstanding work

Rejected work retires its actual ticket before ordinary tracking and NAT.
The installed decision is supplied separately from desired attachment policy.
-/

namespace Netlib.Protocol.GuardedHandoff

open StatefulFailover (Gateway)
abbrev State := CampusWithdrawal.State
abbrev Ticket := Theory.Outstanding.Item SafeHandoff.Ticket

private def after (before : State) (work : Theory.Outstanding.State SafeHandoff.Ticket) : State :=
  { before with
    handoff := { before.handoff with
      work := work
      gateways := { before.handoff.gateways with epoch := before.handoff.gateways.epoch + 1 } } }

private theorem after_safe (before : State) (id : Nat) (safe : before.Safe)
    (completed : Theory.Outstanding.Completed before.handoff.work id) : (after before completed.state).Safe := by
  let next := after before completed.state
  have subset : ∀ item ∈ next.handoff.work.pending, item ∈ before.handoff.work.pending := by
    intro item member
    exact completed.pendingPerm.mem_iff.mpr (List.mem_cons_of_mem _ member)
  have uses : ∀ gateway, next.handoff.uses gateway = true → before.handoff.uses gateway = true :=
    SafeHandoff.State.uses_mono before.handoff next.handoff rfl
      (fun item member => before.handoff.uses_pending item (subset item member))
  have handoffSafe : next.handoff.Safe := by
    cases binding : before.handoff.binding with
    | none =>
      have empty : before.handoff.work.pending = [] := by simpa only [binding] using safe.1.2.2.2
      have member := completed.member
      simp [empty] at member
    | some entry =>
      have flow := safe.1.flow binding
      exact SafeHandoff.State.safe_of_flow next.handoff entry binding safe.1.1
        (completed.valid safe.1.2.1)
        (SafeHandoff.State.unfenced_transfer before.handoff next.handoff safe.1.2.2.1 uses rfl)
        flow.1 flow.2.1 (fun item member => flow.2.2.1 item (subset item member))
        (fun used => flow.2.2.2 (uses .standby used))
  refine ⟨handoffSafe, ?_⟩
  cases withdrawn : before.withdrawn with
  | false => simpa only [after, withdrawn, Bool.false_eq_true, ite_false] using safe.2
  | true =>
    have ready := before.withdrawn_ready safe withdrawn
    have outside := (SafeHandoff.State.outstanding_zero before.handoff .primary).mp ready.2.2.2.1
    have nextReady : next.Ready := ⟨ready.1, ready.2.1, ready.2.2.1,
      (SafeHandoff.State.outstanding_zero next.handoff .primary).mpr
        (fun item member => outside item (subset item member)), ready.2.2.2.2⟩
    have archive := before.withdrawn_archive safe withdrawn
    change if before.withdrawn then next.Ready ∧ before.archive = some before.handoff.gateways.primary else before.archive = none
    rw [withdrawn]
    exact ⟨nextReady, archive⟩

structure Dropped (before : State) (id : Nat) where
  completed : Theory.Outstanding.Completed before.handoff.work id
  computed : Theory.Outstanding.complete before.handoff.work id = .ok completed
  state : State
  state_eq : state = after before completed.state
  beforeSafe : before.Safe
  safe : state.Safe

def Dropped.ticket {before : State} {id : Nat} (dropped : Dropped before id) : Ticket := dropped.completed.item

def retire (before : State) (id : Nat) : Except String (Dropped before id) := do
  if checked : before.check = true then
    match computed : Theory.Outstanding.complete before.handoff.work id with
    | .error error => throw error.describe
    | .ok completed =>
      return ⟨completed, computed, after before completed.state, rfl,
        (CampusWithdrawal.State.check_correct _).mp checked,
        after_safe before id ((CampusWithdrawal.State.check_correct _).mp checked) completed⟩
  else throw "The guarded handoff state violates its contract."

inductive Result (before : State) (id : Nat) where
  | rejected (dropped : Dropped before id)
  | processed (operation : CampusWithdrawal.Result)
      (computed : CampusWithdrawal.step before (.operation (.serve id)) = .ok operation)

def Result.state {before : State} {id : Nat} : Result before id → State
  | .rejected dropped => dropped.state
  | .processed operation _ => operation.state

theorem Result.safe {before : State} {id : Nat} (result : Result before id) : result.state.Safe := by
  cases result with
  | rejected dropped => exact dropped.safe
  | processed operation _ => exact operation.safe

def serve (actualDecision : Bool) (before : State) (id : Nat) : Except String (Result before id) :=
  if actualDecision then
    match computed : CampusWithdrawal.step before (.operation (.serve id)) with
    | .error error => .error error
    | .ok operation => .ok (.processed operation computed)
  else Result.rejected <$> retire before id

theorem Dropped.tables_unchanged {before : State} {id : Nat} (dropped : Dropped before id) :
    dropped.state.handoff.gateways.primary = before.handoff.gateways.primary ∧
      dropped.state.handoff.gateways.standby = before.handoff.gateways.standby := by
  rw [dropped.state_eq]
  exact ⟨rfl, rfl⟩

theorem Dropped.metadata_unchanged {before : State} {id : Nat} (dropped : Dropped before id) :
    dropped.state.handoff.configurations = before.handoff.configurations ∧
      dropped.state.handoff.gateways.cache = before.handoff.gateways.cache ∧
      dropped.state.handoff.binding = before.handoff.binding ∧
      dropped.state.handoff.gateways.owners = before.handoff.gateways.owners ∧
      dropped.state.handoff.gateways.fenced = before.handoff.gateways.fenced ∧
      dropped.state.withdrawn = before.withdrawn ∧ dropped.state.archive = before.archive ∧
      dropped.state.handoff.gateways.epoch = before.handoff.gateways.epoch + 1 := by
  rw [dropped.state_eq]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem Dropped.provenance {before : State} {id : Nat} (dropped : Dropped before id) :
    dropped.ticket ∈ before.handoff.work.pending ∧ dropped.ticket.id = id ∧
      before.handoff.work.pending.Perm (dropped.ticket :: dropped.state.handoff.work.pending) ∧
      dropped.state.handoff.work.completed = before.handoff.work.completed ++ [dropped.ticket] ∧
      dropped.state.handoff.work.nextID = before.handoff.work.nextID := by
  rw [dropped.state_eq]
  exact ⟨dropped.completed.member, dropped.completed.selected, dropped.completed.pendingPerm,
    dropped.completed.history, dropped.completed.nextIDeq⟩

theorem Dropped.remaining {before : State} {id : Nat} (dropped : Dropped before id) :
    ∀ item ∈ dropped.state.handoff.work.pending, item ∈ before.handoff.work.pending := by
  intro item member
  exact dropped.provenance.2.2.1.mem_iff.mpr (List.mem_cons_of_mem _ member)

theorem Dropped.work_eq {before : State} {id : Nat} (dropped : Dropped before id) :
    dropped.state.handoff.work = dropped.completed.state := by
  rw [dropped.state_eq]
  rfl

theorem Dropped.count {before : State} {id : Nat} (dropped : Dropped before id) (gateway : Gateway) :
    before.handoff.outstanding gateway = dropped.state.handoff.outstanding gateway +
      (if dropped.ticket.value.gateway = gateway then 1 else 0) := by
  rw [SafeHandoff.State.outstanding_eq_count, SafeHandoff.State.outstanding_eq_count, dropped.work_eq]
  have counted := dropped.completed.count (fun ticket => decide (ticket.gateway = gateway))
  by_cases selected : dropped.completed.item.value.gateway = gateway <;>
    simpa [Dropped.ticket, selected] using counted

theorem Dropped.no_repeat {before : State} {id : Nat} (dropped : Dropped before id) :
    Theory.Outstanding.complete dropped.state.handoff.work id = .error .notPending := by
  rw [dropped.state_eq]
  exact dropped.completed.no_repeat dropped.beforeSafe.1.2.1

theorem retire_completes (before : State) (id : Nat) (safe : before.Safe)
    (pending : ∃ item ∈ before.handoff.work.pending, item.id = id) :
    ∃ dropped, retire before id = .ok dropped := by
  obtain ⟨item, member, selected⟩ := pending
  subst id
  obtain ⟨completed, completedEq⟩ := Theory.Outstanding.complete_completes before.handoff.work item member
  have checked := (CampusWithdrawal.State.check_correct _).mpr safe
  cases actual : retire before item.id with
  | ok dropped => exact ⟨dropped, rfl⟩
  | error error =>
    simp only [retire, checked, dite_true] at actual
    split at actual
    · rename_i failed
      cases completedEq.symm.trans failed
    · simp only [pure, Except.pure] at actual
      cases actual


theorem serve_true (before : State) (id : Nat) (operation : CampusWithdrawal.Result)
    (computed : CampusWithdrawal.step before (.operation (.serve id)) = .ok operation) :
    serve true before id = .ok (.processed operation computed) := by
  simp only [serve, ite_true]
  split
  · rename_i failed
    cases computed.symm.trans failed
  · rename_i actual accepted
    have same := Except.ok.inj (accepted.symm.trans computed)
    subst actual
    rfl

theorem serve_completes (actualDecision : Bool) (before : State) (id : Nat) (safe : before.Safe)
    (pending : ∃ item ∈ before.handoff.work.pending, item.id = id) :
    ∃ result, serve actualDecision before id = .ok result ∧ result.state.Safe := by
  cases actualDecision
  · obtain ⟨dropped, computed⟩ := retire_completes before id safe pending
    exact ⟨.rejected dropped, by simp [serve, computed, Functor.map, Except.map], dropped.safe⟩
  · have allowed : before.operationAllowed (.serve id) = true := by
      cases withdrawn : before.withdrawn <;> simp [CampusWithdrawal.State.operationAllowed, withdrawn]
    obtain ⟨operation, _, computed, _⟩ := CampusWithdrawal.operation_completes before (.serve id) safe allowed (.serve id pending)
    exact ⟨.processed operation computed, serve_true before id operation computed, operation.safe⟩

theorem serve_rejected (actualDecision : Bool) (before : State) (id : Nat) (dropped : Dropped before id)
    (accepted : serve actualDecision before id = .ok (.rejected dropped)) :
    actualDecision = false ∧ retire before id = .ok dropped := by
  cases actualDecision
  · cases computed : retire before id with
    | error error => simp [serve, computed, Functor.map, Except.map] at accepted
    | ok actual =>
      simp only [serve, Bool.false_eq_true, ite_false, computed, Functor.map, Except.map,
        Except.ok.injEq, Result.rejected.injEq] at accepted
      cases accepted
      exact ⟨rfl, rfl⟩
  · simp only [serve, ite_true] at accepted
    split at accepted <;> cases accepted

theorem serve_processed (actualDecision : Bool) (before : State) (id : Nat) (operation : CampusWithdrawal.Result)
    (computed : CampusWithdrawal.step before (.operation (.serve id)) = .ok operation)
    (accepted : serve actualDecision before id = .ok (.processed operation computed)) : actualDecision = true := by
  cases actualDecision
  · cases retired : retire before id <;> simp [serve, retired, Functor.map, Except.map] at accepted
  · rfl

end Netlib.Protocol.GuardedHandoff
