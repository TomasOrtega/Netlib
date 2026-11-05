import Netlib.Protocol.SafeHandoffFacts

/-!
# Planned withdrawal with an archived primary

The handoff snapshot retains historical primary state after physical withdrawal.
Subsequent operations cannot query or process live primary state.
-/

namespace Netlib.Protocol.CampusWithdrawal

open StatefulFailover (Gateway)

structure State where
  handoff : SafeHandoff.State
  withdrawn : Bool := false
  archive : Option ConntrackLifecycle.State := none

def State.initial (primary standby : SafeHandoff.Configuration) : State :=
  ⟨SafeHandoff.State.initial primary standby, false, none⟩

def State.Ready (state : State) : Prop :=
  state.handoff.binding.isSome = true ∧
    state.handoff.gateways.owners.client = .standby ∧ state.handoff.gateways.owners.server = .standby ∧
    state.handoff.outstanding .primary = 0 ∧ state.handoff.gateways.isFenced .primary = true

def State.ready (state : State) : Bool :=
  state.handoff.binding.isSome && decide (state.handoff.gateways.owners.client = .standby) &&
    decide (state.handoff.gateways.owners.server = .standby) &&
    decide (state.handoff.outstanding .primary = 0) && state.handoff.gateways.isFenced .primary

theorem State.ready_correct (state : State) : state.ready = true ↔ state.Ready := by
  simp [ready, Ready, and_assoc]

def State.Safe (state : State) : Prop :=
  state.handoff.Safe ∧
    if state.withdrawn then state.Ready ∧ state.archive = some state.handoff.gateways.primary
    else state.archive = none

def State.check (state : State) : Bool :=
  state.handoff.check && if state.withdrawn then
    state.ready && decide (state.archive = some state.handoff.gateways.primary)
    else decide (state.archive = none)

theorem State.check_correct (state : State) : state.check = true ↔ state.Safe := by
  cases withdrawn : state.withdrawn <;>
    simp [State.check, State.Safe, SafeHandoff.State.check_correct, State.ready_correct, withdrawn]

theorem State.initial_safe (primary standby : SafeHandoff.Configuration) : (State.initial primary standby).Safe :=
  ⟨SafeHandoff.State.initial_safe primary standby, rfl⟩

def State.operationAllowed (state : State) (event : SafeHandoff.Event) : Bool :=
  if !state.withdrawn then true else match event with
    | .assign .. | .serve .. | .install .standby _ | .forget => true
    | _ => false

inductive Event where
  | operation (event : SafeHandoff.Event)
  | withdraw

structure RawResult where
  state : State
  operation : Option SafeHandoff.Result

structure Result extends RawResult where
  safe : state.Safe

def core (before : State) : Event → Except String RawResult
  | .operation event => do
    if !before.operationAllowed event then throw "The withdrawn primary permits no live operation."
    let result ← SafeHandoff.step before.handoff event
    return ⟨{ before with handoff := result.state }, some result⟩
  | .withdraw => do
    if before.withdrawn then throw "The primary is already withdrawn."
    if !before.ready then throw "Withdraw only after both routes move, primary work drains, and primary fencing completes."
    return ⟨{ before with withdrawn := true, archive := some before.handoff.gateways.primary }, none⟩

def step (before : State) (event : Event) : Except String Result := do
  if _checked : before.check = true then
    let raw ← core before event
    if after : raw.state.check = true then
      return { raw with safe := (State.check_correct _).mp after }
    else throw "The operation violates the primary withdrawal contract."
  else throw "The withdrawal state violates its contract."

theorem step_safe (before : State) (event : Event) (result : Result)
    (_accepted : step before event = .ok result) : result.state.Safe := result.safe

theorem State.withdrawn_ready (state : State) (safe : state.Safe) (withdrawn : state.withdrawn = true) : state.Ready := by
  have fields : state.Ready ∧ state.archive = some state.handoff.gateways.primary := by
    simpa only [withdrawn, Bool.true_eq_false, ite_true] using safe.2
  exact fields.1

theorem State.withdrawn_archive (state : State) (safe : state.Safe) (withdrawn : state.withdrawn = true) :
    state.archive = some state.handoff.gateways.primary := by
  have fields : state.Ready ∧ state.archive = some state.handoff.gateways.primary := by
    simpa only [withdrawn, Bool.true_eq_false, ite_true] using safe.2
  exact fields.2

theorem State.pending_standby (state : State) (safe : state.Safe) (withdrawn : state.withdrawn = true)
    (item : Theory.Outstanding.Item SafeHandoff.Ticket) (member : item ∈ state.handoff.work.pending) :
    item.value.gateway = .standby := by
  have ready := state.withdrawn_ready safe withdrawn
  have outside := (SafeHandoff.State.outstanding_zero _ _).mp ready.2.2.2.1 item member
  cases assigned : item.value.gateway
  · exact False.elim (outside assigned)
  · rfl

theorem step_of_core (before : State) (event : Event) (raw : RawResult)
    (safe : before.Safe) (computed : core before event = .ok raw) (after : raw.state.Safe) :
    ∃ result, step before event = .ok result ∧ result.toRawResult = raw := by
  have checked := (State.check_correct _).mpr safe
  have afterChecked := (State.check_correct _).mpr after
  exact ⟨{ raw with safe := after }, by simp only [step, checked, dite_true, computed, bind, Except.bind,
    afterChecked, pure, Except.pure], rfl⟩

theorem withdraw_completes (before : State) (safe : before.Safe) (active : before.withdrawn = false)
    (ready : before.Ready) :
    ∃ result, step before .withdraw = .ok result ∧ result.state.Safe ∧
      result.state.withdrawn = true ∧ result.state.handoff = before.handoff ∧
      result.state.archive = some before.handoff.gateways.primary ∧ result.operation = none := by
  let raw : RawResult := ⟨{ before with withdrawn := true, archive := some before.handoff.gateways.primary }, none⟩
  have after : raw.state.Safe := ⟨safe.1, ready, rfl⟩
  have computed : core before .withdraw = .ok raw := by
    simp only [core, raw, active, Bool.false_eq_true, ite_false, (State.ready_correct _).mpr ready,
      Bool.not_true, pure, Except.pure]
  obtain ⟨result, accepted, same⟩ := step_of_core before .withdraw raw safe computed after
  refine ⟨result, accepted, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [← same] using after
  · exact congrArg (fun result : RawResult => result.state.withdrawn) same
  · exact congrArg (fun result : RawResult => result.state.handoff) same
  · exact congrArg (fun result : RawResult => result.state.archive) same
  · exact congrArg RawResult.operation same

private theorem operation_fields (before : State) (event : SafeHandoff.Event) (result : SafeHandoff.Result)
    (safe : before.Safe) (withdrawn : before.withdrawn = true)
    (allowed : before.operationAllowed event = true)
    (accepted : SafeHandoff.step before.handoff event = .ok result) :
    result.state.gateways.primary = before.handoff.gateways.primary ∧
      result.state.binding = before.handoff.binding ∧ result.state.gateways.owners = before.handoff.gateways.owners ∧
      result.state.gateways.fenced = before.handoff.gateways.fenced := by
  obtain ⟨_, raw, computed, same⟩ := SafeHandoff.step_core before.handoff event result accepted
  have fields : raw.state.gateways.primary = before.handoff.gateways.primary ∧
      raw.state.binding = before.handoff.binding ∧ raw.state.gateways.owners = before.handoff.gateways.owners ∧
      raw.state.gateways.fenced = before.handoff.gateways.fenced := by
    cases event with
    | assign direction source =>
      simp only [SafeHandoff.core] at computed
      cases binding : before.handoff.binding with
      | none => simp [binding, throw] at computed
      | some entry =>
        simp only [binding] at computed
        split at computed
        · split at computed
          · simp [throw, bind, Except.bind] at computed
          · split at computed
            · simp [throw, bind, Except.bind] at computed
            · simp only [pure, Except.pure] at computed
              cases computed
              exact ⟨rfl, rfl, rfl, rfl⟩
        · simp [throw] at computed
    | serve id =>
      obtain ⟨completed, outcome, completedEq, _, binding, unfenced, ready, served, _⟩ :=
        SafeHandoff.core_serve_facts before.handoff id raw computed
      have selected := before.pending_standby safe withdrawn completed.item completed.member
      have checked := (TrackedFlow.ready_correct _ _).mpr ready
      simp only [SafeHandoff.core, completedEq, Except.mapError, bind, Except.bind, binding,
        ne_eq, not_true_eq_false, ite_false, unfenced, Bool.false_eq_true, checked, Bool.not_true,
        served, pure, Except.pure] at computed
      cases computed
      simp only [selected, StatefulFailover.State.write]
      exact ⟨rfl, binding.symm, rfl, rfl⟩
    | install gateway configuration =>
      cases gateway with
      | primary => simp [State.operationAllowed, withdrawn] at allowed
      | standby => cases computed; exact ⟨rfl, rfl, rfl, rfl⟩
    | forget =>
      change (do
        let result ← StatefulFailover.step before.handoff.gateways .forget
        pure (⟨{ before.handoff with gateways := result.state }, none, none, result.packet⟩ : SafeHandoff.RawResult)) = .ok raw at computed
      cases next : StatefulFailover.step before.handoff.gateways .forget with
      | error error => simp [next, bind, Except.bind] at computed
      | ok actual =>
        simp only [next, bind, Except.bind, pure, Except.pure] at computed
        cases computed
        simp only [StatefulFailover.step] at next
        split at next
        · simp only [pure, Except.pure] at next
          cases next
          exact ⟨rfl, rfl, rfl, rfl⟩
        · simp [throw] at next
    | establish input => simp [State.operationAllowed, withdrawn] at allowed
    | stage zone key => simp [State.operationAllowed, withdrawn] at allowed
    | commit timeout => simp [State.operationAllowed, withdrawn] at allowed
    | handoff leg gateway => simp [State.operationAllowed, withdrawn] at allowed
    | fence gateway => simp [State.operationAllowed, withdrawn] at allowed
  simpa only [← same] using fields

private theorem operation_safe (before : State) (event : SafeHandoff.Event) (result : SafeHandoff.Result)
    (safe : before.Safe) (allowed : before.operationAllowed event = true)
    (accepted : SafeHandoff.step before.handoff event = .ok result) :
    ({ before with handoff := result.state } : State).Safe := by
  refine ⟨result.safe, ?_⟩
  cases withdrawn : before.withdrawn with
  | false => simpa only [withdrawn, Bool.false_eq_true, ite_false] using safe.2
  | true =>
    have ready := before.withdrawn_ready safe withdrawn
    obtain ⟨primary, binding, owners, fenced⟩ := operation_fields before event result safe withdrawn allowed accepted
    have afterReady : ({ before with handoff := result.state } : State).Ready := by
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · simpa only [binding] using ready.1
      · simpa only [owners] using ready.2.1
      · simpa only [owners] using ready.2.2.1
      · apply (SafeHandoff.State.outstanding_zero _ _).mpr
        intro item member assigned
        have unfenced := result.safe.unfenced .primary (by simpa only [assigned] using result.state.uses_pending item member)
        have primaryFenced : result.state.gateways.isFenced .primary = true := by
          simpa only [StatefulFailover.State.isFenced, fenced] using ready.2.2.2.2
        simp [primaryFenced] at unfenced
      · simpa only [StatefulFailover.State.isFenced, fenced] using ready.2.2.2.2
    have archive := before.withdrawn_archive safe withdrawn
    change if true then _ else _
    exact ⟨afterReady, by simpa only [primary] using archive⟩

theorem operation_completes (before : State) (event : SafeHandoff.Event) (safe : before.Safe)
    (allowed : before.operationAllowed event = true) (admissible : SafeHandoff.Admissible before.handoff event) :
    ∃ result operation, step before (.operation event) = .ok result ∧ result.operation = some operation ∧
      SafeHandoff.step before.handoff event = .ok operation ∧ result.state.handoff = operation.state ∧ result.state.Safe := by
  obtain ⟨operation, accepted, _⟩ := SafeHandoff.admissible_progress before.handoff event safe.1 admissible
  let raw : RawResult := ⟨{ before with handoff := operation.state }, some operation⟩
  have after : raw.state.Safe := operation_safe before event operation safe allowed accepted
  have computed : core before (.operation event) = .ok raw := by
    simp only [core, raw, allowed, Bool.not_true, Bool.false_eq_true, ite_false, accepted, bind, Except.bind, pure, Except.pure]
  obtain ⟨result, checked, same⟩ := step_of_core before (.operation event) raw safe computed after
  exact ⟨result, operation, checked, congrArg RawResult.operation same, accepted,
    congrArg (fun result : RawResult => result.state.handoff) same, by simpa only [← same] using after⟩


theorem step_core (before : State) (event : Event) (result : Result)
    (accepted : step before event = .ok result) :
    before.Safe ∧ ∃ raw, core before event = .ok raw ∧ result.toRawResult = raw := by
  unfold step at accepted
  split at accepted
  · rename_i checked
    cases computed : core before event with
    | error error => simp [computed, bind, Except.bind] at accepted
    | ok raw =>
      simp only [computed, bind, Except.bind] at accepted
      split at accepted
      · simp only [pure, Except.pure] at accepted
        cases accepted
        exact ⟨(State.check_correct _).mp checked, raw, rfl, rfl⟩
      · simp [throw] at accepted
  · simp [throw] at accepted

theorem step_operation (before : State) (event : SafeHandoff.Event) (result : Result)
    (accepted : step before (.operation event) = .ok result) :
    before.operationAllowed event = true ∧ ∃ operation,
      SafeHandoff.step before.handoff event = .ok operation ∧ result.operation = some operation ∧
      result.state.handoff = operation.state ∧ result.state.withdrawn = before.withdrawn ∧
      result.state.archive = before.archive := by
  obtain ⟨_, raw, computed, same⟩ := step_core before (.operation event) result accepted
  simp only [core] at computed
  split at computed
  · simp [throw, bind, Except.bind] at computed
  · rename_i allowed
    cases operationEq : SafeHandoff.step before.handoff event with
    | error error => simp [operationEq, bind, Except.bind] at computed
    | ok operation =>
      simp only [operationEq, bind, Except.bind, pure, Except.pure] at computed
      cases computed
      exact ⟨by simpa using allowed, operation, rfl,
        congrArg RawResult.operation same, congrArg (fun raw => raw.state.handoff) same,
        congrArg (fun raw => raw.state.withdrawn) same, congrArg (fun raw => raw.state.archive) same⟩

theorem step_withdraw (before : State) (result : Result) (accepted : step before .withdraw = .ok result) :
    before.withdrawn = false ∧ before.Ready ∧ result.state.withdrawn = true ∧
      result.state.handoff = before.handoff ∧ result.state.archive = some before.handoff.gateways.primary ∧
      result.operation = none := by
  obtain ⟨_, raw, computed, same⟩ := step_core before .withdraw result accepted
  simp only [core] at computed
  split at computed
  · simp [throw, bind, Except.bind] at computed
  · rename_i active
    split at computed
    · simp [throw, bind, Except.bind] at computed
    · rename_i ready
      simp only [pure, Except.pure] at computed
      cases computed
      exact ⟨by simpa using active, (State.ready_correct _).mp (by simpa using ready),
        congrArg (fun raw => raw.state.withdrawn) same, congrArg (fun raw => raw.state.handoff) same,
        congrArg (fun raw => raw.state.archive) same, congrArg RawResult.operation same⟩

inductive Admissible (before : State) : Event → Prop
  | operation (event : SafeHandoff.Event) (allowed : before.operationAllowed event = true)
      (admissible : SafeHandoff.Admissible before.handoff event) : Admissible before (.operation event)
  | withdraw (active : before.withdrawn = false) (ready : before.Ready) : Admissible before .withdraw

theorem admissible_progress (before : State) (event : Event) (safe : before.Safe) (allowed : Admissible before event) :
    ∃ result, step before event = .ok result ∧ result.state.Safe := by
  cases allowed with
  | operation event allowed admissible =>
    obtain ⟨result, _, accepted, _, _, _, after⟩ := operation_completes before event safe allowed admissible
    exact ⟨result, accepted, after⟩
  | withdraw active ready =>
    obtain ⟨result, accepted, after, _⟩ := withdraw_completes before safe active ready
    exact ⟨result, accepted, after⟩

def contract : Transition State Event where
  step before event after := Admissible before event ∧ ∃ result, step before event = .ok result ∧ result.state = after

theorem contract_invariant : contract.Invariant State.Safe := by
  intro before event after safe edge
  obtain ⟨allowed, result, accepted, rfl⟩ := edge
  obtain ⟨actual, computed, preserved⟩ := admissible_progress before event safe allowed
  have equal := Except.ok.inj (computed.symm.trans accepted)
  subst actual
  exact preserved

theorem arbitrary_interleavings (trace : contract.Trace initial events final) (safe : initial.Safe) :
    final.Safe ∧ ∀ event, Admissible final event → ∃ result, step final event = .ok result ∧ result.state.Safe := by
  have preserved := contract_invariant.trace safe trace
  exact ⟨preserved, fun event allowed => admissible_progress final event preserved allowed⟩

theorem archive_preserved (before : State) (event : Event) (result : Result) (withdrawn : before.withdrawn = true)
    (accepted : step before event = .ok result) :
    result.state.withdrawn = true ∧ result.state.archive = before.archive ∧
      result.state.handoff.gateways.primary = before.handoff.gateways.primary := by
  obtain ⟨safe, _, _, _⟩ := step_core before event result accepted
  cases event with
  | withdraw => have active := (step_withdraw before result accepted).1; simp [withdrawn] at active
  | operation event =>
    obtain ⟨allowed, operation, computed, _, handoff, retired, archive⟩ := step_operation before event result accepted
    have fields := operation_fields before event operation safe withdrawn allowed computed
    exact ⟨retired.trans withdrawn, archive, by rw [handoff]; exact fields.1⟩

theorem trace_archive (trace : contract.Trace initial events final) (withdrawn : initial.withdrawn = true) :
    final.withdrawn = true ∧ final.archive = initial.archive ∧
      final.handoff.gateways.primary = initial.handoff.gateways.primary := by
  induction trace with
  | nil => exact ⟨withdrawn, rfl, rfl⟩
  | cons edge rest ih =>
    obtain ⟨_, result, accepted, rfl⟩ := edge
    obtain ⟨retired, archive, primary⟩ := archive_preserved _ _ result withdrawn accepted
    obtain ⟨lastRetired, lastArchive, lastPrimary⟩ := ih retired
    exact ⟨lastRetired, lastArchive.trans archive, lastPrimary.trans primary⟩

theorem serve_service (before : State) (item : Theory.Outstanding.Item SafeHandoff.Ticket)
    (safe : before.Safe) (member : item ∈ before.handoff.work.pending)
    (live : 1 < item.value.source.packet.ip.packet.ttl.toNat)
    (routed : (Routing.nextHop (before.handoff.configurations item.value.gateway).pipeline.routes
      (TrackedFlow.destination item.value.entry item.value.direction).destination).isSome = true)
    (forward : Packet.StatefulACL.Policy.evaluate (before.handoff.configurations item.value.gateway).pipeline.forwardDefault
      (before.handoff.configurations item.value.gateway).pipeline.forward
      (TrackedFlow.classification (before.handoff.gateways.table item.value.gateway) item.value.entry item.value.direction)
      (TrackedFlow.destination item.value.entry item.value.direction) = .permit)
    (late : Packet.StatefulACL.Policy.evaluate (before.handoff.configurations item.value.gateway).pipeline.lateDefault
      (before.handoff.configurations item.value.gateway).pipeline.late
      (TrackedFlow.classification (before.handoff.gateways.table item.value.gateway) item.value.entry item.value.direction)
      (item.value.entry.flow.output item.value.direction) = .permit) :
    ∃ (result : Result) (operation : SafeHandoff.Result) (served : SafeHandoff.PacketResult)
      (emission : WireForwarding.Emission served.ticket.value.source.packet),
      step before (.operation (.serve item.id)) = .ok result ∧ result.operation = some operation ∧
      operation.served = some served ∧ served.ticket = item ∧
      served.configuration = before.handoff.configurations item.value.gateway ∧ served.outcome.output = some emission ∧
      emission.target = item.value.entry.flow.output item.value.direction ∧
      emission.decoded.datagram.payload = item.value.source.packet.datagram.payload ∧
      emission.decoded.ip.packet.ttl.toNat = item.value.source.packet.ip.packet.ttl.toNat - 1 := by
  obtain ⟨operation, served, emission, accepted, stored, selected, config, emitted, target, payload, ttl⟩ :=
    SafeHandoff.serve_service before.handoff item safe.1 member live routed forward late
  have allowed : before.operationAllowed (.serve item.id) = true := by
    cases withdrawn : before.withdrawn <;> simp [State.operationAllowed, withdrawn]
  obtain ⟨result, actual, checked, reported, computed, _, _⟩ := operation_completes before (.serve item.id) safe allowed
    (.serve item.id ⟨item, member, rfl⟩)
  have same := Except.ok.inj (computed.symm.trans accepted)
  subst actual
  exact ⟨result, operation, served, emission, checked, reported, stored, selected, config, emitted, target, payload, ttl⟩


theorem step_operation_facts (before : State) (event : SafeHandoff.Event) (result : Result)
    (accepted : step before (.operation event) = .ok result) :
    ∃ operation, result.operation = some operation ∧ SafeHandoff.step before.handoff event = .ok operation ∧
      result.state.handoff = operation.state ∧ result.state.withdrawn = before.withdrawn ∧ result.state.archive = before.archive := by
  obtain ⟨_, operation, computed, reported, handoff, withdrawn, archive⟩ := step_operation before event result accepted
  exact ⟨operation, reported, computed, handoff, withdrawn, archive⟩

theorem step_withdraw_facts (before : State) (result : Result) (accepted : step before .withdraw = .ok result) :
    before.withdrawn = false ∧ before.Ready ∧ result.state.withdrawn = true ∧
      result.state.handoff = before.handoff ∧ result.state.archive = some before.handoff.gateways.primary ∧
      result.operation = none := step_withdraw before result accepted

end Netlib.Protocol.CampusWithdrawal
