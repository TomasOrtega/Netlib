import Netlib.Protocol.CampusWithdrawal

/-!
# Ordinary processing outside the route-ticket stream

A probe uses the chosen gateway's actual current pipeline and table.
It does not allocate, serve, or retire a route ticket.
-/

namespace Netlib.Protocol.IngressProbe

open Packet
open StatefulFailover (Gateway)
abbrev State := CampusWithdrawal.State

structure Input where
  gateway : Gateway
  direction : FlowNAT.Direction
  source : SafeHandoff.Source
  candidate : Option NetfilterNAT.Entry := none

def Input.wire (input : Input) : WireForwarding.Input := ⟨0, input.source.packet, input.candidate⟩

def BindingReady (before : State) (input : Input) : Prop :=
  match before.handoff.binding with
  | none => True
  | some entry => TrackedFlow.Ready (before.handoff.gateways.table input.gateway) entry ∧
    input.source.packet.header = entry.flow.input input.direction ∧ input.candidate = none

def bindingReady (before : State) (input : Input) : Bool :=
  match before.handoff.binding with
  | none => true
  | some entry => TrackedFlow.ready (before.handoff.gateways.table input.gateway) entry &&
    decide (input.source.packet.header = entry.flow.input input.direction) && input.candidate.isNone

theorem bindingReady_correct (before : State) (input : Input) : bindingReady before input = true ↔ BindingReady before input := by
  cases binding : before.handoff.binding <;>
    simp [bindingReady, BindingReady, binding, TrackedFlow.ready_correct, and_assoc]

private theorem wire_eq (input : Input) (entry : NetfilterNAT.Entry) (supported : SafeHandoff.FlowSupported entry)
    (candidate : input.candidate = none) : input.wire = TrackedFlow.wireInput entry input.direction input.source.packet := by
  have zone : entry.flow.zone input.direction = 0 := by
    cases direction : input.direction
    · exact supported.2.2.1
    · exact supported.2.2.2.1
  simp only [Input.wire, TrackedFlow.wireInput, candidate, zone]

private def after (before : State) (input : Input) (tracker : ConntrackLifecycle.State) : State :=
  { before with
    handoff := { before.handoff with
      gateways := { (before.handoff.gateways.write input.gateway tracker) with epoch := before.handoff.gateways.epoch + 1 } } }

private theorem after_safe (before : State) (input : Input) (safe : before.Safe)
    (unfenced : before.handoff.gateways.isFenced input.gateway = false) (attached : BindingReady before input)
    (outcome : WireForwarding.Outcome input.source.packet)
    (computed : WireForwarding.step (before.handoff.configurations input.gateway).pipeline
      (before.handoff.gateways.table input.gateway) input.wire = .ok outcome) : (after before input outcome.state).Safe := by
  let next := after before input outcome.state
  have owners : next.handoff.gateways.owners = before.handoff.gateways.owners := by cases gateway : input.gateway <;> simp [next, after, gateway, StatefulFailover.State.write]
  have fenced : next.handoff.gateways.fenced = before.handoff.gateways.fenced := by cases gateway : input.gateway <;> simp [next, after, gateway, StatefulFailover.State.write]
  have valid : next.handoff.gateways.Valid := before.handoff.gateways.write_valid input.gateway outcome.state safe.1.1 outcome.valid
  have uses : ∀ gateway, next.handoff.uses gateway = true → before.handoff.uses gateway = true :=
    SafeHandoff.State.uses_mono before.handoff next.handoff owners
      (fun item member => before.handoff.uses_pending item member)
  have unblocked := SafeHandoff.State.unfenced_transfer before.handoff next.handoff safe.1.2.2.1 uses fenced
  have nextSafe : next.handoff.Safe := by
    cases binding : before.handoff.binding with
    | none =>
      refine ⟨valid, safe.1.2.1, unblocked, ?_⟩
      simpa only [next, after, binding] using safe.1.2.2.2
    | some entry =>
      have flow := safe.1.flow binding
      have ready : TrackedFlow.Ready (before.handoff.gateways.table input.gateway) entry ∧
          input.source.packet.header = entry.flow.input input.direction ∧ input.candidate = none := by
        simpa only [BindingReady, binding] using attached
      have zone : entry.flow.zone input.direction = 0 := by
        cases direction : input.direction
        · exact flow.1.2.2.1
        · exact flow.1.2.2.2.1
      have actual : WireForwarding.step (before.handoff.configurations input.gateway).pipeline
          (before.handoff.gateways.table input.gateway)
          (TrackedFlow.wireInput entry input.direction input.source.packet) = .ok outcome := by
        have copied := computed
        change WireForwarding.step (before.handoff.configurations input.gateway).pipeline
          (before.handoff.gateways.table input.gateway) ⟨0, input.source.packet, input.candidate⟩ = .ok outcome at copied
        rw [ready.2.2] at copied
        change WireForwarding.step (before.handoff.configurations input.gateway).pipeline
          (before.handoff.gateways.table input.gateway) ⟨entry.flow.zone input.direction, input.source.packet, none⟩ = .ok outcome
        rw [zone]
        exact copied
      have retained := (TrackedFlow.step_facts (before.handoff.configurations input.gateway).pipeline
        (before.handoff.gateways.table input.gateway) entry input.direction input.source.packet
        (safe.1.table_valid input.gateway) ready.1 flow.1.2.1 ready.2.1 outcome actual).2.2.1
      have primary : TrackedFlow.Ready next.handoff.gateways.primary entry := by
        cases gateway : input.gateway
        · simpa only [next, after, gateway, StatefulFailover.State.write] using retained
        · simpa only [next, after, gateway, StatefulFailover.State.write] using flow.2.1
      have standby : next.handoff.uses .standby = true → TrackedFlow.Ready next.handoff.gateways.standby entry := by
        intro used
        cases gateway : input.gateway
        · simpa only [next, after, gateway, StatefulFailover.State.write] using flow.2.2.2 (uses .standby used)
        · simpa only [next, after, gateway, StatefulFailover.State.write] using retained
      exact SafeHandoff.State.safe_of_flow next.handoff entry binding valid safe.1.2.1 unblocked flow.1 primary flow.2.2.1 standby
  refine ⟨nextSafe, ?_⟩
  cases withdrawn : before.withdrawn with
  | false => simpa only [next, after, withdrawn, Bool.false_eq_true, ite_false] using safe.2
  | true =>
    have ready := before.withdrawn_ready safe withdrawn
    have selected : input.gateway = .standby := by
      cases gateway : input.gateway
      · have closed := ready.2.2.2.2
        rw [gateway] at unfenced
        simp [closed] at unfenced
      · rfl
    change if before.withdrawn then next.Ready ∧ next.archive = some next.handoff.gateways.primary else next.archive = none
    rw [withdrawn]
    have archive := before.withdrawn_archive safe withdrawn
    constructor
    · simpa only [CampusWithdrawal.State.Ready, next, after, selected, StatefulFailover.State.write, SafeHandoff.State.outstanding, StatefulFailover.State.isFenced] using ready
    · simpa only [next, after, selected, StatefulFailover.State.write] using archive

structure Result (before : State) (input : Input) where
  outcome : WireForwarding.Outcome input.source.packet
  computed : WireForwarding.step (before.handoff.configurations input.gateway).pipeline
    (before.handoff.gateways.table input.gateway) input.wire = .ok outcome
  state : State
  state_eq : state = after before input outcome.state
  beforeSafe : before.Safe
  safe : state.Safe

def process (before : State) (input : Input) : Except String (Result before input) := do
  if checked : before.check = true then
    if before.withdrawn && decide (input.gateway = .primary) then throw "The primary probe target has been physically withdrawn."
    if blocked : before.handoff.gateways.isFenced input.gateway = true then throw "The probe gateway is fenced."
    else if ready : bindingReady before input = true then
      match computed : WireForwarding.step (before.handoff.configurations input.gateway).pipeline
          (before.handoff.gateways.table input.gateway) input.wire with
      | .error error => throw error.describe
      | .ok outcome =>
        return ⟨outcome, computed, after before input outcome.state, rfl,
          (CampusWithdrawal.State.check_correct _).mp checked,
          after_safe before input ((CampusWithdrawal.State.check_correct _).mp checked)
            (by simpa using blocked) ((bindingReady_correct _ _).mp ready) outcome computed⟩
    else throw "A protected probe requires its ready binding, matching direction, and no fresh candidate."
  else throw "The probe state violates its contract."

theorem Result.selected_table {before : State} {input : Input} (result : Result before input) :
    result.state.handoff.gateways.table input.gateway = result.outcome.state := by
  have same : result.state = after before input result.outcome.state := result.state_eq
  rw [same]
  change (before.handoff.gateways.write input.gateway result.outcome.state).table input.gateway = _
  exact StatefulFailover.State.table_write _ _ _

theorem Result.other_table {before : State} {input : Input} (result : Result before input) (other : Gateway)
    (different : other ≠ input.gateway) :
    result.state.handoff.gateways.table other = before.handoff.gateways.table other := by
  have same : result.state = after before input result.outcome.state := result.state_eq
  rw [same]
  change (before.handoff.gateways.write input.gateway result.outcome.state).table other = _
  cases gateway : input.gateway <;> cases other <;> simp_all [StatefulFailover.State.write, StatefulFailover.State.table]

theorem Result.metadata_unchanged {before : State} {input : Input} (result : Result before input) :
    result.state.handoff.work = before.handoff.work ∧ result.state.handoff.configurations = before.handoff.configurations ∧
      result.state.handoff.gateways.cache = before.handoff.gateways.cache ∧
      result.state.handoff.binding = before.handoff.binding ∧ result.state.handoff.gateways.owners = before.handoff.gateways.owners ∧
      result.state.handoff.gateways.fenced = before.handoff.gateways.fenced ∧
      result.state.withdrawn = before.withdrawn ∧ result.state.archive = before.archive ∧
      result.state.handoff.gateways.epoch = before.handoff.gateways.epoch + 1 := by
  have same : result.state = after before input result.outcome.state := result.state_eq
  rw [same]
  cases gateway : input.gateway <;> simp [after, gateway, StatefulFailover.State.write]

theorem Result.archived_primary {before : State} {input : Input} (result : Result before input)
    (withdrawn : before.withdrawn = true) :
    result.state.archive = before.archive ∧ result.state.handoff.gateways.primary = before.handoff.gateways.primary := by
  have later := result.metadata_unchanged.2.2.2.2.2.2.1.trans withdrawn
  have source := before.withdrawn_archive result.beforeSafe withdrawn
  have target := result.state.withdrawn_archive result.safe later
  have unchanged := result.metadata_unchanged.2.2.2.2.2.2.2.1
  refine ⟨unchanged, ?_⟩
  exact Option.some.inj (target.symm.trans (unchanged.trans source))

private theorem not_withdrawn_primary (before : State) (input : Input) (safe : before.Safe)
    (unfenced : before.handoff.gateways.isFenced input.gateway = false) :
    (before.withdrawn && decide (input.gateway = .primary)) = false := by
  cases withdrawn : before.withdrawn
  · simp
  · have ready := before.withdrawn_ready safe withdrawn
    cases gateway : input.gateway
    · rw [gateway] at unfenced
      simp [ready.2.2.2.2] at unfenced
    · simp

theorem process_of_wire (before : State) (input : Input) (safe : before.Safe)
    (unfenced : before.handoff.gateways.isFenced input.gateway = false) (attached : BindingReady before input)
    (outcome : WireForwarding.Outcome input.source.packet)
    (computed : WireForwarding.step (before.handoff.configurations input.gateway).pipeline
      (before.handoff.gateways.table input.gateway) input.wire = .ok outcome) :
    ∃ result, process before input = .ok result ∧ result.outcome = outcome := by
  have checked := (CampusWithdrawal.State.check_correct _).mpr safe
  have ready := (bindingReady_correct _ _).mpr attached
  have live := not_withdrawn_primary before input safe unfenced
  cases actual : process before input with
  | ok result =>
    exact ⟨result, rfl, Except.ok.inj (result.computed.symm.trans computed)⟩
  | error error =>
    simp only [process, checked, dite_true, live, Bool.false_eq_true, ite_false, unfenced, dite_false,
      ready, bind, Except.bind, pure, Except.pure] at actual
    split at actual
    · rename_i failed
      cases computed.symm.trans failed
    · cases actual

theorem protected_completes (before : State) (input : Input) (entry : NetfilterNAT.Entry) (safe : before.Safe)
    (binding : before.handoff.binding = some entry)
    (unfenced : before.handoff.gateways.isFenced input.gateway = false)
    (ready : TrackedFlow.Ready (before.handoff.gateways.table input.gateway) entry)
    (selected : input.source.packet.header = entry.flow.input input.direction) (candidate : input.candidate = none) :
    ∃ result, process before input = .ok result := by
  have flow := safe.1.flow binding
  obtain ⟨outcome, computed, _⟩ := TrackedFlow.step_completes
    (before.handoff.configurations input.gateway).pipeline (before.handoff.gateways.table input.gateway)
    entry input.direction input.source.packet (safe.1.table_valid _) ready flow.1.2.1 selected input.source.bytes input.source.encoded
  have zone : entry.flow.zone input.direction = 0 := by
    cases direction : input.direction
    · exact flow.1.2.2.1
    · exact flow.1.2.2.2.1
  have actual : WireForwarding.step (before.handoff.configurations input.gateway).pipeline
      (before.handoff.gateways.table input.gateway) input.wire = .ok outcome := by
    change WireForwarding.step (before.handoff.configurations input.gateway).pipeline
      (before.handoff.gateways.table input.gateway) ⟨entry.flow.zone input.direction, input.source.packet, none⟩ = .ok outcome at computed
    rw [zone] at computed
    change WireForwarding.step (before.handoff.configurations input.gateway).pipeline
      (before.handoff.gateways.table input.gateway) ⟨0, input.source.packet, input.candidate⟩ = .ok outcome
    rw [candidate]
    exact computed
  have attached : BindingReady before input := by simpa only [BindingReady, binding] using And.intro ready ⟨selected, candidate⟩
  obtain ⟨result, accepted, _⟩ := process_of_wire before input safe unfenced attached outcome actual
  exact ⟨result, accepted⟩


theorem process_checks (before : State) (input : Input) (result : Result before input)
    (accepted : process before input = .ok result) :
    before.handoff.gateways.isFenced input.gateway = false ∧ BindingReady before input ∧
      (before.withdrawn && decide (input.gateway = .primary)) = false := by
  have checked := (CampusWithdrawal.State.check_correct _).mpr result.beforeSafe
  have live : (before.withdrawn && decide (input.gateway = .primary)) = false := by
    by_cases blocked : (before.withdrawn && decide (input.gateway = .primary)) = true
    · simp only [process, checked, dite_true, blocked, ite_true, throw, throwThe, bind, Except.bind] at accepted
      cases accepted
    · exact Bool.eq_false_iff.mpr blocked
  have unfenced : before.handoff.gateways.isFenced input.gateway = false := by
    by_cases blocked : before.handoff.gateways.isFenced input.gateway = true
    · simp only [process, checked, dite_true, live, Bool.false_eq_true, ite_false, blocked,
        throw, throwThe, bind, Except.bind] at accepted
      cases accepted
    · exact Bool.eq_false_iff.mpr blocked
  have attached : bindingReady before input = true := by
    by_cases ready : bindingReady before input = true
    · exact ready
    · simp only [process, checked, dite_true, live, Bool.false_eq_true, ite_false, unfenced,
        dite_false, ready, throw, throwThe, bind, Except.bind, pure, Except.pure] at accepted
      cases accepted
  exact ⟨unfenced, (bindingReady_correct _ _).mp attached, live⟩

theorem protected_facts (before : State) (input : Input) (result : Result before input)
    (accepted : process before input = .ok result) (entry : NetfilterNAT.Entry)
    (binding : before.handoff.binding = some entry) :
    input.source.packet.header = entry.flow.input input.direction ∧ input.candidate = none ∧
      result.outcome.attachment = ⟨entry, input.direction,
        TrackedFlow.classification (before.handoff.gateways.table input.gateway) entry input.direction, false⟩ ∧
      result.state.handoff.gateways.table input.gateway =
        TrackedFlow.afterReply (before.handoff.gateways.table input.gateway) entry input.direction ∧
      TrackedFlow.Ready (result.state.handoff.gateways.table input.gateway) entry := by
  have checked := (process_checks before input result accepted).2.1
  have ready : TrackedFlow.Ready (before.handoff.gateways.table input.gateway) entry ∧
      input.source.packet.header = entry.flow.input input.direction ∧ input.candidate = none := by
    simpa only [BindingReady, binding] using checked
  have flow := result.beforeSafe.1.flow binding
  have zone : entry.flow.zone input.direction = 0 := by
    cases direction : input.direction
    · exact flow.1.2.2.1
    · exact flow.1.2.2.2.1
  have computed := result.computed
  change WireForwarding.step (before.handoff.configurations input.gateway).pipeline
    (before.handoff.gateways.table input.gateway) ⟨0, input.source.packet, input.candidate⟩ = .ok result.outcome at computed
  rw [ready.2.2] at computed
  have actual : WireForwarding.step (before.handoff.configurations input.gateway).pipeline
      (before.handoff.gateways.table input.gateway)
      (TrackedFlow.wireInput entry input.direction input.source.packet) = .ok result.outcome := by
    change WireForwarding.step (before.handoff.configurations input.gateway).pipeline
      (before.handoff.gateways.table input.gateway) ⟨entry.flow.zone input.direction, input.source.packet, none⟩ = .ok result.outcome
    rw [zone]
    exact computed
  have facts := TrackedFlow.step_facts (before.handoff.configurations input.gateway).pipeline
    (before.handoff.gateways.table input.gateway) entry input.direction input.source.packet
    (result.beforeSafe.1.table_valid _) ready.1 flow.1.2.1 ready.2.1 result.outcome actual
  exact ⟨ready.2.1, ready.2.2, facts.1, result.selected_table.trans facts.2.1,
    by rw [result.selected_table]; exact facts.2.2.1⟩

end Netlib.Protocol.IngressProbe
