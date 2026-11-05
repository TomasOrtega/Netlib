import Netlib.Protocol.SafeHandoffCommonFacts
import Netlib.Protocol.SafeHandoffControlFacts
namespace Netlib.Protocol.SafeHandoff
open Packet
open StatefulFailover (Gateway Leg)

private def tick (state : State) : State :=
  { state with gateways := { state.gateways with epoch := state.gateways.epoch + 1 } }

private theorem tick_safe (state : State) (safe : state.Safe) : (tick state).Safe := safe

theorem assign_core_completes (before : State) (entry : NetfilterNAT.Entry) (direction : FlowNAT.Direction)
    (source : Source) (safe : before.Safe) (binding : before.binding = some entry)
    (selected : source.packet.header = entry.flow.input direction) :
    ∃ raw, core before (.assign direction source) = .ok raw ∧ raw.state.Safe := by
  let gateway := before.gateways.owners.get (leg direction)
  let ticket : Ticket := ⟨gateway, direction, entry, source, selected, before.gateways.epoch⟩
  let after : State := { before with work := Work.enqueue before.work ticket }
  have flow := safe.flow binding
  have used : before.uses gateway = true := before.uses_owner direction
  have unfenced := safe.unfenced gateway used
  have available := safe.ready binding gateway used
  have checked := (TrackedFlow.ready_correct _ _).mpr available
  have uses : ∀ gateway, after.uses gateway = true → before.uses gateway = true := by
    apply State.uses_mono before after rfl
    intro item member
    change item ∈ before.work.pending ++ [Theory.Outstanding.newItem before.work ticket] at member
    rcases List.mem_append.mp member with old | current
    · exact before.uses_pending item old
    · have equal := List.mem_singleton.mp current
      subst item
      exact used
  have pending : ∀ item ∈ after.work.pending, item.value.entry = entry := by
    intro item member
    change item ∈ before.work.pending ++ [Theory.Outstanding.newItem before.work ticket] at member
    rcases List.mem_append.mp member with old | current
    · exact flow.2.2.1 item old
    · have equal := List.mem_singleton.mp current
      subst item
      rfl
  have afterSafe : after.Safe := State.safe_of_flow after entry binding safe.1
    (Theory.Outstanding.enqueue_valid before.work ticket safe.2.1)
    (State.unfenced_transfer before after safe.2.2.1 uses rfl) flow.1 flow.2.1 pending
    (fun used => flow.2.2.2 (uses .standby used))
  let raw : RawResult := ⟨tick after, some (Work.newItem before.work ticket), none, none⟩
  refine ⟨raw, ?_, tick_safe after afterSafe⟩
  dsimp only [gateway] at unfenced checked
  simp only [core, binding, selected, dite_true, unfenced, Bool.false_eq_true, ite_false,
    checked, Bool.not_true]
  simp only [raw, tick, after, ticket, gateway, binding]
  rfl

theorem serve_bound_core_completes (before : State) (entry : NetfilterNAT.Entry) (id : Nat)
    (safe : before.Safe) (binding : before.binding = some entry)
    (pending : ∃ item ∈ before.work.pending, item.id = id) :
    ∃ raw, core before (.serve id) = .ok raw ∧ raw.state.Safe := by
  obtain ⟨requested, member, selected⟩ := pending
  subst id
  obtain ⟨completed, completedEq⟩ := Theory.Outstanding.complete_completes before.work requested member
  let ticket := completed.item.value
  have belongs := completed.member
  have flow := safe.flow binding
  have sameEntry : ticket.entry = entry := flow.2.2.1 completed.item belongs
  have used : before.uses ticket.gateway = true := before.uses_pending completed.item belongs
  have unfenced := safe.unfenced ticket.gateway used
  have available := safe.ready binding ticket.gateway used
  have ticketReady : TrackedFlow.Ready (before.gateways.table ticket.gateway) ticket.entry := by
    rw [sameEntry]
    exact available
  have udp : ticket.entry.flow.original.protocol = Protocol.udp := by rw [sameEntry]; exact flow.1.2.1
  obtain ⟨outcome, computed, _, _, preserved, valid⟩ := TrackedFlow.step_completes
    (before.configurations ticket.gateway).pipeline (before.gateways.table ticket.gateway)
    ticket.entry ticket.direction ticket.source.packet (safe.table_valid ticket.gateway) ticketReady udp
    ticket.selected ticket.source.bytes ticket.source.encoded
  have preservedEntry : TrackedFlow.Ready outcome.state entry := by rw [← sameEntry]; exact preserved
  let after : State := { before with
    gateways := before.gateways.write ticket.gateway outcome.state
    work := completed.state }
  have subset : ∀ item ∈ after.work.pending, item ∈ before.work.pending := by
    intro item member
    exact completed.pendingPerm.mem_iff.mpr (List.mem_cons_of_mem _ member)
  have owners : after.gateways.owners = before.gateways.owners := by cases gatewayEq : ticket.gateway <;> simp [after, gatewayEq, StatefulFailover.State.write]
  have fenced : after.gateways.fenced = before.gateways.fenced := by cases gatewayEq : ticket.gateway <;> simp [after, gatewayEq, StatefulFailover.State.write]
  have uses : ∀ gateway, after.uses gateway = true → before.uses gateway = true :=
    State.uses_mono before after owners (fun item member => before.uses_pending item (subset item member))
  have primary : TrackedFlow.Ready after.gateways.primary entry := by
    cases gatewayEq : ticket.gateway
    · simpa only [after, gatewayEq, StatefulFailover.State.write] using preservedEntry
    · simpa only [after, gatewayEq, StatefulFailover.State.write] using flow.2.1
  have standby : after.uses .standby = true → TrackedFlow.Ready after.gateways.standby entry := by
    intro used
    cases gatewayEq : ticket.gateway
    · simpa only [after, gatewayEq, StatefulFailover.State.write] using flow.2.2.2 (uses .standby used)
    · simpa only [after, gatewayEq, StatefulFailover.State.write] using preservedEntry
  have afterSafe : after.Safe := State.safe_of_flow after entry binding
    (before.gateways.write_valid ticket.gateway outcome.state safe.1 valid) (completed.valid safe.2.1)
    (State.unfenced_transfer before after safe.2.2.1 uses fenced) flow.1 primary
    (fun item member => flow.2.2.1 item (subset item member)) standby
  let raw : RawResult := ⟨tick after, none, some ⟨completed.item, before.configurations ticket.gateway, outcome⟩, none⟩
  refine ⟨raw, ?_, tick_safe after afterSafe⟩
  have checked := (TrackedFlow.ready_correct _ _).mpr available
  have different : ¬ ticket.entry ≠ entry := by rw [sameEntry]; simp
  dsimp only [ticket] at unfenced checked computed different
  simp only [core, completedEq, Except.mapError, bind, Except.bind, binding, different, ite_false,
    unfenced, Bool.false_eq_true, checked, Bool.not_true]
  rw [computed]
  simp only [pure, Except.pure]
  simp only [raw, tick, after, ticket, binding]
  rfl


theorem serve_core_completes (before : State) (id : Nat) (safe : before.Safe)
    (pending : ∃ item ∈ before.work.pending, item.id = id) :
    ∃ raw, core before (.serve id) = .ok raw ∧ raw.state.Safe := by
  cases binding : before.binding with
  | none =>
    have empty : before.work.pending = [] := by simpa only [binding] using safe.2.2.2
    obtain ⟨item, member, _⟩ := pending
    simp [empty] at member
  | some entry => exact serve_bound_core_completes before entry id safe binding pending

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

theorem core_assign_facts (before : State) (direction : FlowNAT.Direction) (source : Source) (raw : RawResult)
    (accepted : core before (.assign direction source) = .ok raw) :
    ∃ item, raw.admitted = some item ∧ before.binding = some item.value.entry ∧
      item.id = before.work.nextID ∧ item.value.gateway = before.gateways.owners.get (leg direction) ∧
      item.value.direction = direction ∧ item.value.source = source ∧ item.value.routeEpoch = before.gateways.epoch ∧
      raw.state.work.nextID = before.work.nextID + 1 ∧ raw.state.work.pending = before.work.pending ++ [item] ∧
      raw.state.work.completed = before.work.completed ∧ raw.state.binding = before.binding ∧
      raw.state.gateways.owners = before.gateways.owners := by
  unfold core at accepted
  cases binding : before.binding with
  | none => simp [binding, throw] at accepted
  | some entry =>
    simp only [binding] at accepted
    split at accepted
    · split at accepted
      · simp [throw, bind, Except.bind] at accepted
      · split at accepted
        · simp [throw, bind, Except.bind] at accepted
        · simp only [pure, Except.pure] at accepted
          cases accepted
          exact ⟨_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · simp [throw] at accepted

theorem core_serve_facts (before : State) (id : Nat) (raw : RawResult)
    (accepted : core before (.serve id) = .ok raw) :
    ∃ (completed : Theory.Outstanding.Completed before.work id)
      (outcome : WireForwarding.Outcome completed.item.value.source.packet),
      Work.complete before.work id = .ok completed ∧
      raw.served = some ⟨completed.item, before.configurations completed.item.value.gateway, outcome⟩ ∧
      before.binding = some completed.item.value.entry ∧
      before.gateways.isFenced completed.item.value.gateway = false ∧
      TrackedFlow.Ready (before.gateways.table completed.item.value.gateway) completed.item.value.entry ∧
      WireForwarding.step (before.configurations completed.item.value.gateway).pipeline
        (before.gateways.table completed.item.value.gateway)
        (TrackedFlow.wireInput completed.item.value.entry completed.item.value.direction completed.item.value.source.packet) = .ok outcome ∧
      raw.state.work = completed.state ∧
      raw.state.gateways.table completed.item.value.gateway = outcome.state ∧
      raw.state.configurations = before.configurations ∧ raw.state.binding = before.binding ∧
      raw.state.gateways.owners = before.gateways.owners := by
  unfold core at accepted
  cases completedEq : Work.complete before.work id with
  | error error => simp [completedEq, Except.mapError, bind, Except.bind] at accepted
  | ok completed =>
    simp only [completedEq, Except.mapError, bind, Except.bind] at accepted
    cases binding : before.binding with
    | none => simp [binding, throw] at accepted
    | some entry =>
      simp only [binding] at accepted
      split at accepted
      · simp [throw] at accepted
      · rename_i same
        split at accepted
        · simp [throw] at accepted
        · rename_i unfenced
          split at accepted
          · simp [throw] at accepted
          · rename_i ready
            cases computed : WireForwarding.step (before.configurations completed.item.value.gateway).pipeline
                (before.gateways.table completed.item.value.gateway)
                (TrackedFlow.wireInput completed.item.value.entry completed.item.value.direction completed.item.value.source.packet) with
            | error error => simp [computed] at accepted
            | ok outcome =>
              simp only [computed, pure, Except.pure] at accepted
              cases accepted
              have equal : completed.item.value.entry = entry := by
                by_cases matched : completed.item.value.entry = entry
                · exact matched
                · exact False.elim (same matched)
              refine ⟨completed, outcome, rfl, rfl, ?_, by simpa using unfenced, ?_, computed,
                rfl, ?_, rfl, rfl, ?_⟩
              · exact congrArg some equal.symm
              · rw [equal]
                exact (TrackedFlow.ready_correct _ _).mp (by simpa using ready)
              · exact StatefulFailover.State.table_write _ _ _
              · cases completed.item.value.gateway <;> rfl


inductive Admissible (before : State) : Event → Prop
  | stage (zone : Nat) (key : Header) (entry : NetfilterNAT.Entry) (direction : FlowNAT.Direction)
      (supported : FlowSupported entry) (primary : TrackedFlow.Ready before.gateways.primary entry)
      (binding : before.binding = none ∨ before.binding = some entry)
      (standby : before.uses .standby = true → TrackedFlow.Ready before.gateways.standby entry)
      (attached : entry.flow.key direction = (zone, key)) : Admissible before (.stage zone key)
  | commit (timeout : Nat) (selection : ConntrackReplication.Selection) (entry : NetfilterNAT.Entry)
      (binding : before.binding = some entry) (cached : before.gateways.cache = some selection)
      (same : selection.record.entry = entry) (bounded : 0 < timeout ∧ timeout < 4294967296)
      (fresh : ∀ direction, entry.flow.key direction ∉ before.gateways.standby.model.keys) :
      Admissible before (.commit timeout)
  | handoff (selectedLeg : Leg) (gateway : Gateway) (entry : NetfilterNAT.Entry)
      (binding : before.binding = some entry) (ready : TrackedFlow.Ready (before.gateways.table gateway) entry)
      (unfenced : before.gateways.isFenced gateway = false) : Admissible before (.handoff selectedLeg gateway)
  | fence (gateway : Gateway) (client : before.gateways.owners.client ≠ gateway)
      (server : before.gateways.owners.server ≠ gateway) (drained : before.outstanding gateway = 0) :
      Admissible before (.fence gateway)
  | forget : Admissible before .forget
  | install (gateway : Gateway) (configuration : Configuration) : Admissible before (.install gateway configuration)
  | assign (direction : FlowNAT.Direction) (source : Source) (entry : NetfilterNAT.Entry)
      (binding : before.binding = some entry) (selected : source.packet.header = entry.flow.input direction) :
      Admissible before (.assign direction source)
  | serve (id : Nat) (pending : ∃ item ∈ before.work.pending, item.id = id) : Admissible before (.serve id)

theorem admissible_core_progress (before : State) (event : Event) (safe : before.Safe)
    (admissible : Admissible before event) : ∃ raw, core before event = .ok raw ∧ raw.state.Safe := by
  cases admissible with
  | stage zone key entry direction supported primary binding standby attached =>
    exact stage_core_completes before zone key entry direction safe supported primary binding standby attached
  | commit timeout selection entry binding cached same bounded fresh =>
    exact commit_core_completes before timeout selection safe binding cached same bounded fresh
  | handoff selectedLeg gateway entry binding ready unfenced =>
    exact handoff_core_completes before selectedLeg gateway safe binding ready unfenced
  | fence gateway client server drained => exact fence_core_completes before gateway safe client server drained
  | forget => exact forget_core_completes before safe
  | install gateway configuration => exact install_core_completes before gateway configuration safe
  | assign direction source entry binding selected => exact assign_core_completes before entry direction source safe binding selected
  | serve id pending => exact serve_core_completes before id safe pending

theorem admissible_progress (before : State) (event : Event) (safe : before.Safe)
    (admissible : Admissible before event) : ∃ result, step before event = .ok result ∧ result.state.Safe := by
  obtain ⟨raw, computed, after⟩ := admissible_core_progress before event safe admissible
  obtain ⟨result, accepted, same⟩ := step_of_core before event raw safe computed after
  exact ⟨result, accepted, by simpa only [← same] using after⟩

def contract : Transition State Event where
  step before event after := Admissible before event ∧ ∃ result, step before event = .ok result ∧ result.state = after

theorem contract_invariant : contract.Invariant State.Safe := by
  intro before event after safe edge
  obtain ⟨admissible, result, accepted, rfl⟩ := edge
  obtain ⟨actual, computed, preserved⟩ := admissible_progress before event safe admissible
  have equal := Except.ok.inj (computed.symm.trans accepted)
  subst actual
  exact preserved

theorem arbitrary_interleavings (trace : contract.Trace initial events final) (safe : initial.Safe) :
    final.Safe ∧ ∀ event, Admissible final event → ∃ result, step final event = .ok result ∧ result.state.Safe := by
  have preserved := contract_invariant.trace safe trace
  exact ⟨preserved, fun event allowed => admissible_progress final event preserved allowed⟩

theorem arbitrary_prefixes (trace : contract.Trace initial (prior ++ later) final) (safe : initial.Safe) :
    ∃ middle, contract.Trace initial prior middle ∧ contract.Trace middle later final ∧ middle.Safe ∧
      ∀ event, Admissible middle event → ∃ result, step middle event = .ok result ∧ result.state.Safe := by
  obtain ⟨middle, first, rest⟩ := trace.split
  have preserved := arbitrary_interleavings first safe
  exact ⟨middle, first, rest, preserved⟩


theorem core_serve_forwarded (before : State) (id : Nat) (raw : RawResult) (safe : before.Safe)
    (accepted : core before (.serve id) = .ok raw) (served : PacketResult) (seen : raw.served = some served)
    (emission : WireForwarding.Emission served.ticket.value.source.packet)
    (emitted : served.outcome.output = some emission) :
    served.ticket ∈ before.work.pending ∧ served.ticket.id = id ∧
      served.configuration = before.configurations served.ticket.value.gateway ∧
      emission.target = served.ticket.value.entry.flow.output served.ticket.value.direction ∧
      emission.decoded.datagram.payload = served.ticket.value.source.packet.datagram.payload ∧
      emission.decoded.ip.packet.ttl.toNat = served.ticket.value.source.packet.ip.packet.ttl.toNat - 1 ∧
      StatefulACL.Policy.evaluate served.configuration.pipeline.forwardDefault served.configuration.pipeline.forward
        (TrackedFlow.classification (before.gateways.table served.ticket.value.gateway)
          served.ticket.value.entry served.ticket.value.direction)
        (TrackedFlow.destination served.ticket.value.entry served.ticket.value.direction) = .permit ∧
      StatefulACL.Policy.evaluate served.configuration.pipeline.lateDefault served.configuration.pipeline.late
        (TrackedFlow.classification (before.gateways.table served.ticket.value.gateway)
          served.ticket.value.entry served.ticket.value.direction) emission.target = .permit := by
  obtain ⟨completed, outcome, _, reported, binding, _, ready, computed, _⟩ := core_serve_facts before id raw accepted
  have equal := Option.some.inj (reported.symm.trans seen)
  cases equal
  have flow := safe.flow binding
  have udp := flow.1.2.1
  have facts := TrackedFlow.forwarded (before.configurations completed.item.value.gateway).pipeline
    (before.gateways.table completed.item.value.gateway) completed.item.value.entry completed.item.value.direction
    completed.item.value.source.packet (safe.table_valid _) ready udp completed.item.value.selected outcome computed emission emitted
  exact ⟨completed.member, completed.selected, rfl, facts.1, facts.2.2.1, facts.2.2.2.1,
    facts.2.2.2.2.1, by simpa only [facts.1] using facts.2.2.2.2.2⟩

theorem serve_service (before : State) (item : Work.Item Ticket) (safe : before.Safe)
    (member : item ∈ before.work.pending) (live : 1 < item.value.source.packet.ip.packet.ttl.toNat)
    (routed : (Routing.nextHop (before.configurations item.value.gateway).pipeline.routes
      (TrackedFlow.destination item.value.entry item.value.direction).destination).isSome = true)
    (forward : StatefulACL.Policy.evaluate (before.configurations item.value.gateway).pipeline.forwardDefault
      (before.configurations item.value.gateway).pipeline.forward
      (TrackedFlow.classification (before.gateways.table item.value.gateway) item.value.entry item.value.direction)
      (TrackedFlow.destination item.value.entry item.value.direction) = .permit)
    (late : StatefulACL.Policy.evaluate (before.configurations item.value.gateway).pipeline.lateDefault
      (before.configurations item.value.gateway).pipeline.late
      (TrackedFlow.classification (before.gateways.table item.value.gateway) item.value.entry item.value.direction)
      (item.value.entry.flow.output item.value.direction) = .permit) :
    ∃ (result : Result) (served : PacketResult) (emission : WireForwarding.Emission served.ticket.value.source.packet),
      step before (.serve item.id) = .ok result ∧ result.served = some served ∧ served.ticket = item ∧
      served.configuration = before.configurations item.value.gateway ∧ served.outcome.output = some emission ∧
      emission.target = item.value.entry.flow.output item.value.direction ∧
      emission.decoded.datagram.payload = item.value.source.packet.datagram.payload ∧
      emission.decoded.ip.packet.ttl.toNat = item.value.source.packet.ip.packet.ttl.toNat - 1 := by
  obtain ⟨raw, computed, after⟩ := serve_core_completes before item.id safe ⟨item, member, rfl⟩
  obtain ⟨result, accepted, same⟩ := step_of_core before (.serve item.id) raw safe computed after
  obtain ⟨completed, outcome, completedEq, reported, binding, _, ready, servedEq, _⟩ := core_serve_facts before item.id raw computed
  have selected := completed.item_eq safe.2.1 item member rfl
  have flow := safe.flow binding
  obtain ⟨actual, emission, completedWire, output, target, payload, ttl, _⟩ := TrackedFlow.service
    (before.configurations completed.item.value.gateway).pipeline (before.gateways.table completed.item.value.gateway)
    completed.item.value.entry completed.item.value.direction completed.item.value.source.packet
    (safe.table_valid _) ready flow.1.2.1 completed.item.value.selected completed.item.value.source.bytes
    completed.item.value.source.encoded
    (by simpa only [selected] using live) (by simpa only [selected] using routed)
    (by simpa only [selected] using forward) (by simpa only [selected] using late)
  have equal := Except.ok.inj (completedWire.symm.trans servedEq)
  subst actual
  refine ⟨result, ⟨completed.item, before.configurations completed.item.value.gateway, outcome⟩,
    emission, accepted, ?_, selected,
    congrArg (fun ticket : Work.Item Ticket => before.configurations ticket.value.gateway) selected,
    output, target.trans (congrArg (fun ticket : Work.Item Ticket => ticket.value.entry.flow.output ticket.value.direction) selected),
    payload.trans (congrArg (fun ticket : Work.Item Ticket => ticket.value.source.packet.datagram.payload) selected),
    ttl.trans (congrArg (fun ticket : Work.Item Ticket => ticket.value.source.packet.ip.packet.ttl.toNat - 1) selected)⟩
  have field := congrArg RawResult.served same
  exact field.trans reported


theorem core_assign_outstanding (before : State) (direction : FlowNAT.Direction) (source : Source)
    (raw : RawResult) (accepted : core before (.assign direction source) = .ok raw) (gateway : Gateway) :
    ∃ item, raw.admitted = some item ∧ item.value.gateway = before.gateways.owners.get (leg direction) ∧
      raw.state.outstanding gateway = before.outstanding gateway + if item.value.gateway = gateway then 1 else 0 := by
  obtain ⟨item, reported, _, _, assigned, _, _, _, _, pending, _⟩ := core_assign_facts before direction source raw accepted
  refine ⟨item, reported, assigned, ?_⟩
  simp only [State.outstanding_eq_count, Theory.Outstanding.count, pending, List.countP_append,
    List.countP_cons, List.countP_nil, Nat.zero_add, decide_eq_true_eq]

theorem core_assign_not_target (before : State) (direction : FlowNAT.Direction) (source : Source)
    (raw : RawResult) (accepted : core before (.assign direction source) = .ok raw) (gateway : Gateway)
    (assigned : before.gateways.owners.get (leg direction) ≠ gateway) :
    raw.state.outstanding gateway = before.outstanding gateway := by
  obtain ⟨item, _, selected, counted⟩ := core_assign_outstanding before direction source raw accepted gateway
  simpa only [selected, assigned, ite_false, Nat.add_zero] using counted

theorem serve_count (before : State) (item : Work.Item Ticket) (safe : before.Safe)
    (member : item ∈ before.work.pending) (gateway : Gateway) :
    ∃ result, step before (.serve item.id) = .ok result ∧ result.state.Safe ∧
      before.outstanding gateway = result.state.outstanding gateway + (if item.value.gateway = gateway then 1 else 0) ∧
      result.state.gateways.owners = before.gateways.owners := by
  obtain ⟨raw, computed, after⟩ := serve_core_completes before item.id safe ⟨item, member, rfl⟩
  obtain ⟨result, accepted, same⟩ := step_of_core before (.serve item.id) raw safe computed after
  obtain ⟨completed, outcome, completedEq, _, _, _, _, _, work, _, _, _, owners⟩ := core_serve_facts before item.id raw computed
  have selected := completed.item_eq safe.2.1 item member rfl
  have counted : before.outstanding gateway = raw.state.outstanding gateway + if item.value.gateway = gateway then 1 else 0 := by
    rw [State.outstanding_eq_count, State.outstanding_eq_count, work]
    simpa only [selected, decide_eq_true_eq] using completed.count (fun ticket => decide (ticket.gateway = gateway))
  refine ⟨result, accepted, ?_, ?_, ?_⟩
  · simpa only [← same] using after
  · simpa only [← same] using counted
  · simpa only [← same] using owners

theorem drain_gateway (before : State) (gateway : Gateway) (safe : before.Safe) :
    ∃ (ids : List Nat) (final : State), contract.Trace before (ids.map Event.serve) final ∧ final.Safe ∧
      final.outstanding gateway = 0 ∧ ids.length = before.outstanding gateway ∧
      final.gateways.owners = before.gateways.owners := by
  by_cases empty : before.outstanding gateway = 0
  · exact ⟨[], before, .nil before, safe, empty, empty.symm, rfl⟩
  · have positive : 0 < Theory.Outstanding.count before.work (fun ticket => decide (ticket.gateway = gateway)) := by
      rw [← State.outstanding_eq_count]
      omega
    obtain ⟨item, member, matching⟩ := List.countP_pos_iff.mp positive
    have selected : item.value.gateway = gateway := of_decide_eq_true matching
    obtain ⟨result, accepted, preserved, counted, owners⟩ := serve_count before item safe member gateway
    simp only [selected, ite_true] at counted
    have smaller : result.state.outstanding gateway < before.outstanding gateway := by omega
    obtain ⟨ids, final, rest, finalSafe, drained, length, finalOwners⟩ := drain_gateway result.state gateway preserved
    refine ⟨item.id :: ids, final, .cons ?_ rest, finalSafe, drained, ?_, finalOwners.trans owners⟩
    · exact ⟨.serve item.id ⟨item, member, rfl⟩, result, accepted, rfl⟩
    · simp only [List.length_cons]
      omega
termination_by before.outstanding gateway

theorem drain_then_fence (before : State) (gateway : Gateway) (safe : before.Safe)
    (client : before.gateways.owners.client ≠ gateway) (server : before.gateways.owners.server ≠ gateway) :
    ∃ (ids : List Nat) (middle final : State), contract.Trace before (ids.map Event.serve) middle ∧
      middle.outstanding gateway = 0 ∧ contract.Trace middle [.fence gateway] final ∧ final.Safe := by
  obtain ⟨ids, middle, trace, preserved, drained, _, owners⟩ := drain_gateway before gateway safe
  have ready : Admissible middle (.fence gateway) := .fence gateway
    (by simpa only [owners] using client) (by simpa only [owners] using server) drained
  obtain ⟨result, accepted, finalSafe⟩ := admissible_progress middle (.fence gateway) preserved ready
  exact ⟨ids, middle, result.state, trace, drained, .cons ⟨ready, result, accepted, rfl⟩ (.nil _), finalSafe⟩

end Netlib.Protocol.SafeHandoff
