import Netlib.Protocol.WireForwarding
/-!
# A protected ordinary flow

Readiness requires a matching NAT entry in the current valid table.
Reply observations may differ across gateways without changing that binding.
Every valid selected packet completes. Current routes, TTL, and policy determine whether it emits bytes.
Timeout evolution and transport validation remain outside this module.
-/

namespace Netlib.Protocol.TrackedFlow
open Packet
open ConntrackLifecycle (State Record)
private theorem record_key_injective {records : List Record}
    (unique : (records.flatMap fun record =>
      [record.entry.flow.key .original, record.entry.flow.key .reply]).Nodup)
    {left right : Record} (leftMember : left ∈ records) (rightMember : right ∈ records)
    (same : left.entry.flow.key .original = right.entry.flow.key .original) : left = right := by
  induction records with
  | nil => simp at leftMember
  | cons head tail ih =>
    simp only [List.flatMap_cons, List.cons_append, List.nil_append] at unique
    have absent := (List.nodup_cons.mp unique).1
    have tailUnique := (List.nodup_cons.mp (List.nodup_cons.mp unique).2).2
    rcases List.mem_cons.mp leftMember with rfl | leftTail
    · rcases List.mem_cons.mp rightMember with rfl | rightTail
      · rfl
      · exact False.elim (absent (List.mem_cons_of_mem _
          (List.mem_flatMap.mpr ⟨right, rightTail, by rw [same]; simp⟩)))
    · rcases List.mem_cons.mp rightMember with rfl | rightTail
      · exact False.elim (absent (List.mem_cons_of_mem _
          (List.mem_flatMap.mpr ⟨left, leftTail, by rw [← same]; simp⟩)))
      · exact ih tailUnique leftTail rightTail

theorem find_record (state : State) (valid : state.Valid) (record : Record) (member : record ∈ state.records) :
    state.records.find? (fun item => decide (item.entry.flow = record.entry.flow)) = some record := by
  have unique : (state.records.flatMap fun record =>
      [record.entry.flow.key .original, record.entry.flow.key .reply]).Nodup := by
    simpa [State.model, FlowNAT.Snapshot.keys, FlowNAT.Snapshot.slots, List.map_flatMap,
      List.flatMap_map, List.map_map, Function.comp_def, FlowNAT.Hit.key] using valid.1.2
  cases found : state.records.find? (fun item => decide (item.entry.flow = record.entry.flow)) with
  | none =>
    have absent := List.find?_eq_none.mp found
    exact False.elim (absent record member (by simp))
  | some actual =>
    have belongs := List.mem_of_find?_eq_some found
    have same : actual.entry.flow = record.entry.flow := of_decide_eq_true (List.find?_some
      (p := fun item : Record => decide (item.entry.flow = record.entry.flow)) (a := actual) found)
    have equal := record_key_injective unique belongs member (congrArg (fun flow => flow.key .original) same)
    subst actual
    rfl


def Ready (state : State) (entry : NetfilterNAT.Entry) : Prop :=
  ∃ record ∈ state.records, record.entry = entry

def ready (state : State) (entry : NetfilterNAT.Entry) : Bool :=
  state.records.any (fun record => decide (record.entry = entry))

theorem ready_correct (state : State) (entry : NetfilterNAT.Entry) : ready state entry = true ↔ Ready state entry := by
  simp [ready, Ready, List.any_eq_true]

def classification (state : State) (entry : NetfilterNAT.Entry) (direction : FlowNAT.Direction) : StatefulACL.CTState :=
  match state.records.find? (fun record => decide (record.entry.flow = entry.flow)) with
  | none => .new
  | some record => ConntrackLifecycle.classify record direction

def lifecycleInput (entry : NetfilterNAT.Entry) (direction : FlowNAT.Direction) : ConntrackLifecycle.Input :=
  ⟨entry.flow.zone direction, entry.flow.input direction, none⟩

def wireInput (entry : NetfilterNAT.Entry) (direction : FlowNAT.Direction) (packet : UDP.DecodedIPv4) : WireForwarding.Input :=
  ⟨entry.flow.zone direction, packet, none⟩

def afterReply (state : State) (entry : NetfilterNAT.Entry) : FlowNAT.Direction → State
  | .original => state
  | .reply => state.markReply entry.flow

theorem Ready.compatible (available : Ready state entry) (valid : state.Valid) : entry.Compatible := by
  obtain ⟨record, member, same⟩ := available
  rw [← same]
  exact valid.2 record member

theorem Ready.lookup (available : Ready state entry) (valid : state.Valid) (direction : FlowNAT.Direction) :
    state.model.lookup (entry.flow.zone direction) (entry.flow.input direction) = some ⟨entry.flow, direction⟩ := by
  obtain ⟨record, member, same⟩ := available
  have found := FlowNAT.Snapshot.lookup_complete _ valid.1 ⟨entry.flow, direction⟩
    (List.mem_map.mpr ⟨record, member, congrArg (·.flow) same⟩)
  simpa only [FlowNAT.Hit.key, FlowNAT.Entry.key] using found

theorem Ready.afterReply (available : Ready state entry) (direction : FlowNAT.Direction) :
    Ready (afterReply state entry direction) entry := by
  cases direction
  · exact available
  · obtain ⟨record, member, same⟩ := available
    exact ⟨State.markRecord entry.flow record, List.mem_map.mpr ⟨record, member, rfl⟩,
      (State.markRecord_entry _ _).trans same⟩

theorem classification_record (state : State) (valid : state.Valid) (record : Record)
    (member : record ∈ state.records) (same : record.entry = entry) (direction : FlowNAT.Direction) :
    classification state entry direction = ConntrackLifecycle.classify record direction := by
  have found := find_record state valid record member
  rw [same] at found
  simp [classification, found]

theorem wireInput_lifecycle (entry : NetfilterNAT.Entry) (direction : FlowNAT.Direction)
    (packet : UDP.DecodedIPv4) (selected : packet.header = entry.flow.input direction) :
    (wireInput entry direction packet).lifecycle = lifecycleInput entry direction := by
  simp [wireInput, WireForwarding.Input.lifecycle, lifecycleInput, selected]

theorem prepare (state : State) (entry : NetfilterNAT.Entry) (direction : FlowNAT.Direction)
    (valid : state.Valid) (available : Ready state entry) (udp : entry.flow.original.protocol = Protocol.udp) :
    ∃ prepared : ConntrackLifecycle.Prepared (lifecycleInput entry direction),
      ConntrackLifecycle.prepare state (lifecycleInput entry direction) = .ok prepared ∧
      prepared.attachment = ⟨entry, direction, classification state entry direction, false⟩ ∧
      prepared.state = afterReply state entry direction := by
  obtain ⟨record, member, same⟩ := available
  have compatible := valid.2 record member
  have entryCompatible : entry.Compatible := by rw [← same]; exact compatible
  have checked := (State.check_correct _).mpr valid
  have found : state.model.lookup (lifecycleInput entry direction).zone (lifecycleInput entry direction).packet =
      some ⟨entry.flow, direction⟩ := (show Ready state entry from ⟨record, member, same⟩).lookup valid direction
  have row := find_record state valid record member
  rw [same] at row
  have classified := classification_record state valid record member same direction
  have bounded : ¬ (lifecycleInput entry direction).zone ≥ 65536 := by
    apply Nat.not_le.mpr
    cases direction
    · exact entryCompatible.1.2.2.1
    · exact entryCompatible.1.2.2.2.1
  have transport : Conntrack.transport (lifecycleInput entry direction).packet = true := by
    have protocol : (lifecycleInput entry direction).packet.protocol = Protocol.udp := by
      cases direction
      · exact udp
      · exact entryCompatible.1.1.symm.trans udp
    simp [Conntrack.transport, protocol]
  have candidate : (lifecycleInput entry direction).candidate = none := rfl
  cases direction with
  | original =>
    let prepared : ConntrackLifecycle.Prepared (lifecycleInput entry .original) :=
      ⟨state, valid, ⟨record.entry, .original, ConntrackLifecycle.classify record .original, false⟩,
        compatible, by rw [same]; rfl⟩
    refine ⟨prepared, ?_, ?_, rfl⟩
    · simp only [ConntrackLifecycle.prepare, checked, dite_true, bounded, ite_false,
        transport, Bool.not_true, Bool.false_eq_true, candidate, Option.isSome_none]
      split
      · rename_i absent
        rw [found] at absent
        cases absent
      · rename_i hit equation
        have equal := Option.some.inj (equation.symm.trans found)
        subst hit
        split
        · rename_i absent
          rw [row] at absent
          cases absent
        · rename_i selected equation
          have equal := Option.some.inj (equation.symm.trans row)
          subst selected
          rfl
    · change (⟨record.entry, .original, ConntrackLifecycle.classify record .original, false⟩ : ConntrackLifecycle.Attachment) = _
      rw [same, classified]
  | reply =>
    let prepared : ConntrackLifecycle.Prepared (lifecycleInput entry .reply) :=
      ⟨state.markReply entry.flow, State.markReply_valid _ _ valid,
        ⟨record.entry, .reply, ConntrackLifecycle.classify record .reply, false⟩,
        compatible, by rw [same]; rfl⟩
    refine ⟨prepared, ?_, ?_, rfl⟩
    · simp only [ConntrackLifecycle.prepare, checked, dite_true, bounded, ite_false,
        transport, Bool.not_true, Bool.false_eq_true, candidate, Option.isSome_none]
      split
      · rename_i absent
        rw [found] at absent
        cases absent
      · rename_i hit equation
        have equal := Option.some.inj (equation.symm.trans found)
        subst hit
        split
        · rename_i absent
          rw [row] at absent
          cases absent
        · rename_i selected equation
          have equal := Option.some.inj (equation.symm.trans row)
          subst selected
          rfl
    · change (⟨record.entry, .reply, ConntrackLifecycle.classify record .reply, false⟩ : ConntrackLifecycle.Attachment) = _
      rw [same, classified]

theorem prepare_fields (state : State) (entry : NetfilterNAT.Entry) (direction : FlowNAT.Direction)
    (valid : state.Valid) (available : Ready state entry) (udp : entry.flow.original.protocol = Protocol.udp)
    (prepared : ConntrackLifecycle.Prepared (lifecycleInput entry direction))
    (accepted : ConntrackLifecycle.prepare state (lifecycleInput entry direction) = .ok prepared) :
    prepared.attachment = ⟨entry, direction, classification state entry direction, false⟩ ∧
      prepared.state = afterReply state entry direction := by
  obtain ⟨actual, computed, fields⟩ := prepare state entry direction valid available udp
  have equal := Except.ok.inj (computed.symm.trans accepted)
  subst actual
  exact fields

theorem prepare_wire (state : State) (entry : NetfilterNAT.Entry) (direction : FlowNAT.Direction)
    (packet : UDP.DecodedIPv4) (valid : state.Valid) (available : Ready state entry)
    (udp : entry.flow.original.protocol = Protocol.udp) (selected : packet.header = entry.flow.input direction) :
    ∃ prepared : ConntrackLifecycle.Prepared (wireInput entry direction packet).lifecycle,
      ConntrackLifecycle.prepare state (wireInput entry direction packet).lifecycle = .ok prepared ∧
      prepared.attachment = ⟨entry, direction, classification state entry direction, false⟩ ∧
      prepared.state = afterReply state entry direction := by
  have actual := prepare state entry direction valid available udp
  rw [← wireInput_lifecycle entry direction packet selected] at actual
  exact actual

private theorem ordinary_completes (pipeline : ConntrackLifecycle.Pipeline)
    (prepared : ConntrackLifecycle.Prepared input) (existing : prepared.attachment.fresh = false) :
    ∃ outcome, ConntrackLifecycle.process pipeline prepared = .ok outcome := by
  cases routed : Routing.nextHop pipeline.routes ((ConntrackLifecycle.destinationStage prepared.attachment.entry prepared.attachment.direction).apply input.packet).destination with
  | none => exact ⟨_, by simp only [ConntrackLifecycle.process, routed]; rfl⟩
  | some hop =>
    by_cases denied : StatefulACL.Policy.evaluate pipeline.forwardDefault pipeline.forward
        prepared.attachment.classification ((ConntrackLifecycle.destinationStage prepared.attachment.entry prepared.attachment.direction).apply input.packet) = .deny
    · exact ⟨_, by simp only [ConntrackLifecycle.process, routed, denied, ite_true]; rfl⟩
    · by_cases late : StatefulACL.Policy.evaluate pipeline.lateDefault pipeline.late
          prepared.attachment.classification ((ConntrackLifecycle.sourceStage prepared.attachment.entry prepared.attachment.direction).apply ((ConntrackLifecycle.destinationStage prepared.attachment.entry prepared.attachment.direction).apply input.packet)) = .deny
      · exact ⟨_, by simp only [ConntrackLifecycle.process, routed, denied, ite_false, late, ite_true]; rfl⟩
      · exact ⟨_, by simp only [ConntrackLifecycle.process, routed, denied, ite_false, late, existing, Bool.false_eq_true]; rfl⟩

private theorem finish_attachment (pipeline : ConntrackLifecycle.Pipeline) (input : WireForwarding.Input)
    (valid : UDPRewrite.SourceValid input.packet) (prepared : ConntrackLifecycle.Prepared input.lifecycle)
    (outcome : WireForwarding.Outcome input.packet)
    (accepted : WireForwarding.finish pipeline input valid prepared = .ok outcome) :
    outcome.attachment = prepared.attachment := by
  obtain ⟨model, processed, same⟩ := WireForwarding.finish_realizes _ _ _ _ _ accepted
  rw [same]
  exact ConntrackLifecycle.process_attachment _ _ _ processed

private theorem process_attachment (pipeline : ConntrackLifecycle.Pipeline) (input : WireForwarding.Input)
    (valid : UDPRewrite.SourceValid input.packet) (prepared : ConntrackLifecycle.Prepared input.lifecycle)
    (outcome : WireForwarding.Outcome input.packet)
    (accepted : WireForwarding.process pipeline input valid prepared = .ok outcome) :
    outcome.attachment = prepared.attachment := by
  unfold WireForwarding.process at accepted
  split at accepted
  · exact finish_attachment _ _ _ _ _ accepted
  · split at accepted
    · cases accepted
      rfl
    · exact finish_attachment _ _ _ _ _ accepted

theorem step_facts (pipeline : ConntrackLifecycle.Pipeline) (state : State) (entry : NetfilterNAT.Entry)
    (direction : FlowNAT.Direction) (packet : UDP.DecodedIPv4) (valid : state.Valid) (available : Ready state entry)
    (udp : entry.flow.original.protocol = Protocol.udp) (selected : packet.header = entry.flow.input direction)
    (outcome : WireForwarding.Outcome packet)
    (accepted : WireForwarding.step pipeline state (wireInput entry direction packet) = .ok outcome) :
    outcome.attachment = ⟨entry, direction, classification state entry direction, false⟩ ∧
      outcome.state = afterReply state entry direction ∧ Ready outcome.state entry ∧ outcome.state.Valid := by
  obtain ⟨sourceValid, prepared, attached, processed⟩ := WireForwarding.step_prepared _ _ _ _ accepted
  obtain ⟨actual, computed, attachment, after⟩ := prepare_wire state entry direction packet valid available udp selected
  have equal := Except.ok.inj (computed.symm.trans attached)
  subst actual
  have observed := process_attachment _ _ _ _ _ processed
  have binding := observed.trans attachment
  have existing : outcome.attachment.fresh = false := by rw [binding]
  have state := (WireForwarding.process_existing_state _ _ _ _ _ processed existing).trans after
  exact ⟨binding, state, by rw [state]; exact available.afterReply direction, outcome.valid⟩

theorem step_completes (pipeline : ConntrackLifecycle.Pipeline) (state : State) (entry : NetfilterNAT.Entry)
    (direction : FlowNAT.Direction) (packet : UDP.DecodedIPv4) (valid : state.Valid) (available : Ready state entry)
    (udp : entry.flow.original.protocol = Protocol.udp) (selected : packet.header = entry.flow.input direction)
    (bytes : List UInt8) (encoded : UDP.encodeIPv4 packet = .ok bytes) :
    ∃ outcome, WireForwarding.step pipeline state (wireInput entry direction packet) = .ok outcome ∧
      outcome.attachment = ⟨entry, direction, classification state entry direction, false⟩ ∧
      outcome.state = afterReply state entry direction ∧ Ready outcome.state entry ∧ outcome.state.Valid := by
  obtain ⟨prepared, attached, attachment, _⟩ := prepare_wire state entry direction packet valid available udp selected
  have existing : prepared.attachment.fresh = false := by rw [attachment]
  obtain ⟨model, processed⟩ := ordinary_completes pipeline prepared existing
  obtain ⟨outcome, accepted⟩ := WireForwarding.step_completes pipeline state (wireInput entry direction packet)
    bytes encoded prepared attached model processed
  exact ⟨outcome, accepted, step_facts _ _ _ _ _ valid available udp selected _ accepted⟩

def destination (entry : NetfilterNAT.Entry) (direction : FlowNAT.Direction) : Header :=
  (ConntrackLifecycle.destinationStage entry direction).apply (entry.flow.input direction)

private theorem ordinary_service (pipeline : ConntrackLifecycle.Pipeline) (state : State)
    (entry : NetfilterNAT.Entry) (direction : FlowNAT.Direction) (packet : UDP.DecodedIPv4)
    (compatible : entry.Compatible) (selected : packet.header = entry.flow.input direction)
    (prepared : ConntrackLifecycle.Prepared (wireInput entry direction packet).lifecycle)
    (attachment : prepared.attachment = ⟨entry, direction, classification state entry direction, false⟩)
    (routed : (Routing.nextHop pipeline.routes (destination entry direction).destination).isSome = true)
    (forward : StatefulACL.Policy.evaluate pipeline.forwardDefault pipeline.forward
      (classification state entry direction) (destination entry direction) = .permit)
    (late : StatefulACL.Policy.evaluate pipeline.lateDefault pipeline.late
      (classification state entry direction) (entry.flow.output direction) = .permit)
    (model : ConntrackLifecycle.Outcome) (processed : ConntrackLifecycle.process pipeline prepared = .ok model) :
    model.output = some (entry.flow.output direction) := by
  have rewritten := ConntrackLifecycle.stages_correct entry compatible direction
  cases routeEq : Routing.nextHop pipeline.routes (destination entry direction).destination with
  | none => simp [routeEq] at routed
  | some hop =>
    simp only [destination] at routeEq forward
    simp [ConntrackLifecycle.process, attachment, wireInput, WireForwarding.Input.lifecycle,
      selected, routeEq, forward, rewritten, late, pure, Except.pure] at processed
    cases processed
    rfl

theorem forwarded (pipeline : ConntrackLifecycle.Pipeline) (state : State) (entry : NetfilterNAT.Entry)
    (direction : FlowNAT.Direction) (packet : UDP.DecodedIPv4) (valid : state.Valid) (available : Ready state entry)
    (udp : entry.flow.original.protocol = Protocol.udp) (selected : packet.header = entry.flow.input direction)
    (outcome : WireForwarding.Outcome packet)
    (accepted : WireForwarding.step pipeline state (wireInput entry direction packet) = .ok outcome)
    (emission : WireForwarding.Emission packet) (emitted : outcome.output = some emission) :
    emission.target = entry.flow.output direction ∧ outcome.afterDestination = destination entry direction ∧
      emission.decoded.datagram.payload = packet.datagram.payload ∧
      emission.decoded.ip.packet.ttl.toNat = packet.ip.packet.ttl.toNat - 1 ∧
      StatefulACL.Policy.evaluate pipeline.forwardDefault pipeline.forward
        (classification state entry direction) (destination entry direction) = .permit ∧
      StatefulACL.Policy.evaluate pipeline.lateDefault pipeline.late
        (classification state entry direction) (entry.flow.output direction) = .permit := by
  obtain ⟨sourceValid, prepared, model, processed, attached, same, output, _⟩ :=
    WireForwarding.step_output_prepared _ _ _ _ accepted emission emitted
  obtain ⟨actual, computed, attachment, _⟩ := prepare_wire state entry direction packet valid available udp selected
  have equal := Except.ok.inj (computed.symm.trans attached)
  subst actual
  have binding := ConntrackLifecycle.process_output _ _ _ _ processed output
  rw [attachment] at binding
  have afterDestination : outcome.afterDestination = destination entry direction := by
    rw [same]
    change model.afterDestination = destination entry direction
    rw [ConntrackLifecycle.process_destination _ _ _ processed, attachment]
    simp [destination, WireForwarding.Input.lifecycle, wireInput, selected]
  have facts := step_facts _ _ _ _ _ valid available udp selected _ accepted
  obtain ⟨_, _, allowed, allowedLate, _⟩ := WireForwarding.step_filters _ _ _ _ accepted emission emitted
  rw [facts.1, afterDestination] at allowed
  rw [facts.1, binding] at allowedLate
  exact ⟨binding, afterDestination, emission.payload, emission.ttl, allowed, allowedLate⟩

theorem service (pipeline : ConntrackLifecycle.Pipeline) (state : State) (entry : NetfilterNAT.Entry)
    (direction : FlowNAT.Direction) (packet : UDP.DecodedIPv4) (valid : state.Valid) (available : Ready state entry)
    (udp : entry.flow.original.protocol = Protocol.udp) (selected : packet.header = entry.flow.input direction)
    (bytes : List UInt8) (encoded : UDP.encodeIPv4 packet = .ok bytes) (live : 1 < packet.ip.packet.ttl.toNat)
    (routed : (Routing.nextHop pipeline.routes (destination entry direction).destination).isSome = true)
    (forward : StatefulACL.Policy.evaluate pipeline.forwardDefault pipeline.forward
      (classification state entry direction) (destination entry direction) = .permit)
    (late : StatefulACL.Policy.evaluate pipeline.lateDefault pipeline.late
      (classification state entry direction) (entry.flow.output direction) = .permit) :
    ∃ (outcome : WireForwarding.Outcome packet) (emission : WireForwarding.Emission packet),
      WireForwarding.step pipeline state (wireInput entry direction packet) = .ok outcome ∧
      outcome.output = some emission ∧ emission.target = entry.flow.output direction ∧
      emission.decoded.datagram.payload = packet.datagram.payload ∧
      emission.decoded.ip.packet.ttl.toNat = packet.ip.packet.ttl.toNat - 1 ∧
      Ready outcome.state entry ∧ outcome.state.Valid := by
  obtain ⟨outcome, accepted, fields⟩ := step_completes pipeline state entry direction packet valid available udp selected bytes encoded
  obtain ⟨sourceValid, prepared, attached, processed⟩ := WireForwarding.step_prepared _ _ _ _ accepted
  obtain ⟨actual, computed, attachment, _⟩ := prepare_wire state entry direction packet valid available udp selected
  have equal := Except.ok.inj (computed.symm.trans attached)
  subst actual
  rw [WireForwarding.process_long _ _ _ _ live] at processed
  obtain ⟨model, modeled, same⟩ := WireForwarding.finish_realizes _ _ _ _ _ processed
  have output := ordinary_service pipeline state entry direction packet (available.compatible valid)
    selected prepared attachment routed forward late model modeled
  have present : outcome.output.isSome = true := by
    rw [same]
    simp only [WireForwarding.ofLifecycle]
    split
    · rename_i absent
      rw [output] at absent
      cases absent
    · rfl
  cases emitted : outcome.output with
  | none => simp [emitted] at present
  | some emission =>
    have certified := forwarded pipeline state entry direction packet valid available udp selected outcome accepted emission emitted
    exact ⟨outcome, emission, accepted, emitted, certified.1, certified.2.2.1,
      certified.2.2.2.1, fields.2.2.1, outcome.valid⟩

end Netlib.Protocol.TrackedFlow
