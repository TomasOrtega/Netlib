import Netlib.Protocol.ConntrackLifecycle

/-!
# Checked ordinary conntrack replication

Staging selects a record from an explicit source state and epoch.
Commit installs its normalized tuple, NAT, and seen-reply projection.
The configured positive commit timeout is metadata. This model does not evolve time.
Native success requires separate observation. Daemon exit status alone does not establish installation.
Collisions are unsupported because native commit can destroy an existing record before retrying.
-/

namespace Netlib.Protocol.ConntrackReplication

open Packet
open ConntrackLifecycle (Record State)

inductive Error where
  | invalidSource
  | unsupportedProfile
  | missingRecord
  | invalidTarget
  | invalidCommitTTL
  | unsupportedCollision
  deriving Repr, BEq, DecidableEq

def Error.describe : Error → String
  | .invalidSource => "The source ordinary conntrack table is invalid."
  | .unsupportedProfile => "Require a normalized UDP record with both direction zones zero."
  | .missingRecord => "The selected source tuple has no confirmed record."
  | .invalidTarget => "The standby ordinary conntrack table is invalid."
  | .invalidCommitTTL => "Require a positive commit timeout below 2^32."
  | .unsupportedCollision => "Colliding native commit and destructive retry are outside this profile."

def Profile (record : Record) : Prop :=
  record.entry.flow.original.protocol = Protocol.udp ∧
  record.entry.flow.originalZone = 0 ∧ record.entry.flow.replyZone = 0 ∧
  record.entry.flow.remainingTTL = 0

instance (record : Record) : Decidable (Profile record) := by unfold Profile; infer_instance

structure Selection where
  sourceEpoch : Nat
  source : State
  sourceValid : source.Valid
  record : Record
  member : record ∈ source.records
  profile : Profile record
  direction : FlowNAT.Direction
  zone : Nat
  packet : Header
  attached : record.entry.flow.key direction = (zone, packet)

def Selection.recordForInstall (selection : Selection) : Record := selection.record

def stage (source : State) (sourceEpoch zone : Nat) (packet : Header) : Except Error Selection := do
  if valid : source.check = true then
    match found : source.model.lookup zone packet with
    | none => throw .missingRecord
    | some hit =>
      match row : source.records.find? (fun record => decide (record.entry.flow = hit.entry)) with
      | none => throw .invalidSource
      | some record =>
        if profile : Profile record then
          have same : record.entry.flow = hit.entry := of_decide_eq_true (List.find?_some
            (p := fun item : Record => decide (item.entry.flow = hit.entry)) (a := record) row)
          return ⟨sourceEpoch, source, (State.check_correct _).mp valid, record,
            List.mem_of_find?_eq_some row, profile, hit.direction, zone, packet,
            by rw [same]; exact (FlowNAT.Snapshot.lookup_sound _ _ _ _ found).2⟩
        else throw .unsupportedProfile
  else throw .invalidSource

theorem stage_origin (source : State) (sourceEpoch zone : Nat) (packet : Header) (selection : Selection)
    (accepted : stage source sourceEpoch zone packet = .ok selection) :
    selection.source = source ∧ selection.sourceEpoch = sourceEpoch ∧ selection.record ∈ source.records ∧
      selection.record.entry.flow.key selection.direction = (zone, packet) := by
  have fields : selection.source = source ∧ selection.sourceEpoch = sourceEpoch ∧
      selection.zone = zone ∧ selection.packet = packet := by
    unfold stage at accepted
    repeat' first
      | (cases accepted; exact ⟨rfl, rfl, rfl, rfl⟩)
      | (split at accepted <;> try simp [throw, pure, Except.pure] at accepted)
  exact ⟨fields.1, fields.2.1, by rw [← fields.1]; exact selection.member,
    by simpa only [fields.2.2.1, fields.2.2.2] using selection.attached⟩

structure Installed where
  before : State
  selection : Selection
  commitTTL : Nat
  timeout : 0 < commitTTL ∧ commitTTL < 4294967296
  state : State
  valid : state.Valid
  records : state.records = before.records ++ [selection.recordForInstall]

def commit (before : State) (selection : Selection) (commitTTL : Nat) : Except Error Installed := do
  if before.check = true then
    if timeout : 0 < commitTTL ∧ commitTTL < 4294967296 then
      let after : State := ⟨before.records ++ [selection.recordForInstall]⟩
      if valid : after.check = true then
        return ⟨before, selection, commitTTL, timeout, after, (State.check_correct _).mp valid, rfl⟩
      else throw .unsupportedCollision
    else throw .invalidCommitTTL
  else throw .invalidTarget

theorem commit_fields (before : State) (selection : Selection) (commitTTL : Nat) (installed : Installed)
    (accepted : commit before selection commitTTL = .ok installed) :
    installed.before = before ∧ installed.selection = selection ∧ installed.commitTTL = commitTTL := by
  unfold commit at accepted
  repeat' first
    | (cases accepted; exact ⟨rfl, rfl, rfl⟩)
    | (split at accepted <;> try simp [throw, pure, Except.pure] at accepted)

theorem commit_valid (before : State) (selection : Selection) (commitTTL : Nat) (installed : Installed)
    (_accepted : commit before selection commitTTL = .ok installed) : installed.state.Valid := installed.valid

theorem Installed.only_selected (installed : Installed) (record : Record) :
    record ∈ installed.state.records ↔ record ∈ installed.before.records ∨ record = installed.selection.recordForInstall := by
  rw [installed.records]
  simp

theorem Installed.selected_member (installed : Installed) :
    installed.selection.recordForInstall ∈ installed.state.records :=
  (installed.only_selected _).mpr (Or.inr rfl)

theorem Installed.old_member (installed : Installed) (record : Record) (member : record ∈ installed.before.records) :
    record ∈ installed.state.records := (installed.only_selected _).mpr (Or.inl member)

theorem Installed.provenance (installed : Installed) :
    installed.selection.recordForInstall ∈ installed.selection.source.records := installed.selection.member

theorem Installed.keys (installed : Installed) : installed.state.model.keys.Nodup := installed.valid.1.2

theorem Installed.key_absent (installed : Installed) (direction : FlowNAT.Direction) :
    installed.selection.recordForInstall.entry.flow.key direction ∉ installed.before.model.keys := by
  have expanded : installed.state.model.keys = installed.before.model.keys ++
      [installed.selection.recordForInstall.entry.flow.key .original,
        installed.selection.recordForInstall.entry.flow.key .reply] := by
    simp only [State.model, FlowNAT.Snapshot.keys, FlowNAT.Snapshot.slots]
    rw [installed.records]
    simp [List.flatMap_append, FlowNAT.Hit.key]
  have unique := installed.keys
  rw [expanded] at unique
  have disjoint := (List.nodup_append.mp unique).2.2
  intro member
  apply disjoint _ member (installed.selection.recordForInstall.entry.flow.key direction)
  · cases direction <;> simp
  · rfl

theorem Installed.fresh_lookup (installed : Installed) (direction : FlowNAT.Direction) :
    installed.before.model.lookup (installed.selection.recordForInstall.entry.flow.zone direction)
      (installed.selection.recordForInstall.entry.flow.input direction) = none := by
  cases found : installed.before.model.lookup (installed.selection.recordForInstall.entry.flow.zone direction)
      (installed.selection.recordForInstall.entry.flow.input direction) with
  | none => rfl
  | some hit =>
    obtain ⟨member, same⟩ := FlowNAT.Snapshot.lookup_sound _ _ _ _ found
    exact False.elim (installed.key_absent direction (List.mem_map.mpr
      ⟨hit, (FlowNAT.Snapshot.mem_slots _ _).mpr member, same⟩))

theorem Installed.lookup_other (installed : Installed) (zone : Nat) (packet : Header)
    (original : installed.selection.recordForInstall.entry.flow.key .original ≠ (zone, packet))
    (reply : installed.selection.recordForInstall.entry.flow.key .reply ≠ (zone, packet)) :
    installed.state.model.lookup zone packet = installed.before.model.lookup zone packet := by
  simp only [State.model, FlowNAT.Snapshot.lookup, FlowNAT.Snapshot.slots]
  rw [installed.records]
  simp [List.flatMap_append, List.find?_append, FlowNAT.Hit.key, original, reply]

theorem Installed.find_record (installed : Installed) :
    installed.state.records.find? (fun record => decide
      (record.entry.flow = installed.selection.recordForInstall.entry.flow)) =
        some installed.selection.recordForInstall := by
  have absent : installed.before.records.find? (fun record => decide
      (record.entry.flow = installed.selection.recordForInstall.entry.flow)) = none := by
    apply List.find?_eq_none.mpr
    intro record member matched
    have same : record.entry.flow = installed.selection.recordForInstall.entry.flow := of_decide_eq_true matched
    apply installed.key_absent .original
    exact List.mem_map.mpr ⟨⟨record.entry.flow, .original⟩,
      (FlowNAT.Snapshot.mem_slots _ _).mpr (List.mem_map.mpr ⟨record, member, rfl⟩),
      by simp [FlowNAT.Hit.key, same]⟩
  rw [installed.records, List.find?_append, absent]
  simp

theorem Installed.lookup (installed : Installed) (direction : FlowNAT.Direction) :
    installed.state.model.lookup (installed.selection.recordForInstall.entry.flow.zone direction)
      (installed.selection.recordForInstall.entry.flow.input direction) =
        some ⟨installed.selection.recordForInstall.entry.flow, direction⟩ := by
  have found := FlowNAT.Snapshot.lookup_complete _ installed.valid.1
    ⟨installed.selection.recordForInstall.entry.flow, direction⟩
    (List.mem_map.mpr ⟨_, installed.selected_member, rfl⟩)
  simpa only [FlowNAT.Hit.key, FlowNAT.Entry.key] using found

theorem Installed.translate (installed : Installed) (direction : FlowNAT.Direction) :
    installed.state.model.translate (installed.selection.recordForInstall.entry.flow.zone direction)
      (installed.selection.recordForInstall.entry.flow.input direction) =
        some (installed.selection.record.entry.flow.output direction) := by
  exact FlowNAT.Snapshot.translate_entry _ installed.valid.1 _
    (List.mem_map.mpr ⟨_, installed.selected_member, rfl⟩) direction

theorem Installed.rewrite (installed : Installed) (direction : FlowNAT.Direction) :
    (installed.selection.recordForInstall.entry.rewrite direction).apply
      (installed.selection.record.entry.flow.input direction) =
        installed.selection.record.entry.flow.output direction :=
  installed.selection.record.entry.rewrite_correct
    (installed.selection.sourceValid.2 _ installed.selection.member) direction

theorem Installed.classification (installed : Installed) (direction : FlowNAT.Direction) :
    ConntrackLifecycle.classify installed.selection.recordForInstall direction =
      ConntrackLifecycle.classify installed.selection.record direction := rfl

def Selection.input (selection : Selection) (direction : FlowNAT.Direction) : ConntrackLifecycle.Input :=
  ⟨selection.record.entry.flow.zone direction, selection.record.entry.flow.input direction, none⟩

theorem Selection.zone_zero (selection : Selection) (direction : FlowNAT.Direction) :
    (selection.input direction).zone = 0 := by
  cases direction
  · exact selection.profile.2.1
  · exact selection.profile.2.2.1

theorem Selection.transport (selection : Selection) (direction : FlowNAT.Direction) :
    Conntrack.transport (selection.input direction).packet = true := by
  have compatible := selection.sourceValid.2 _ selection.member
  have protocol : (selection.input direction).packet.protocol = Protocol.udp := by
    cases direction
    · exact selection.profile.1
    · exact compatible.1.1.symm.trans selection.profile.1
  simp [Conntrack.transport, protocol]

theorem Installed.prepare (installed : Installed) (direction : FlowNAT.Direction) :
    ∃ prepared : ConntrackLifecycle.Prepared (installed.selection.input direction),
      ConntrackLifecycle.prepare installed.state (installed.selection.input direction) = .ok prepared ∧
      prepared.attachment.entry = installed.selection.record.entry ∧
      prepared.attachment.direction = direction ∧
      prepared.attachment.classification = ConntrackLifecycle.classify installed.selection.record direction ∧
      prepared.attachment.fresh = false ∧
      prepared.state = ((fun selected : FlowNAT.Direction => match selected with
        | .original => installed.state
        | .reply => installed.state.markReply installed.selection.record.entry.flow) direction) := by
  have checked := (State.check_correct _).mpr installed.valid
  have compatible := installed.selection.sourceValid.2 _ installed.selection.member
  have found : installed.state.model.lookup (installed.selection.input direction).zone
      (installed.selection.input direction).packet = some ⟨installed.selection.record.entry.flow, direction⟩ :=
    installed.lookup direction
  have record : installed.state.records.find? (fun record => decide
      (record.entry.flow = installed.selection.record.entry.flow)) = some installed.selection.record := installed.find_record
  have zero := installed.selection.zone_zero direction
  have transport := installed.selection.transport direction
  have bounded : ¬ (installed.selection.input direction).zone ≥ 65536 := by rw [zero]; decide
  have candidate : (installed.selection.input direction).candidate = none := rfl
  cases direction with
  | original =>
    let prepared : ConntrackLifecycle.Prepared (installed.selection.input .original) :=
      ⟨installed.state, installed.valid,
        ⟨installed.selection.record.entry, .original,
          ConntrackLifecycle.classify installed.selection.record .original, false⟩, compatible, rfl⟩
    refine ⟨prepared, ?_, rfl, rfl, rfl, rfl, rfl⟩
    simp only [ConntrackLifecycle.prepare, checked, dite_true, bounded, ite_false,
      transport, Bool.not_true, Bool.false_eq_true, candidate, Option.isSome_none]
    split
    · rename_i absent
      rw [found] at absent
      cases absent
    · rename_i hit equation
      have same := Option.some.inj (equation.symm.trans found)
      subst hit
      split
      · rename_i absent
        rw [record] at absent
        cases absent
      · rename_i selected equation
        have same := Option.some.inj (equation.symm.trans record)
        subst selected
        rfl
  | reply =>
    let prepared : ConntrackLifecycle.Prepared (installed.selection.input .reply) :=
      ⟨installed.state.markReply installed.selection.record.entry.flow,
        State.markReply_valid _ _ installed.valid,
        ⟨installed.selection.record.entry, .reply,
          ConntrackLifecycle.classify installed.selection.record .reply, false⟩, compatible, rfl⟩
    refine ⟨prepared, ?_, rfl, rfl, rfl, rfl, rfl⟩
    simp only [ConntrackLifecycle.prepare, checked, dite_true, bounded, ite_false,
      transport, Bool.not_true, Bool.false_eq_true, candidate, Option.isSome_none]
    split
    · rename_i absent
      rw [found] at absent
      cases absent
    · rename_i hit equation
      have same := Option.some.inj (equation.symm.trans found)
      subst hit
      split
      · rename_i absent
        rw [record] at absent
        cases absent
      · rename_i selected equation
        have same := Option.some.inj (equation.symm.trans record)
        subst selected
        rfl

theorem Installed.prepare_fields (installed : Installed) (direction : FlowNAT.Direction)
    (prepared : ConntrackLifecycle.Prepared (installed.selection.input direction))
    (accepted : ConntrackLifecycle.prepare installed.state (installed.selection.input direction) = .ok prepared) :
    prepared.attachment.entry = installed.selection.record.entry ∧
      prepared.attachment.direction = direction ∧
      prepared.attachment.classification = ConntrackLifecycle.classify installed.selection.record direction ∧
      prepared.attachment.fresh = false ∧
      prepared.state = ((fun selected : FlowNAT.Direction => match selected with
        | .original => installed.state
        | .reply => installed.state.markReply installed.selection.record.entry.flow) direction) := by
  obtain ⟨actual, computed, fields⟩ := installed.prepare direction
  have same := Except.ok.inj (computed.symm.trans accepted)
  subst actual
  exact fields

theorem Installed.step_binding (installed : Installed) (direction : FlowNAT.Direction)
    (pipeline : ConntrackLifecycle.Pipeline) (outcome : ConntrackLifecycle.Outcome)
    (accepted : ConntrackLifecycle.step pipeline installed.state (installed.selection.input direction) = .ok outcome) :
    outcome.attachment.entry = installed.selection.record.entry ∧
      outcome.attachment.direction = direction ∧
      outcome.attachment.classification = ConntrackLifecycle.classify installed.selection.record direction ∧
      outcome.attachment.fresh = false ∧
      outcome.state = ((fun selected : FlowNAT.Direction => match selected with
        | .original => installed.state
        | .reply => installed.state.markReply installed.selection.record.entry.flow) direction) := by
  obtain ⟨prepared, attached, processed⟩ := ConntrackLifecycle.step_prepared _ _ _ _ accepted
  obtain ⟨entry, selected, classified, existing, state⟩ := installed.prepare_fields direction prepared attached
  have attachment := ConntrackLifecycle.process_attachment _ _ _ processed
  have retained := ConntrackLifecycle.process_existing_state _ _ _ processed existing
  exact ⟨by rw [attachment, entry], by rw [attachment, selected], by rw [attachment, classified],
    by rw [attachment, existing], retained.trans state⟩

theorem Installed.forwarded (installed : Installed) (direction : FlowNAT.Direction)
    (pipeline : ConntrackLifecycle.Pipeline) (outcome : ConntrackLifecycle.Outcome) (packet : Header)
    (accepted : ConntrackLifecycle.step pipeline installed.state (installed.selection.input direction) = .ok outcome)
    (forwarded : outcome.output = some packet) :
    packet = installed.selection.record.entry.flow.output direction ∧
      StatefulACL.Policy.evaluate pipeline.forwardDefault pipeline.forward
        (ConntrackLifecycle.classify installed.selection.record direction) outcome.afterDestination = .permit ∧
      StatefulACL.Policy.evaluate pipeline.lateDefault pipeline.late
        (ConntrackLifecycle.classify installed.selection.record direction) packet = .permit ∧
      outcome.state.Valid := by
  obtain ⟨entry, selected, classified, _, _⟩ := installed.step_binding direction pipeline outcome accepted
  have rewritten := ConntrackLifecycle.step_output _ _ _ _ _ accepted forwarded
  rw [entry, selected] at rewritten
  obtain ⟨_, allowed, late, _, _⟩ := ConntrackLifecycle.step_filters _ _ _ _ _ accepted forwarded
  rw [classified] at allowed late
  exact ⟨rewritten, allowed, late, outcome.valid⟩

theorem commit_completes (before : State) (selection : Selection) (commitTTL : Nat)
    (valid : before.Valid) (timeout : 0 < commitTTL ∧ commitTTL < 4294967296)
    (available : ∀ direction, selection.recordForInstall.entry.flow.key direction ∉ before.model.keys) :
    ∃ installed, commit before selection commitTTL = .ok installed := by
  let after : State := ⟨before.records ++ [selection.recordForInstall]⟩
  have compatible : selection.recordForInstall.entry.Compatible := selection.sourceValid.2 _ selection.member
  have expanded : after.model.keys = before.model.keys ++
      [selection.recordForInstall.entry.flow.key .original, selection.recordForInstall.entry.flow.key .reply] := by
    simp [after, State.model, FlowNAT.Snapshot.keys, FlowNAT.Snapshot.slots, List.flatMap_append, FlowNAT.Hit.key]
  have unique : after.model.keys.Nodup := by
    rw [expanded]
    apply List.nodup_append.mpr
    refine ⟨valid.1.2, ?_, ?_⟩
    · simpa using compatible.1.2.2.2.2.2
    · intro oldKey oldMember newKey newMember same
      rcases List.mem_cons.mp newMember with rfl | last
      · exact available .original (same ▸ oldMember)
      · have equal := List.mem_singleton.mp last
        exact available .reply (by rw [← equal, ← same]; exact oldMember)
  have afterValid : after.Valid := by
    constructor
    · constructor
      · intro flow member
        obtain ⟨record, belongs, rfl⟩ := List.mem_map.mp member
        rcases List.mem_append.mp belongs with old | current
        · exact (valid.2 record old).1
        · have equal := List.mem_singleton.mp current
          subst record
          exact compatible.1
      · exact unique
    · intro record belongs
      rcases List.mem_append.mp belongs with old | current
      · exact valid.2 record old
      · have equal := List.mem_singleton.mp current
        subst record
        exact compatible
  have checked := (State.check_correct _).mpr valid
  have afterChecked := (State.check_correct _).mpr afterValid
  change ({ records := before.records ++ [selection.recordForInstall] } : State).check = true at afterChecked
  cases accepted : commit before selection commitTTL with
  | ok installed => exact ⟨installed, rfl⟩
  | error error => simp [commit, checked, timeout, afterChecked, pure, Except.pure] at accepted

theorem commit_initial (selection : Selection) (commitTTL : Nat)
    (timeout : 0 < commitTTL ∧ commitTTL < 4294967296) :
    ∃ installed, commit State.initial selection commitTTL = .ok installed :=
  commit_completes _ _ _ State.initial_valid timeout (by
    intro direction
    simp [State.initial, State.model, FlowNAT.Snapshot.keys, FlowNAT.Snapshot.slots])
end Netlib.Protocol.ConntrackReplication
