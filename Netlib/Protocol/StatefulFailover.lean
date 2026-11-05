import Netlib.Protocol.ConntrackReplication
import Netlib.Protocol.ConntrackOperations
import Netlib.Protocol.WireForwarding

/-!
# Ordered gateway replication and handoff

A staged record comes from the primary's computed ordinary table.
Commitment and each endpoint's route handoff are separate operations.
Packets encounter the selected gateway's current supplied pipeline.
Detection, convergence, expiry, concurrent controls, and split-brain prevention remain outside this profile.
-/

namespace Netlib.Protocol.StatefulFailover

open Packet
abbrev Tracker := ConntrackLifecycle.State
abbrev Replica := ConntrackReplication.Selection

inductive Gateway where
  | primary
  | standby
  deriving Repr, BEq, DecidableEq

inductive Leg where
  | client
  | server
  deriving Repr, BEq, DecidableEq

structure Owners where
  client : Gateway := .primary
  server : Gateway := .primary
  deriving Repr, BEq, DecidableEq

def Owners.get (owners : Owners) : Leg → Gateway
  | .client => owners.client
  | .server => owners.server

def Owners.set (owners : Owners) (leg : Leg) (gateway : Gateway) : Owners :=
  match leg with
  | .client => { owners with client := gateway }
  | .server => { owners with server := gateway }

@[simp] theorem Owners.get_set (owners : Owners) (leg : Leg) (gateway : Gateway) :
    (owners.set leg gateway).get leg = gateway := by cases leg <;> rfl

structure State where
  primary : Tracker := .initial
  standby : Tracker := .initial
  cache : Option Replica := none
  owners : Owners := {}
  epoch : Nat := 0
  fenced : List Gateway := []

def State.initial : State := {}

def State.table (state : State) : Gateway → Tracker
  | .primary => state.primary
  | .standby => state.standby

def State.Valid (state : State) : Prop := state.primary.Valid ∧ state.standby.Valid

def State.isFenced (state : State) (gateway : Gateway) : Bool :=
  state.fenced.any (fun other => decide (other = gateway))

def State.write (state : State) (gateway : Gateway) (table : Tracker) : State :=
  match gateway with
  | .primary => { state with primary := table }
  | .standby => { state with standby := table }

@[simp] theorem State.table_write (state : State) (gateway : Gateway) (table : Tracker) :
    (state.write gateway table).table gateway = table := by cases gateway <;> rfl

theorem State.write_valid (state : State) (gateway : Gateway) (table : Tracker)
    (valid : state.Valid) (next : table.Valid) : (state.write gateway table).Valid := by
  cases gateway
  · exact ⟨next, valid.2⟩
  · exact ⟨valid.1, next⟩

theorem State.initial_valid : State.initial.Valid :=
  ⟨ConntrackLifecycle.State.initial_valid, ConntrackLifecycle.State.initial_valid⟩

structure PacketCall where
  gateway : Gateway
  leg : Leg
  pipeline : ConntrackLifecycle.Pipeline
  input : WireForwarding.Input

inductive Event where
  | packet (call : PacketCall)
  | stage (zone : Nat) (packet : Header)
  | commit (timeout : Nat)
  | handoff (leg : Leg) (gateway : Gateway)
  | fence (gateway : Gateway)
  | erase (gateway : Gateway) (zone : Nat) (packet : Header)
  | forget

structure PacketResult where
  call : PacketCall
  outcome : WireForwarding.Outcome call.input.packet

structure Result where
  state : State
  valid : state.Valid
  packet : Option PacketResult
  installed : Option ConntrackReplication.Installed

private def advance (state : State) : State := { state with epoch := state.epoch + 1 }

private theorem advance_valid (state : State) (valid : state.Valid) : (advance state).Valid := valid

def step (before : State) : Event → Except String Result
  | .packet call => do
    if call.gateway ≠ before.owners.get call.leg then
      throw "The packet gateway disagrees with the selected endpoint route."
    if before.isFenced call.gateway then
      throw "The selected gateway is fenced from data forwarding."
    if valid : before.primary.check = true ∧ before.standby.check = true then
      let outcome ← (WireForwarding.step call.pipeline (before.table call.gateway) call.input).mapError (·.describe)
      let after := before.write call.gateway outcome.state
      let checked := before.write_valid call.gateway outcome.state
        ⟨(ConntrackLifecycle.State.check_correct _).mp valid.1, (ConntrackLifecycle.State.check_correct _).mp valid.2⟩ outcome.valid
      return ⟨advance after, advance_valid _ checked, some ⟨call, outcome⟩, none⟩
    else throw "A gateway's ordinary conntrack table is invalid."
  | .stage zone packet => do
    if valid : before.primary.check = true ∧ before.standby.check = true then
      let selected ← (ConntrackReplication.stage before.primary before.epoch zone packet).mapError (·.describe)
      let after := { before with cache := some selected }
      return ⟨advance after,
        advance_valid _ ⟨(ConntrackLifecycle.State.check_correct _).mp valid.1, (ConntrackLifecycle.State.check_correct _).mp valid.2⟩,
        none, none⟩
    else throw "A gateway's ordinary conntrack table is invalid."
  | .commit timeout => do
    if valid : before.primary.check = true then
      let some selected := before.cache | throw "No staged primary record is available for commitment."
      let installed ← (ConntrackReplication.commit before.standby selected timeout).mapError (·.describe)
      let after := { before with standby := installed.state }
      return ⟨advance after, advance_valid _ ⟨(ConntrackLifecycle.State.check_correct _).mp valid, installed.valid⟩,
        none, some installed⟩
    else throw "The primary's ordinary conntrack table is invalid."
  | .handoff leg gateway => do
    if valid : before.primary.check = true ∧ before.standby.check = true then
      return ⟨advance { before with owners := before.owners.set leg gateway },
        advance_valid _ ⟨(ConntrackLifecycle.State.check_correct _).mp valid.1, (ConntrackLifecycle.State.check_correct _).mp valid.2⟩,
        none, none⟩
    else throw "A gateway's ordinary conntrack table is invalid."
  | .fence gateway => do
    if valid : before.primary.check = true ∧ before.standby.check = true then
      return ⟨advance { before with fenced := gateway :: before.fenced },
        advance_valid _ ⟨(ConntrackLifecycle.State.check_correct _).mp valid.1,
          (ConntrackLifecycle.State.check_correct _).mp valid.2⟩, none, none⟩
    else throw "A gateway's ordinary conntrack table is invalid."
  | .erase gateway zone packet => do
    if valid : before.primary.check = true ∧ before.standby.check = true then
      let erased ← (ConntrackLifecycle.Operations.step (before.table gateway) (.erase zone packet)).mapError (·.describe)
      let after := before.write gateway erased.state
      return ⟨advance after, advance_valid _ (before.write_valid gateway erased.state
        ⟨(ConntrackLifecycle.State.check_correct _).mp valid.1, (ConntrackLifecycle.State.check_correct _).mp valid.2⟩ erased.valid), none, none⟩
    else throw "A gateway's ordinary conntrack table is invalid."
  | .forget => do
    if valid : before.primary.check = true ∧ before.standby.check = true then
      return ⟨advance { before with cache := none },
        advance_valid _ ⟨(ConntrackLifecycle.State.check_correct _).mp valid.1, (ConntrackLifecycle.State.check_correct _).mp valid.2⟩,
        none, none⟩
    else throw "A gateway's ordinary conntrack table is invalid."

theorem step_valid (before : State) (event : Event) (result : Result)
    (_accepted : step before event = .ok result) : result.state.Valid := result.valid

theorem step_packet (before : State) (call : PacketCall) (result : Result)
    (accepted : step before (.packet call) = .ok result) :
    call.gateway = before.owners.get call.leg ∧ before.isFenced call.gateway = false ∧
      ∃ outcome, WireForwarding.step call.pipeline (before.table call.gateway) call.input = .ok outcome ∧
        result.packet = some ⟨call, outcome⟩ ∧
        result.state.table call.gateway = outcome.state ∧
        result.state.cache = before.cache ∧ result.state.owners = before.owners ∧
        result.state.epoch = before.epoch + 1 := by
  simp only [step] at accepted
  split at accepted
  · simp [bind, throw, Except.bind] at accepted
  · rename_i owner
    split at accepted
    · simp [bind, throw, Except.bind] at accepted
    · rename_i unfenced
      split at accepted
      · cases computed : WireForwarding.step call.pipeline (before.table call.gateway) call.input with
        | error reason => simp [computed, bind, Except.bind, Except.mapError] at accepted
        | ok outcome =>
          simp only [computed, Except.mapError, bind, Except.bind, pure, Except.pure] at accepted
          cases accepted
          refine ⟨by simpa using owner, by simpa using unfenced, outcome, rfl, rfl, ?_, ?_, ?_, ?_⟩
          · exact State.table_write _ _ _
          · change (before.write call.gateway outcome.state).cache = before.cache
            cases call.gateway <;> rfl
          · change (before.write call.gateway outcome.state).owners = before.owners
            cases call.gateway <;> rfl
          · change (before.write call.gateway outcome.state).epoch + 1 = before.epoch + 1
            cases call.gateway <;> rfl
      · simp [throw] at accepted

theorem step_stage (before : State) (zone : Nat) (packet : Header) (result : Result)
    (accepted : step before (.stage zone packet) = .ok result) :
    ∃ selected, ConntrackReplication.stage before.primary before.epoch zone packet = .ok selected ∧
      result.state.cache = some selected ∧ selected.source = before.primary ∧
      selected.sourceEpoch = before.epoch ∧ selected.record ∈ before.primary.records ∧
      selected.record.entry.flow.key selected.direction = (zone, packet) ∧
      result.state.primary = before.primary ∧ result.state.standby = before.standby ∧
      result.state.owners = before.owners ∧ result.state.epoch = before.epoch + 1 := by
  simp only [step] at accepted
  split at accepted
  · cases computed : ConntrackReplication.stage before.primary before.epoch zone packet with
    | error reason => simp [computed, bind, Except.bind, Except.mapError] at accepted
    | ok selected =>
      simp only [computed, Except.mapError, bind, Except.bind, pure, Except.pure] at accepted
      cases accepted
      obtain ⟨source, epoch, member, attached⟩ := ConntrackReplication.stage_origin _ _ _ _ _ computed
      exact ⟨selected, rfl, rfl, source, epoch, member, attached, rfl, rfl, rfl, rfl⟩
  · simp [throw] at accepted

theorem step_commit (before : State) (timeout : Nat) (result : Result)
    (accepted : step before (.commit timeout) = .ok result) :
    ∃ selected installed, before.cache = some selected ∧
      ConntrackReplication.commit before.standby selected timeout = .ok installed ∧
      result.installed = some installed ∧ result.state.standby = installed.state ∧
      result.state.standby.records = before.standby.records ++ [selected.recordForInstall] ∧
      result.state.primary = before.primary ∧ result.state.cache = before.cache ∧
      result.state.owners = before.owners ∧ result.state.epoch = before.epoch + 1 := by
  simp only [step] at accepted
  split at accepted
  · cases cached : before.cache with
    | none => simp [cached, throw] at accepted
    | some selected =>
      simp only [cached] at accepted
      cases computed : ConntrackReplication.commit before.standby selected timeout with
      | error reason => simp [computed, bind, Except.bind, Except.mapError] at accepted
      | ok installed =>
        simp only [computed, Except.mapError, bind, Except.bind, pure, Except.pure] at accepted
        cases accepted
        obtain ⟨old, selection, _⟩ := ConntrackReplication.commit_fields _ _ _ _ computed
        refine ⟨selected, installed, rfl, computed, rfl, rfl, ?_, rfl, rfl, rfl, rfl⟩
        change installed.state.records = before.standby.records ++ [selected.recordForInstall]
        simpa only [old, selection] using installed.records
  · simp [throw] at accepted

theorem step_handoff (before : State) (leg : Leg) (gateway : Gateway) (result : Result)
    (accepted : step before (.handoff leg gateway) = .ok result) :
    result.state.owners = before.owners.set leg gateway ∧
      result.state.owners.get leg = gateway ∧
      result.state.primary = before.primary ∧ result.state.standby = before.standby ∧
      result.state.cache = before.cache ∧ result.state.epoch = before.epoch + 1 ∧
      result.packet = none ∧ result.installed = none := by
  simp only [step] at accepted
  split at accepted
  · simp only [pure, Except.pure] at accepted
    cases accepted
    exact ⟨rfl, Owners.get_set _ _ _, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · simp [throw] at accepted

theorem step_fence (before : State) (gateway : Gateway) (result : Result)
    (accepted : step before (.fence gateway) = .ok result) :
    result.state.isFenced gateway = true ∧ result.state.cache = before.cache ∧
      result.state.primary = before.primary ∧ result.state.standby = before.standby ∧
      result.state.owners = before.owners ∧ result.state.epoch = before.epoch + 1 := by
  simp only [step] at accepted
  split at accepted
  · simp only [pure, Except.pure] at accepted
    cases accepted
    exact ⟨by simp [State.isFenced, advance], rfl, rfl, rfl, rfl, rfl⟩
  · simp [throw] at accepted

theorem step_erase (before : State) (gateway : Gateway) (zone : Nat) (packet : Header) (result : Result)
    (accepted : step before (.erase gateway zone packet) = .ok result) :
    ∃ erased, ConntrackLifecycle.Operations.step (before.table gateway) (.erase zone packet) = .ok erased ∧
      result.state.table gateway = erased.state ∧ result.state.cache = before.cache ∧
      result.state.owners = before.owners ∧ result.state.epoch = before.epoch + 1 := by
  simp only [step] at accepted
  split at accepted
  · cases computed : ConntrackLifecycle.Operations.step (before.table gateway) (.erase zone packet) with
    | error reason => simp [computed, bind, Except.bind, Except.mapError] at accepted
    | ok erased =>
      simp only [computed, Except.mapError, bind, Except.bind, pure, Except.pure] at accepted
      cases accepted
      refine ⟨erased, rfl, State.table_write _ _ _, ?_, ?_, ?_⟩
      · change (before.write gateway erased.state).cache = before.cache
        cases gateway <;> rfl
      · change (before.write gateway erased.state).owners = before.owners
        cases gateway <;> rfl
      · change (before.write gateway erased.state).epoch + 1 = before.epoch + 1
        cases gateway <;> rfl
  · simp [throw] at accepted

theorem step_forget (before : State) (result : Result)
    (accepted : step before .forget = .ok result) : result.state.cache = none := by
  simp only [step] at accepted
  split at accepted
  · simp only [pure, Except.pure] at accepted
    cases accepted
    rfl
  · simp [throw] at accepted

theorem step_cache_origin (before : State) (event : Event) (result : Result) (selected : Replica)
    (accepted : step before event = .ok result) (cached : result.state.cache = some selected) :
    before.cache = some selected ∨
      ∃ zone packet, event = .stage zone packet ∧
        selected.source = before.primary ∧ selected.sourceEpoch = before.epoch ∧
        selected.record ∈ before.primary.records ∧
        selected.record.entry.flow.key selected.direction = (zone, packet) := by
  cases event with
  | packet call =>
    obtain ⟨_, _, _, _, _, _, cache, _, _⟩ := step_packet _ _ _ accepted
    exact Or.inl (cache.symm.trans cached)
  | stage zone packet =>
    obtain ⟨staged, _, cache, source, epoch, member, attached, _⟩ := step_stage _ _ _ _ accepted
    have same : staged = selected := Option.some.inj (cache.symm.trans cached)
    subst staged
    exact Or.inr ⟨zone, packet, rfl, source, epoch, member, attached⟩
  | commit timeout =>
    obtain ⟨_, _, _, _, _, _, _, _, cache, _⟩ := step_commit _ _ _ accepted
    exact Or.inl (cache.symm.trans cached)
  | handoff leg gateway =>
    have cache := (step_handoff _ _ _ _ accepted).2.2.2.2.1
    exact Or.inl (cache.symm.trans cached)
  | fence gateway => exact Or.inl ((step_fence _ _ _ accepted).2.1.symm.trans cached)
  | erase gateway zone packet =>
    obtain ⟨_, _, _, cache, _⟩ := step_erase _ _ _ _ _ accepted
    exact Or.inl (cache.symm.trans cached)
  | forget => simp [step_forget _ _ accepted] at cached

end Netlib.Protocol.StatefulFailover
