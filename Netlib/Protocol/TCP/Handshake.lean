import Netlib.Protocol.TCP.ControlOutput
import Netlib.Protocol.TCP.Endpoint

/-!
# Checked ordinary TCP startup

This profile uses SYN, SYN,ACK, and ACK with no data or options.
It derives application cursors and peer fields from checked startup inputs.
Local configuration and output policy remain explicit inputs.
The active window initialization uses RFC 1122, section 4.2.2.20(c).
Unsupported processing preserves the supplied phase and requires a replay stop.
The profile does not prove native transmission or connection-instance freshness.
-/

namespace Netlib.Protocol.TCP.Handshake

abbrev Input := EstablishedReceive.Input

structure Socket where
  address : Packet.Address
  port : Packet.Port
  deriving Repr, BEq, DecidableEq

structure Local where
  socket : Socket
  iss : Seq
  capacity : Nat
  pendingLimit : Nat
  ipSendLimit : Nat
  deriving Repr, BEq, DecidableEq

def Local.Valid (config : Local) : Prop :=
  config.capacity ≤ 65535 ∧ config.pendingLimit ≤ 65535 ∧
    40 < config.ipSendLimit ∧ config.ipSendLimit ≤ 65535

instance (config : Local) : Decidable config.Valid := by unfold Local.Valid; infer_instance

def outbound (config : Local) (remote : Socket) : Packet.Header :=
  ⟨config.socket.address, remote.address, Packet.Protocol.tcp, config.socket.port, remote.port⟩

def inbound (config : Local) (remote : Socket) : Packet.Header := Output.reverse (outbound config remote)

def destination (config : Local) (input : Input) : Prop :=
  input.packet.header.destination = config.socket.address ∧ input.packet.header.destinationPort = config.socket.port

instance (config : Local) (input : Input) : Decidable (destination config input) := by
  unfold destination
  infer_instance

def Profile (input : Input) (flags : UInt8) : Prop :=
  input.packet.segment.flags = flags ∧ input.packet.segment.options = [] ∧ input.packet.segment.payload = []

instance (input : Input) (flags : UInt8) : Decidable (Profile input flags) := by unfold Profile; infer_instance

inductive Reject where
  | invalidConfig | policy | tuple | encoding
  deriving Repr, BEq, DecidableEq

inductive Unsupported where
  | flags | options | data | acknowledgment | sequence
  deriving Repr, BEq, DecidableEq

inductive Failure where
  | reject (reason : Reject)
  | unsupported (reason : Unsupported)
  deriving Repr, BEq, DecidableEq

def Failure.message : Failure → String
  | .reject .invalidConfig => "The local TCP configuration exceeds its selected limits."
  | .reject .policy => "The output policy does not permit this startup event."
  | .reject .tuple => "The checked input does not match this endpoint tuple."
  | .reject .encoding => "The selected startup output could not be encoded."
  | .unsupported .flags => "The startup flags require processing outside this profile."
  | .unsupported .options => "Startup option processing is outside this profile."
  | .unsupported .data => "Startup data processing is outside this profile."
  | .unsupported .acknowledgment => "The startup ACK requires processing outside this profile."
  | .unsupported .sequence => "The startup sequence requires processing outside this profile."

def profileReason (input : Input) : Unsupported :=
  if input.packet.segment.options ≠ [] then .options
  else if input.packet.segment.payload ≠ [] then .data
  else .flags

structure SynSent where
  config : Local
  remote : Socket
  output : Input
  localValid : config.Valid
  generated : ControlOutput.emit (outbound config remote) config.iss (Seq.ofNat 0) 2 config.capacity = .ok output

structure SynReceived where
  config : Local
  input : Input
  output : Input
  localValid : config.Valid
  destination : Handshake.destination config input
  profile : Profile input 2
  generated : ControlOutput.emit (Output.reverse input.packet.header) config.iss
    (input.packet.segment.sequence.add 1) 18 config.capacity = .ok output

def effectiveMSS (config : Local) : Nat := min 536 (config.ipSendLimit - 40)

def activeSeed (pending : SynSent) (input : Input) : Endpoint.State := {
  core := ⟨inbound pending.config pending.remote, input.packet.segment.sequence.add 1,
    pending.config.capacity, [], pending.config.iss.add 1, pending.config.iss.add 1, []⟩
  pending := []
  pendingLimit := pending.config.pendingLimit
  sendWindow := input.packet.segment.window.val
  sendWL1 := input.packet.segment.sequence
  sendWL2 := input.packet.segment.acknowledgment
  effectiveMSS := effectiveMSS pending.config
  ipSendLimit := pending.config.ipSendLimit }

def passiveSeed (pending : SynReceived) (input : Input) : Endpoint.State := {
  core := ⟨pending.input.packet.header, pending.input.packet.segment.sequence.add 1,
    pending.config.capacity, [], pending.config.iss.add 1, pending.config.iss.add 1, []⟩
  pending := []
  pendingLimit := pending.config.pendingLimit
  sendWindow := input.packet.segment.window.val
  sendWL1 := input.packet.segment.sequence
  sendWL2 := input.packet.segment.acknowledgment
  effectiveMSS := effectiveMSS pending.config
  ipSendLimit := pending.config.ipSendLimit }

theorem effectiveMSS_bounds (config : Local) (valid : config.Valid) :
    0 < effectiveMSS config ∧ effectiveMSS config ≤ 536 ∧ 40 + effectiveMSS config ≤ config.ipSendLimit := by
  have upper := Nat.min_le_right 536 (config.ipSendLimit - 40)
  have lower := valid.2.2.1
  unfold effectiveMSS
  omega

theorem activeSeed_valid (pending : SynSent) (input : Input) : (activeSeed pending input).Valid := by
  obtain ⟨capacity, storage, _, size⟩ := pending.localValid
  obtain ⟨positive, _, limit⟩ := effectiveMSS_bounds pending.config pending.localValid
  have window := input.packet.segment.window.isLt
  refine ⟨⟨rfl, by simp [activeSeed], capacity, by simp [activeSeed], ?_, ?_⟩,
    by simp [activeSeed], storage, by dsimp [activeSeed]; omega, positive, limit, size⟩
  · simp [activeSeed]
  · change 0 + EstablishedReceive.maxSendWindow < Seq.halfSpace
    decide

theorem passiveSeed_valid (pending : SynReceived) (input : Input) : (passiveSeed pending input).Valid := by
  obtain ⟨capacity, storage, _, size⟩ := pending.localValid
  obtain ⟨positive, _, limit⟩ := effectiveMSS_bounds pending.config pending.localValid
  have window := input.packet.segment.window.isLt
  refine ⟨⟨rfl, by simp [passiveSeed], capacity, by simp [passiveSeed], ?_, ?_⟩,
    by simp [passiveSeed], storage, by dsimp [passiveSeed]; omega, positive, limit, size⟩
  · simp [passiveSeed]
  · change 0 + EstablishedReceive.maxSendWindow < Seq.halfSpace
    decide

def ActiveAccepted (pending : SynSent) (input : Input) : Prop :=
  input.packet.header = inbound pending.config pending.remote ∧ Profile input 18 ∧
    input.packet.segment.acknowledgment = pending.config.iss.add 1

def PassiveAccepted (pending : SynReceived) (input : Input) : Prop :=
  input.packet.header = pending.input.packet.header ∧ Profile input 16 ∧
    input.packet.segment.sequence = pending.input.packet.segment.sequence.add 1 ∧
    input.packet.segment.acknowledgment = pending.config.iss.add 1

structure ActiveEstablished (pending : SynSent) (input : Input) where
  seed : Endpoint.State
  derived : seed = activeSeed pending input
  valid : seed.Valid
  accepted : ActiveAccepted pending input
  output : Input
  outputGenerated : Output.emit seed.core [] = .ok output

structure PassiveEstablished (pending : SynReceived) (input : Input) where
  seed : Endpoint.State
  derived : seed = passiveSeed pending input
  valid : seed.Valid
  accepted : PassiveAccepted pending input

def activeOpen (config : Local) (remote : Socket) (policy : Bool) : Except Failure SynSent :=
  if valid : config.Valid then
    if policy then
      match generated : ControlOutput.emit (outbound config remote) config.iss (Seq.ofNat 0) 2 config.capacity with
      | .error _ => .error (.reject .encoding)
      | .ok output => .ok ⟨config, remote, output, valid, generated⟩
    else .error (.reject .policy)
  else .error (.reject .invalidConfig)

def listenSyn (config : Local) (input : Input) (policy : Bool) : Except Failure SynReceived :=
  if valid : config.Valid then
    if tuple : destination config input then
      if profile : Profile input 2 then
        if policy then
          match generated : ControlOutput.emit (Output.reverse input.packet.header) config.iss
              (input.packet.segment.sequence.add 1) 18 config.capacity with
          | .error _ => .error (.reject .encoding)
          | .ok output => .ok ⟨config, input, output, valid, tuple, profile, generated⟩
        else .error (.reject .policy)
      else .error (.unsupported (profileReason input))
    else .error (.reject .tuple)
  else .error (.reject .invalidConfig)

def synSentSynAck (pending : SynSent) (input : Input) (policy : Bool) :
    Except Failure (ActiveEstablished pending input) :=
  if tuple : input.packet.header = inbound pending.config pending.remote then
    if profile : Profile input 18 then
      if acknowledgment : input.packet.segment.acknowledgment = pending.config.iss.add 1 then
        if policy then
          match generated : Output.emit (activeSeed pending input).core [] with
          | .error _ => .error (.reject .encoding)
          | .ok output => .ok ⟨activeSeed pending input, rfl, activeSeed_valid pending input,
              ⟨tuple, profile, acknowledgment⟩, output, generated⟩
        else .error (.reject .policy)
      else .error (.unsupported .acknowledgment)
    else .error (.unsupported (profileReason input))
  else .error (.reject .tuple)

def synReceivedAck (pending : SynReceived) (input : Input) : Except Failure (PassiveEstablished pending input) :=
  if tuple : input.packet.header = pending.input.packet.header then
    if profile : Profile input 16 then
      if sequence : input.packet.segment.sequence = pending.input.packet.segment.sequence.add 1 then
        if acknowledgment : input.packet.segment.acknowledgment = pending.config.iss.add 1 then
          .ok ⟨passiveSeed pending input, rfl, passiveSeed_valid pending input,
            ⟨tuple, profile, sequence, acknowledgment⟩⟩
        else .error (.unsupported .acknowledgment)
      else .error (.unsupported .sequence)
    else .error (.unsupported (profileReason input))
  else .error (.reject .tuple)

theorem activeOpen_fields (config : Local) (remote : Socket) (policy : Bool) (pending : SynSent)
    (computed : activeOpen config remote policy = .ok pending) :
    pending.config = config ∧ pending.remote = remote ∧ policy = true := by
  unfold activeOpen at computed
  split at computed
  · split at computed
    · rename_i permitted
      split at computed
      · cases computed
      · cases computed
        exact ⟨rfl, rfl, permitted⟩
    · cases computed
  · cases computed

theorem listenSyn_fields (config : Local) (input : Input) (policy : Bool) (pending : SynReceived)
    (computed : listenSyn config input policy = .ok pending) :
    pending.config = config ∧ pending.input = input ∧ policy = true := by
  unfold listenSyn at computed
  split at computed
  · split at computed
    · split at computed
      · split at computed
        · rename_i permitted
          split at computed
          · cases computed
          · cases computed
            exact ⟨rfl, rfl, permitted⟩
        · cases computed
      · cases computed
    · cases computed
  · cases computed

theorem SynSent.output_fields (pending : SynSent) :
    pending.output.packet.header = outbound pending.config pending.remote ∧
      pending.output.packet.segment.sequence = pending.config.iss ∧
      pending.output.packet.segment.acknowledgment = Seq.ofNat 0 ∧
      pending.output.packet.segment.window.val = pending.config.capacity ∧
      pending.output.packet.segment.flags = 2 ∧ pending.output.packet.segment.options = [] ∧
      pending.output.packet.segment.payload = [] := by
  have fields := ControlOutput.emit_transport _ _ _ _ _ _ pending.generated
  exact ⟨fields.1, fields.2.1, fields.2.2.1, fields.2.2.2.1, fields.2.2.2.2.1,
    fields.2.2.2.2.2.1, fields.2.2.2.2.2.2.1⟩

theorem SynReceived.output_fields (pending : SynReceived) :
    pending.output.packet.header = Output.reverse pending.input.packet.header ∧
      pending.output.packet.segment.sequence = pending.config.iss ∧
      pending.output.packet.segment.acknowledgment = pending.input.packet.segment.sequence.add 1 ∧
      pending.output.packet.segment.window.val = pending.config.capacity ∧
      pending.output.packet.segment.flags = 18 ∧ pending.output.packet.segment.options = [] ∧
      pending.output.packet.segment.payload = [] := by
  have fields := ControlOutput.emit_transport _ _ _ _ _ _ pending.generated
  exact ⟨fields.1, fields.2.1, fields.2.2.1, fields.2.2.2.1, fields.2.2.2.2.1,
    fields.2.2.2.2.2.1, fields.2.2.2.2.2.2.1⟩

theorem SynSent.control_position (pending : SynSent) :
    Seq.distance pending.output.packet.segment.sequence (pending.config.iss.add 1) = 1 := by
  rw [pending.output_fields.2.1, Seq.distance_add]
  rfl

theorem SynReceived.control_position (pending : SynReceived) :
    Seq.distance pending.output.packet.segment.sequence (pending.config.iss.add 1) = 1 := by
  rw [pending.output_fields.2.1, Seq.distance_add]
  rfl

theorem activeSeed_empty (pending : SynSent) (input : Input) :
    (activeSeed pending input).pending = [] ∧ (activeSeed pending input).core.sent = [] ∧
      (activeSeed pending input).core.received = [] := ⟨rfl, rfl, rfl⟩

theorem passiveSeed_empty (pending : SynReceived) (input : Input) :
    (passiveSeed pending input).pending = [] ∧ (passiveSeed pending input).core.sent = [] ∧
      (passiveSeed pending input).core.received = [] := ⟨rfl, rfl, rfl⟩

theorem activeOpen_exists (config : Local) (remote : Socket) (valid : config.Valid) :
    ∃ pending, activeOpen config remote true = .ok pending := by
  obtain ⟨output, generated⟩ := ControlOutput.emit_exists (outbound config remote) config.iss (Seq.ofNat 0) 2
    config.capacity rfl (by decide) valid.1
  simp only [activeOpen, valid, dite_true, ite_true]
  split
  · rename_i reason failed
    simp only [failed] at generated
    cases generated
  · exact ⟨_, rfl⟩

theorem listenSyn_exists (config : Local) (input : Input) (valid : config.Valid)
    (tuple : destination config input) (profile : Profile input 2) :
    ∃ pending, listenSyn config input true = .ok pending := by
  obtain ⟨output, generated⟩ := ControlOutput.emit_exists (Output.reverse input.packet.header) config.iss
    (input.packet.segment.sequence.add 1) 18 config.capacity rfl (by decide) valid.1
  simp only [listenSyn, valid, dite_true, tuple, profile, ite_true]
  split
  · rename_i reason failed
    simp only [failed] at generated
    cases generated
  · exact ⟨_, rfl⟩

theorem synSentSynAck_exists (pending : SynSent) (input : Input) (accepted : ActiveAccepted pending input) :
    ∃ result, synSentSynAck pending input true = .ok result := by
  obtain ⟨tuple, profile, acknowledgment⟩ := accepted
  obtain ⟨output, generated⟩ := Output.emit_exists (activeSeed pending input).core []
    (activeSeed_valid pending input).1 (by decide)
  simp only [synSentSynAck, tuple, dite_true, profile, acknowledgment, ite_true]
  split
  · rename_i reason failed
    simp only [failed] at generated
    cases generated
  · exact ⟨_, rfl⟩

theorem synReceivedAck_exists (pending : SynReceived) (input : Input) (accepted : PassiveAccepted pending input) :
    ∃ result, synReceivedAck pending input = .ok result := by
  obtain ⟨tuple, profile, sequence, acknowledgment⟩ := accepted
  simp only [synReceivedAck, tuple, dite_true, profile, sequence, acknowledgment]
  exact ⟨_, rfl⟩

theorem ActiveEstablished.empty (result : ActiveEstablished pending input) :
    result.seed.pending = [] ∧ result.seed.core.sent = [] ∧ result.seed.core.received = [] := by
  rw [result.derived]
  exact activeSeed_empty pending input

theorem PassiveEstablished.empty (result : PassiveEstablished pending input) :
    result.seed.pending = [] ∧ result.seed.core.sent = [] ∧ result.seed.core.received = [] := by
  rw [result.derived]
  exact passiveSeed_empty pending input

theorem ActiveEstablished.cursors (result : ActiveEstablished pending input) :
    result.seed.core.receiveNext = input.packet.segment.sequence.add 1 ∧
      result.seed.core.sendUna = pending.config.iss.add 1 ∧ result.seed.core.sendNext = pending.config.iss.add 1 := by
  rw [result.derived]
  exact ⟨rfl, rfl, rfl⟩

theorem PassiveEstablished.cursors (result : PassiveEstablished pending input) :
    result.seed.core.receiveNext = pending.input.packet.segment.sequence.add 1 ∧
      result.seed.core.sendUna = pending.config.iss.add 1 ∧ result.seed.core.sendNext = pending.config.iss.add 1 := by
  rw [result.derived]
  exact ⟨rfl, rfl, rfl⟩

theorem ActiveEstablished.peer_fields (result : ActiveEstablished pending input) :
    result.seed.sendWindow = input.packet.segment.window.val ∧
      result.seed.sendWL1 = input.packet.segment.sequence ∧ result.seed.sendWL2 = input.packet.segment.acknowledgment ∧
      result.seed.effectiveMSS = min 536 (pending.config.ipSendLimit - 40) ∧ input.packet.segment.options = [] := by
  rw [result.derived]
  exact ⟨rfl, rfl, rfl, rfl, result.accepted.2.1.2.1⟩

theorem PassiveEstablished.peer_fields (result : PassiveEstablished pending input) :
    result.seed.sendWindow = input.packet.segment.window.val ∧
      result.seed.sendWL1 = input.packet.segment.sequence ∧ result.seed.sendWL2 = input.packet.segment.acknowledgment ∧
      result.seed.effectiveMSS = min 536 (pending.config.ipSendLimit - 40) ∧ pending.input.packet.segment.options = [] := by
  rw [result.derived]
  exact ⟨rfl, rfl, rfl, rfl, pending.profile.2.1⟩

theorem ActiveEstablished.acknowledges_syn (result : ActiveEstablished pending input) :
    input.packet.segment.acknowledgment = pending.output.packet.segment.sequence.add 1 := by
  rw [pending.output_fields.2.1]
  exact result.accepted.2.2

theorem PassiveEstablished.acknowledges_syn (result : PassiveEstablished pending input) :
    input.packet.segment.acknowledgment = pending.output.packet.segment.sequence.add 1 := by
  rw [pending.output_fields.2.1]
  exact result.accepted.2.2.2

end Netlib.Protocol.TCP.Handshake
