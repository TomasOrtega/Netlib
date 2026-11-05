import Netlib.Protocol.TCP.ControlOutput
import Netlib.Protocol.TCP.Endpoint
import Netlib.Protocol.TCP.MSS

/-!
# Checked ordinary TCP startup

This profile uses empty SYN and SYN,ACK packets with selected MSS options.
The final ACK has no options.
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
  receiveMSS : Option MSS.Advertisement := none
  deriving Repr, BEq, DecidableEq

def advertised (config : Local) : Option MSS.Value := config.receiveMSS.map (·.value)

def options (config : Local) : List UInt8 :=
  ControlOutput.outputOptions (advertised config)

def receiveOffer (config : Local) : MSS.Offer :=
  match config.receiveMSS with | none => .absent | some advertisement => advertisement.offer

theorem options_selected (config : Local) : MSS.readStartup (options config) = .ok (receiveOffer config) := by
  cases selected : config.receiveMSS with
  | none => simp [options, advertised, receiveOffer, selected, ControlOutput.outputOptions,
      MSS.readStartup, MSS.read, Options.maximumSegmentSizes, MSS.startupOptions]
  | some advertisement =>
    simpa [options, advertised, receiveOffer, selected, ControlOutput.outputOptions, MSS.Advertisement.offer]
      using MSS.readStartup_encode advertisement.value

def startupLength (config : Local) : Nat := 40 + (options config).length

def Local.Valid (config : Local) : Prop :=
  config.capacity ≤ 65535 ∧ config.pendingLimit ≤ 65535 ∧
    40 < config.ipSendLimit ∧ config.ipSendLimit ≤ 65535 ∧ startupLength config ≤ config.ipSendLimit

instance (config : Local) : Decidable config.Valid := by unfold Local.Valid; infer_instance

def outbound (config : Local) (remote : Socket) : Packet.Header :=
  ⟨config.socket.address, remote.address, Packet.Protocol.tcp, config.socket.port, remote.port⟩

def inbound (config : Local) (remote : Socket) : Packet.Header := Output.reverse (outbound config remote)

def destination (config : Local) (input : Input) : Prop :=
  input.packet.header.destination = config.socket.address ∧ input.packet.header.destinationPort = config.socket.port

instance (config : Local) (input : Input) : Decidable (destination config input) := by
  unfold destination
  infer_instance

def optionProfile (input : Input) (flags : UInt8) : Prop :=
  if flags = 16 then input.packet.segment.options = []
  else match MSS.readStartup input.packet.segment.options with | .ok _ => True | .error _ => False

def Profile (input : Input) (flags : UInt8) : Prop :=
  input.packet.segment.flags = flags ∧ optionProfile input flags ∧ input.packet.segment.payload = []

instance (input : Input) (flags : UInt8) : Decidable (optionProfile input flags) := by
  unfold optionProfile
  split
  · infer_instance
  · split <;> infer_instance

instance (input : Input) (flags : UInt8) : Decidable (Profile input flags) := by unfold Profile; infer_instance

theorem Profile.selection (profile : Profile input flags) (syn : flags ≠ 16) :
    ∃ peer, MSS.readStartup input.packet.segment.options = .ok peer := by
  cases selected : MSS.readStartup input.packet.segment.options with
  | error reason => simp [Profile, optionProfile, syn, selected] at profile
  | ok peer => exact ⟨peer, rfl⟩

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

def profileReason (input : Input) (flags : UInt8) : Unsupported :=
  if ¬optionProfile input flags then .options
  else if input.packet.segment.payload ≠ [] then .data
  else .flags

structure SynSent where
  config : Local
  remote : Socket
  output : Input
  localValid : config.Valid
  generated : ControlOutput.emitWithMSS (outbound config remote) config.iss (Seq.ofNat 0) 2 config.capacity (advertised config) = .ok output

structure SynReceived where
  config : Local
  input : Input
  output : Input
  localValid : config.Valid
  destination : Handshake.destination config input
  profile : Profile input 2
  peerMSS : MSS.Offer
  peerSelected : MSS.readStartup input.packet.segment.options = .ok peerMSS
  generated : ControlOutput.emitWithMSS (Output.reverse input.packet.header) config.iss
    (input.packet.segment.sequence.add 1) 18 config.capacity (advertised config) = .ok output

def effectiveMSS (config : Local) (peer : MSS.Offer) : Nat := MSS.effective peer config.ipSendLimit 0 0

def activeSeed (pending : SynSent) (input : Input) (peer : MSS.Offer) : Endpoint.State := {
  core := ⟨inbound pending.config pending.remote, input.packet.segment.sequence.add 1,
    pending.config.capacity, [], pending.config.iss.add 1, pending.config.iss.add 1, []⟩
  pending := []
  pendingLimit := pending.config.pendingLimit
  sendWindow := input.packet.segment.window.val
  sendWL1 := input.packet.segment.sequence
  sendWL2 := input.packet.segment.acknowledgment
  effectiveMSS := effectiveMSS pending.config peer
  ipSendLimit := pending.config.ipSendLimit }

def passiveSeed (pending : SynReceived) (input : Input) : Endpoint.State := {
  core := ⟨pending.input.packet.header, pending.input.packet.segment.sequence.add 1,
    pending.config.capacity, [], pending.config.iss.add 1, pending.config.iss.add 1, []⟩
  pending := []
  pendingLimit := pending.config.pendingLimit
  sendWindow := input.packet.segment.window.val
  sendWL1 := input.packet.segment.sequence
  sendWL2 := input.packet.segment.acknowledgment
  effectiveMSS := effectiveMSS pending.config pending.peerMSS
  ipSendLimit := pending.config.ipSendLimit }

theorem effectiveMSS_bounds (config : Local) (peer : MSS.Offer) (valid : config.Valid) :
    0 < effectiveMSS config peer ∧ effectiveMSS config peer ≤ peer.limit ∧
      40 + effectiveMSS config peer ≤ config.ipSendLimit :=
  MSS.effective_no_options_positive peer config.ipSendLimit valid.2.2.1

theorem activeSeed_valid (pending : SynSent) (input : Input) (peer : MSS.Offer) : (activeSeed pending input peer).Valid := by
  obtain ⟨capacity, storage, _, size, _⟩ := pending.localValid
  obtain ⟨positive, _, limit⟩ := effectiveMSS_bounds pending.config peer pending.localValid
  have window := input.packet.segment.window.isLt
  refine ⟨⟨rfl, by simp [activeSeed], capacity, by simp [activeSeed], ?_, ?_⟩,
    by simp [activeSeed], storage, by dsimp [activeSeed]; omega, positive, limit, size⟩
  · simp [activeSeed]
  · change 0 + EstablishedReceive.maxSendWindow < Seq.halfSpace
    decide

theorem passiveSeed_valid (pending : SynReceived) (input : Input) : (passiveSeed pending input).Valid := by
  obtain ⟨capacity, storage, _, size, _⟩ := pending.localValid
  obtain ⟨positive, _, limit⟩ := effectiveMSS_bounds pending.config pending.peerMSS pending.localValid
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
  peerMSS : MSS.Offer
  peerSelected : MSS.readStartup input.packet.segment.options = .ok peerMSS
  seed : Endpoint.State
  derived : seed = activeSeed pending input peerMSS
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
      match generated : ControlOutput.emitWithMSS (outbound config remote) config.iss (Seq.ofNat 0) 2 config.capacity (advertised config) with
      | .error _ => .error (.reject .encoding)
      | .ok output => .ok ⟨config, remote, output, valid, generated⟩
    else .error (.reject .policy)
  else .error (.reject .invalidConfig)

def listenSyn (config : Local) (input : Input) (policy : Bool) : Except Failure SynReceived :=
  if valid : config.Valid then
    if tuple : destination config input then
      if profile : Profile input 2 then
        match selected : MSS.readStartup input.packet.segment.options with
        | .error _ => .error (.unsupported .options)
        | .ok peer =>
          if policy then
            match generated : ControlOutput.emitWithMSS (Output.reverse input.packet.header) config.iss
                (input.packet.segment.sequence.add 1) 18 config.capacity (advertised config) with
            | .error _ => .error (.reject .encoding)
            | .ok output => .ok ⟨config, input, output, valid, tuple, profile, peer, selected, generated⟩
          else .error (.reject .policy)
      else .error (.unsupported (profileReason input 2))
    else .error (.reject .tuple)
  else .error (.reject .invalidConfig)

def synSentSynAck (pending : SynSent) (input : Input) (policy : Bool) :
    Except Failure (ActiveEstablished pending input) :=
  if tuple : input.packet.header = inbound pending.config pending.remote then
    if profile : Profile input 18 then
      match selected : MSS.readStartup input.packet.segment.options with
      | .error _ => .error (.unsupported .options)
      | .ok peer =>
        if acknowledgment : input.packet.segment.acknowledgment = pending.config.iss.add 1 then
          if policy then
            match generated : Output.emit (activeSeed pending input peer).core [] with
            | .error _ => .error (.reject .encoding)
            | .ok output => .ok ⟨peer, selected, activeSeed pending input peer, rfl, activeSeed_valid pending input peer,
                ⟨tuple, profile, acknowledgment⟩, output, generated⟩
          else .error (.reject .policy)
        else .error (.unsupported .acknowledgment)
    else .error (.unsupported (profileReason input 18))
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
    else .error (.unsupported (profileReason input 16))
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
  repeat' first
    | (solve | cases computed)
    | (solve | cases computed; exact ⟨rfl, rfl, by assumption⟩)
    | (split at computed)

theorem SynSent.output_fields (pending : SynSent) :
    pending.output.packet.header = outbound pending.config pending.remote ∧
      pending.output.packet.segment.sequence = pending.config.iss ∧
      pending.output.packet.segment.acknowledgment = Seq.ofNat 0 ∧
      pending.output.packet.segment.window.val = pending.config.capacity ∧
      pending.output.packet.segment.flags = 2 ∧ pending.output.packet.segment.options = options pending.config ∧
      pending.output.packet.segment.payload = [] := by
  have fields := ControlOutput.emitWithMSS_transport _ _ _ _ _ _ _ pending.generated
  exact ⟨fields.1, fields.2.1, fields.2.2.1, fields.2.2.2.1, fields.2.2.2.2.1,
    fields.2.2.2.2.2.1, fields.2.2.2.2.2.2.1⟩

theorem SynReceived.output_fields (pending : SynReceived) :
    pending.output.packet.header = Output.reverse pending.input.packet.header ∧
      pending.output.packet.segment.sequence = pending.config.iss ∧
      pending.output.packet.segment.acknowledgment = pending.input.packet.segment.sequence.add 1 ∧
      pending.output.packet.segment.window.val = pending.config.capacity ∧
      pending.output.packet.segment.flags = 18 ∧ pending.output.packet.segment.options = options pending.config ∧
      pending.output.packet.segment.payload = [] := by
  have fields := ControlOutput.emitWithMSS_transport _ _ _ _ _ _ _ pending.generated
  exact ⟨fields.1, fields.2.1, fields.2.2.1, fields.2.2.2.1, fields.2.2.2.2.1,
    fields.2.2.2.2.2.1, fields.2.2.2.2.2.2.1⟩

theorem SynSent.output_fits (pending : SynSent) : pending.output.bytes.length ≤ pending.config.ipSendLimit := by
  rw [ControlOutput.emitWithMSS_length _ _ _ _ _ _ _ pending.generated]
  exact pending.localValid.2.2.2.2

theorem SynReceived.output_fits (pending : SynReceived) : pending.output.bytes.length ≤ pending.config.ipSendLimit := by
  rw [ControlOutput.emitWithMSS_length _ _ _ _ _ _ _ pending.generated]
  exact pending.localValid.2.2.2.2

theorem SynSent.output_profile (pending : SynSent) : Profile pending.output 2 := by
  have fields := pending.output_fields
  refine ⟨fields.2.2.2.2.1, ?_, fields.2.2.2.2.2.2⟩
  simp only [optionProfile, show (2 : UInt8) ≠ 16 by decide, ite_false,
    fields.2.2.2.2.2.1, options_selected]

theorem SynReceived.output_profile (pending : SynReceived) : Profile pending.output 18 := by
  have fields := pending.output_fields
  refine ⟨fields.2.2.2.2.1, ?_, fields.2.2.2.2.2.2⟩
  simp only [optionProfile, show (18 : UInt8) ≠ 16 by decide, ite_false,
    fields.2.2.2.2.2.1, options_selected]

theorem SynSent.control_position (pending : SynSent) :
    Seq.distance pending.output.packet.segment.sequence (pending.config.iss.add 1) = 1 := by
  rw [pending.output_fields.2.1, Seq.distance_add]
  rfl

theorem SynReceived.control_position (pending : SynReceived) :
    Seq.distance pending.output.packet.segment.sequence (pending.config.iss.add 1) = 1 := by
  rw [pending.output_fields.2.1, Seq.distance_add]
  rfl

theorem activeSeed_empty (pending : SynSent) (input : Input) (peer : MSS.Offer) :
    (activeSeed pending input peer).pending = [] ∧ (activeSeed pending input peer).core.sent = [] ∧
      (activeSeed pending input peer).core.received = [] := ⟨rfl, rfl, rfl⟩

theorem passiveSeed_empty (pending : SynReceived) (input : Input) :
    (passiveSeed pending input).pending = [] ∧ (passiveSeed pending input).core.sent = [] ∧
      (passiveSeed pending input).core.received = [] := ⟨rfl, rfl, rfl⟩

theorem activeOpen_exists (config : Local) (remote : Socket) (valid : config.Valid) :
    ∃ pending, activeOpen config remote true = .ok pending := by
  obtain ⟨output, generated⟩ := ControlOutput.emitWithMSS_exists (outbound config remote) config.iss (Seq.ofNat 0) 2
    config.capacity (advertised config) rfl (by decide) valid.1 (by intro _; exact .inl rfl)
  simp only [activeOpen, valid, dite_true, ite_true]
  split
  · rename_i reason failed
    rw [failed] at generated
    cases generated
  · exact ⟨_, rfl⟩

theorem listenSyn_exists (config : Local) (input : Input) (valid : config.Valid)
    (tuple : destination config input) (profile : Profile input 2) :
    ∃ pending, listenSyn config input true = .ok pending := by
  obtain ⟨peer, selected⟩ := profile.selection (by decide)
  obtain ⟨output, generated⟩ := ControlOutput.emitWithMSS_exists (Output.reverse input.packet.header) config.iss
    (input.packet.segment.sequence.add 1) 18 config.capacity (advertised config) rfl (by decide) valid.1 (by intro _; exact .inr rfl)
  simp only [listenSyn, valid, dite_true, tuple, profile, ite_true]
  split
  · rename_i reason failed
    rw [failed] at selected
    cases selected
  · rename_i actual parsed
    have same := Except.ok.inj (parsed.symm.trans selected)
    subst actual
    split
    · rename_i reason failed
      rw [failed] at generated
      cases generated
    · exact ⟨_, rfl⟩

theorem synSentSynAck_exists (pending : SynSent) (input : Input) (accepted : ActiveAccepted pending input) :
    ∃ result, synSentSynAck pending input true = .ok result := by
  obtain ⟨tuple, profile, acknowledgment⟩ := accepted
  obtain ⟨peer, selected⟩ := profile.selection (by decide)
  obtain ⟨output, generated⟩ := Output.emit_exists (activeSeed pending input peer).core []
    (activeSeed_valid pending input peer).1 (by decide)
  simp only [synSentSynAck, tuple, dite_true, profile, acknowledgment, ite_true]
  split
  · rename_i reason failed
    rw [failed] at selected
    cases selected
  · rename_i actual parsed
    have same := Except.ok.inj (parsed.symm.trans selected)
    subst actual
    split
    · rename_i reason failed
      rw [failed] at generated
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
  exact activeSeed_empty pending input result.peerMSS

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
      result.seed.effectiveMSS = effectiveMSS pending.config result.peerMSS ∧
      MSS.readStartup input.packet.segment.options = .ok result.peerMSS := by
  rw [result.derived]
  exact ⟨rfl, rfl, rfl, rfl, result.peerSelected⟩

theorem PassiveEstablished.peer_fields (result : PassiveEstablished pending input) :
    result.seed.sendWindow = input.packet.segment.window.val ∧
      result.seed.sendWL1 = input.packet.segment.sequence ∧ result.seed.sendWL2 = input.packet.segment.acknowledgment ∧
      result.seed.effectiveMSS = effectiveMSS pending.config pending.peerMSS ∧
      MSS.readStartup pending.input.packet.segment.options = .ok pending.peerMSS := by
  rw [result.derived]
  exact ⟨rfl, rfl, rfl, rfl, pending.peerSelected⟩

theorem ActiveEstablished.acknowledges_syn (result : ActiveEstablished pending input) :
    input.packet.segment.acknowledgment = pending.output.packet.segment.sequence.add 1 := by
  rw [pending.output_fields.2.1]
  exact result.accepted.2.2

theorem PassiveEstablished.acknowledges_syn (result : PassiveEstablished pending input) :
    input.packet.segment.acknowledgment = pending.output.packet.segment.sequence.add 1 := by
  rw [pending.output_fields.2.1]
  exact result.accepted.2.2.2

end Netlib.Protocol.TCP.Handshake
