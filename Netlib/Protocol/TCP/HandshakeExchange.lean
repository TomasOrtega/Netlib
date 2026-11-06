import Netlib.Protocol.TCP.ApplicationTrace
import Netlib.Protocol.TCP.Handshake

/-!
# A checked startup history for two TCP endpoints

The selected history records actual control outputs and checked input bytes.
Its delivery paths preserve the transport fields used during startup.
Model output does not prove native transmission or peer identity.
-/

namespace Netlib.Protocol.TCP.ApplicationTrace

theorem BytePath.control_fields (path : BytePath source target) :
    target.packet.segment.acknowledgment = source.packet.segment.acknowledgment ∧
      target.packet.segment.flags = source.packet.segment.flags ∧
      target.packet.segment.window = source.packet.segment.window ∧
      target.packet.segment.options = source.packet.segment.options := by
  induction path with
  | @direct source target same =>
    have packet : target.packet = source.packet := by
      have decoded := target.checked
      rw [same, source.checked] at decoded
      exact (Except.ok.inj decoded).symm
    simp [packet]
  | @rewrite source target header ttl transport same =>
    have packet : target.packet = (source.rewrite header ttl transport).packet := by
      have decoded := target.checked
      rw [same, (source.rewrite header ttl transport).checked] at decoded
      exact (Except.ok.inj decoded).symm
    rw [packet]
    exact ⟨rfl, rfl, rfl, rfl⟩
  | trans first second ihFirst ihSecond =>
    exact ⟨ihSecond.1.trans ihFirst.1, ihSecond.2.1.trans ihFirst.2.1,
      ihSecond.2.2.1.trans ihFirst.2.2.1, ihSecond.2.2.2.trans ihFirst.2.2.2⟩

end Netlib.Protocol.TCP.ApplicationTrace

namespace Netlib.Protocol.TCP.HandshakeExchange

abbrev InputPacket := EstablishedReceive.Input

structure Rewrite where
  target : Packet.Header
  ttl : UInt8
  deriving Repr, BEq, DecidableEq

structure DeliverySpec where
  bytes : List UInt8
  rewrites : List Rewrite
  deriving Repr, BEq, DecidableEq

structure Routed (source : InputPacket) where
  input : InputPacket
  path : ApplicationTrace.BytePath source input

def route (source : InputPacket) : List Rewrite → Except String (Routed source)
  | [] => .ok ⟨source, .direct rfl⟩
  | rewrite :: rest => do
    if transport : rewrite.target.protocol = Packet.Protocol.tcp then
      let middle := source.rewrite rewrite.target rewrite.ttl transport
      let result ← route middle rest
      return ⟨result.input, .trans (.rewrite rewrite.target rewrite.ttl transport rfl) result.path⟩
    else throw "A startup byte path must use TCP tuples."

structure Delivery (source : InputPacket) (spec : DeliverySpec) where
  input : InputPacket
  bytes : input.bytes = spec.bytes
  routed : Routed source
  generated : route source spec.rewrites = .ok routed
  matched : input.bytes = routed.input.bytes

theorem Delivery.path (value : Delivery source spec) : ApplicationTrace.BytePath source value.input :=
  .trans value.routed.path (.direct value.matched)

def DeliverySpec.check (spec : DeliverySpec) (source : InputPacket) : Except String (Delivery source spec) :=
  match generated : route source spec.rewrites with
  | .error reason => .error reason
  | .ok routed =>
    match decoded : decodeIPv4 spec.bytes with
    | .error reason => .error reason
    | .ok packet =>
      if same : spec.bytes = routed.input.bytes then
        let received : InputPacket := ⟨spec.bytes, packet, decoded⟩
        .ok ⟨received, rfl, routed, generated, same⟩
      else .error "The received bytes must agree with the earlier output and its selected tuple path."


def Delivery.direct (source : InputPacket) : Delivery source ⟨source.bytes, []⟩ :=
  ⟨source, rfl, ⟨source, .direct rfl⟩, rfl, rfl⟩

def Delivery.rewritten (source : InputPacket) (target : Packet.Header) (ttl : UInt8)
    (transport : target.protocol = Packet.Protocol.tcp) :
    Delivery source ⟨(source.rewrite target ttl transport).bytes, [⟨target, ttl⟩]⟩ :=
  ⟨source.rewrite target ttl transport, rfl,
    ⟨source.rewrite target ttl transport, .trans (.rewrite target ttl transport rfl) (.direct rfl)⟩,
    by simp only [route, transport, dite_true, bind, Except.bind, pure]; rfl, rfl⟩


theorem Delivery.checked (value : Delivery source spec) : spec.check source = .ok value := by
  rcases value with ⟨⟨bytes, packet, checked⟩, original, routed, generated, matched⟩
  dsimp only at original matched
  subst bytes
  unfold DeliverySpec.check
  split
  · rename_i reason failed
    rw [generated] at failed
    cases failed
  · rename_i actual produced
    have same : actual = routed := Except.ok.inj (produced.symm.trans generated)
    subst actual
    split
    · rename_i reason failed
      rw [checked] at failed
      cases failed
    · rename_i actual decoded
      have same : actual = packet := Except.ok.inj (decoded.symm.trans checked)
      subst actual
      split
      · rfl
      · rename_i different
        exact False.elim (different matched)


structure Times where
  opened : Nat
  synReceived : Nat
  synAckReceived : Nat
  ackReceived : Nat
  deriving Repr, BEq, DecidableEq

def Times.Valid (times : Times) : Prop :=
  times.opened < times.synReceived ∧ times.synReceived < times.synAckReceived ∧
    times.synAckReceived < times.ackReceived

instance (times : Times) : Decidable times.Valid := by unfold Times.Valid; infer_instance

structure Input where
  active : Handshake.Local
  remote : Handshake.Socket
  passive : Handshake.Local
  openPolicy : Bool
  synPolicy : Bool
  synAckPolicy : Bool
  syn : DeliverySpec
  synAck : DeliverySpec
  ack : DeliverySpec
  times : Times

structure Complete (input : Input) where
  ordered : input.times.Valid
  activePending : Handshake.SynSent
  opened : Handshake.activeOpen input.active input.remote input.openPolicy = .ok activePending
  syn : Delivery activePending.output input.syn
  passivePending : Handshake.SynReceived
  listened : Handshake.listenSyn input.passive syn.input input.synPolicy = .ok passivePending
  synAck : Delivery passivePending.output input.synAck
  active : Handshake.ActiveEstablished activePending synAck.input
  activeComputed : Handshake.synSentSynAck activePending synAck.input input.synAckPolicy = .ok active
  ack : Delivery active.output input.ack
  passive : Handshake.PassiveEstablished passivePending ack.input
  passiveComputed : Handshake.synReceivedAck passivePending ack.input = .ok passive

private def successful (value : Except Handshake.Failure α) : Except String { result : α // value = .ok result } :=
  match value with
  | .error reason => .error reason.message
  | .ok result => .ok ⟨result, rfl⟩

def Input.check (input : Input) : Except String (Complete input) := do
  if ordered : input.times.Valid then
    let pending ← successful (Handshake.activeOpen input.active input.remote input.openPolicy)
    let syn ← input.syn.check pending.val.output
    let listener ← successful (Handshake.listenSyn input.passive syn.input input.synPolicy)
    let synAck ← input.synAck.check listener.val.output
    let active ← successful (Handshake.synSentSynAck pending.val synAck.input input.synAckPolicy)
    let ack ← input.ack.check active.val.output
    let passive ← successful (Handshake.synReceivedAck listener.val ack.input)
    return ⟨ordered, pending.val, pending.property, syn, listener.val, listener.property,
      synAck, active.val, active.property, ack, passive.val, passive.property⟩
  else throw "The startup event times must increase from OPEN to the final ACK receipt."


private theorem successful_of_ok (computed : value = Except.ok result) :
    successful value = .ok ⟨result, computed⟩ := by
  cases computed
  rfl

theorem Input.check_of_complete (value : Complete input) : input.check = .ok value := by
  unfold Input.check
  simp only [value.ordered, dite_true]
  rw [successful_of_ok value.opened]
  dsimp only [bind, Except.bind]
  rw [value.syn.checked]
  dsimp only [bind, Except.bind]
  rw [successful_of_ok value.listened]
  dsimp only [bind, Except.bind]
  rw [value.synAck.checked]
  dsimp only [bind, Except.bind]
  rw [successful_of_ok value.activeComputed]
  dsimp only [bind, Except.bind]
  rw [value.ack.checked]
  dsimp only [bind, Except.bind]
  rw [successful_of_ok value.passiveComputed]
  rfl

def Complete.activeSeed (value : Complete input) : Endpoint.State := value.active.seed

def Complete.passiveSeed (value : Complete input) : Endpoint.State := value.passive.seed

theorem Complete.valid (value : Complete input) : value.activeSeed.Valid ∧ value.passiveSeed.Valid :=
  ⟨value.active.valid, value.passive.valid⟩

theorem Complete.empty (value : Complete input) :
    value.activeSeed.pending = [] ∧ value.activeSeed.core.sent = [] ∧ value.activeSeed.core.received = [] ∧
      value.passiveSeed.pending = [] ∧ value.passiveSeed.core.sent = [] ∧ value.passiveSeed.core.received = [] := by
  simp only [Complete.activeSeed, Complete.passiveSeed, value.active.derived, value.passive.derived,
    Handshake.activeSeed, Handshake.passiveSeed, and_self]

theorem Complete.receiveStore_initial (value : Complete input) :
    value.activeSeed.receiveStore = ReceiveStore.initial ∧ value.passiveSeed.receiveStore = ReceiveStore.initial := by
  simp only [Complete.activeSeed, Complete.passiveSeed, value.active.derived, value.passive.derived,
    Handshake.activeSeed, Handshake.passiveSeed, and_self]

theorem Complete.empty_receiveStore (value : Complete input) :
    value.activeSeed.receiveStore.held = [] ∧ value.passiveSeed.receiveStore.held = [] := by
  simp only [value.receiveStore_initial.1, value.receiveStore_initial.2, ReceiveStore.initial, and_self]

theorem Complete.establishment_order (value : Complete input) :
    input.times.opened < input.times.synReceived ∧
      input.times.synReceived < input.times.synAckReceived ∧
      input.times.synAckReceived < input.times.ackReceived := value.ordered


theorem Complete.pending_fields (value : Complete input) :
    value.activePending.config = input.active ∧ value.activePending.remote = input.remote ∧
      value.passivePending.config = input.passive ∧ value.passivePending.input = value.syn.input := by
  have active := Handshake.activeOpen_fields _ _ _ _ value.opened
  have passive := Handshake.listenSyn_fields _ _ _ _ value.listened
  exact ⟨active.1, active.2.1, passive.1, passive.2.1⟩

theorem Complete.cursors (value : Complete input) :
    value.activeSeed.core.receiveNext = value.passiveSeed.core.sendNext ∧
      value.passiveSeed.core.receiveNext = value.activeSeed.core.sendNext := by
  have synFields := value.activePending.output_fields
  have synAckFields := value.passivePending.output_fields
  have synSequence := value.syn.path.fields.2.trans synFields.2.1
  have synAckSequence := value.synAck.path.fields.2.trans synAckFields.2.1
  simp only [Complete.activeSeed, Complete.passiveSeed, value.active.derived, value.passive.derived,
    Handshake.activeSeed, Handshake.passiveSeed, synAckSequence, value.pending_fields.2.2.2,
    synSequence, and_self]

theorem Complete.initial_sequences (value : Complete input) :
    value.activeSeed.core.sendUna = input.active.iss.add 1 ∧
      value.activeSeed.core.sendNext = input.active.iss.add 1 ∧
      value.activeSeed.core.receiveNext = input.passive.iss.add 1 ∧
      value.passiveSeed.core.sendUna = input.passive.iss.add 1 ∧
      value.passiveSeed.core.sendNext = input.passive.iss.add 1 ∧
      value.passiveSeed.core.receiveNext = input.active.iss.add 1 := by
  have activeSend : value.activeSeed.core.sendUna = input.active.iss.add 1 ∧
      value.activeSeed.core.sendNext = input.active.iss.add 1 := by
    simp only [Complete.activeSeed, value.active.derived, Handshake.activeSeed, value.pending_fields.1, and_self]
  have passiveSend : value.passiveSeed.core.sendUna = input.passive.iss.add 1 ∧
      value.passiveSeed.core.sendNext = input.passive.iss.add 1 := by
    simp only [Complete.passiveSeed, value.passive.derived, Handshake.passiveSeed,
      value.pending_fields.2.2.1, and_self]
  exact ⟨activeSend.1, activeSend.2, value.cursors.1.trans passiveSend.2,
    passiveSend.1, passiveSend.2, value.cursors.2.trans activeSend.2⟩

theorem Complete.window_history (value : Complete input) :
    value.activeSeed.sendWindow = value.synAck.input.packet.segment.window.val ∧
      value.activeSeed.sendWL1 = input.passive.iss ∧
      value.activeSeed.sendWL2 = input.active.iss.add 1 ∧
      value.passiveSeed.sendWindow = value.ack.input.packet.segment.window.val ∧
      value.passiveSeed.sendWL1 = input.active.iss.add 1 ∧
      value.passiveSeed.sendWL2 = input.passive.iss.add 1 := by
  have synAckFields := value.passivePending.output_fields
  have synAckSequence := value.synAck.path.fields.2.trans synAckFields.2.1
  have activeACK := value.active.accepted.2.2
  have passiveSequence := value.passive.accepted.2.2.1
  have passiveACK := value.passive.accepted.2.2.2
  have synFields := value.activePending.output_fields
  have synSequence := value.syn.path.fields.2.trans synFields.2.1
  simp only [Complete.activeSeed, Complete.passiveSeed, value.active.derived, value.passive.derived,
    Handshake.activeSeed, Handshake.passiveSeed, synAckSequence, activeACK, passiveSequence, passiveACK,
    value.pending_fields.1, value.pending_fields.2.2.1, value.pending_fields.2.2.2, synSequence, and_self]

theorem Complete.configuration (value : Complete input) :
    value.activeSeed.core.capacity = input.active.capacity ∧
      value.activeSeed.pendingLimit = input.active.pendingLimit ∧
      value.activeSeed.ipSendLimit = input.active.ipSendLimit ∧
      value.passiveSeed.core.capacity = input.passive.capacity ∧
      value.passiveSeed.pendingLimit = input.passive.pendingLimit ∧
      value.passiveSeed.ipSendLimit = input.passive.ipSendLimit := by
  simp only [Complete.activeSeed, Complete.passiveSeed, value.active.derived, value.passive.derived,
    Handshake.activeSeed, Handshake.passiveSeed, value.pending_fields.1, value.pending_fields.2.2.1, and_self]

theorem Complete.directional_mss (value : Complete input) :
    value.active.peerMSS = Handshake.receiveOffer input.passive ∧
      value.passivePending.peerMSS = Handshake.receiveOffer input.active ∧
      value.activeSeed.effectiveMSS = Handshake.effectiveMSS input.active (Handshake.receiveOffer input.passive) ∧
      value.passiveSeed.effectiveMSS = Handshake.effectiveMSS input.passive (Handshake.receiveOffer input.active) := by
  have activeSelected := value.active.peerSelected
  rw [value.synAck.path.control_fields.2.2.2, value.passivePending.output_fields.2.2.2.2.2.1,
    Handshake.options_selected] at activeSelected
  have activePeer : value.active.peerMSS = Handshake.receiveOffer input.passive := by
    rw [value.pending_fields.2.2.1] at activeSelected
    exact (Except.ok.inj activeSelected).symm
  have passiveSelected := value.passivePending.peerSelected
  rw [value.pending_fields.2.2.2, value.syn.path.control_fields.2.2.2,
    value.activePending.output_fields.2.2.2.2.2.1, Handshake.options_selected] at passiveSelected
  have passivePeer : value.passivePending.peerMSS = Handshake.receiveOffer input.active := by
    rw [value.pending_fields.1] at passiveSelected
    exact (Except.ok.inj passiveSelected).symm
  refine ⟨activePeer, passivePeer, ?_, ?_⟩
  · simp only [Complete.activeSeed, value.active.derived, Handshake.activeSeed, activePeer, value.pending_fields.1]
  · simp only [Complete.passiveSeed, value.passive.derived, Handshake.passiveSeed, passivePeer, value.pending_fields.2.2.1]

theorem Complete.own_receiveMSS (value : Complete input) :
    value.activeSeed.localReceiveMSS = Handshake.receiveOffer input.active ∧
      value.passiveSeed.localReceiveMSS = Handshake.receiveOffer input.passive := by
  simp only [Complete.activeSeed, Complete.passiveSeed, value.active.derived, value.passive.derived,
    Handshake.activeSeed, Handshake.passiveSeed, value.pending_fields.1, value.pending_fields.2.2.1, and_self]

theorem Complete.default_mss (value : Complete input)
    (active : input.active.receiveMSS = none) (passive : input.passive.receiveMSS = none) :
    value.syn.input.packet.segment.options = [] ∧ value.synAck.input.packet.segment.options = [] ∧
      value.activeSeed.effectiveMSS = min 536 (input.active.ipSendLimit - 40) ∧
      value.passiveSeed.effectiveMSS = min 536 (input.passive.ipSendLimit - 40) ∧
      value.activeSeed.effectiveMSS ≤ 536 ∧ value.passiveSeed.effectiveMSS ≤ 536 := by
  have synOptions := value.syn.path.control_fields.2.2.2.trans value.activePending.output_fields.2.2.2.2.2.1
  have synAckOptions := value.synAck.path.control_fields.2.2.2.trans value.passivePending.output_fields.2.2.2.2.2.1
  rw [value.pending_fields.1] at synOptions
  rw [value.pending_fields.2.2.1] at synAckOptions
  have mss := value.directional_mss
  simp only [Handshake.options, Handshake.advertised, active, passive, Option.map_none,
    ControlOutput.outputOptions] at synOptions synAckOptions
  simp only [Handshake.receiveOffer, active, passive, Handshake.effectiveMSS, MSS.effective_default] at mss
  exact ⟨synOptions, synAckOptions, mss.2.2.1, mss.2.2.2,
    by rw [mss.2.2.1]; exact Nat.min_le_left _ _, by rw [mss.2.2.2]; exact Nat.min_le_left _ _⟩


theorem Complete.peer_capacities (value : Complete input) :
    value.activeSeed.sendWindow = input.passive.capacity ∧
      value.passiveSeed.sendWindow = input.active.capacity := by
  have synAckFields := value.passivePending.output_fields
  have activeWindow : value.activeSeed.sendWindow = input.passive.capacity := by
    change value.active.seed.sendWindow = _
    rw [value.active.derived]
    change value.synAck.input.packet.segment.window.val = _
    rw [value.synAck.path.control_fields.2.2.1, synAckFields.2.2.2.1, value.pending_fields.2.2.1]
  have ackFields := Output.emit_transport _ _ _ value.active.outputGenerated
  have passiveWindow : value.passiveSeed.sendWindow = input.active.capacity := by
    change value.passive.seed.sendWindow = _
    rw [value.passive.derived]
    change value.ack.input.packet.segment.window.val = _
    rw [value.ack.path.control_fields.2.2.1, ackFields.2.2.2.1, value.active.derived]
    simp only [Handshake.activeSeed, EstablishedReceive.State.window, List.length_nil,
      Nat.sub_zero, value.pending_fields.1]
  exact ⟨activeWindow, passiveWindow⟩

structure QuietBoundary (value : Complete input) (activeSteps passiveSteps : List ApplicationTrace.Step) : Prop where
  active : ∀ step ∈ activeSteps, input.times.ackReceived < step.stamp
  passive : ∀ step ∈ passiveSteps, input.times.ackReceived < step.stamp

structure Environment (value : Complete input) (currentInstance : Nat → InputPacket → Prop) : Prop where
  syn : currentInstance input.times.synReceived value.syn.input
  synAck : currentInstance input.times.synAckReceived value.synAck.input
  ack : currentInstance input.times.ackReceived value.ack.input

structure ApplicationAssurance (value : Complete input) (currentInstance : Nat → InputPacket → Prop)
    (activeSteps passiveSteps : List ApplicationTrace.Step) : Prop where
  startupEnvironment : Environment value currentInstance
  quiet : QuietBoundary value activeSteps passiveSteps
  activeSupported : activeSteps.all ApplicationTrace.Step.supported = true
  passiveSupported : passiveSteps.all ApplicationTrace.Step.supported = true
  activeInputs : ∀ step ∈ activeSteps, ∀ packet, step.event = .receive packet → currentInstance step.stamp packet
  passiveInputs : ∀ step ∈ passiveSteps, ∀ packet, step.event = .receive packet → currentInstance step.stamp packet
  application : passiveSteps.flatMap ApplicationTrace.Step.readBytes <+: activeSteps.flatMap ApplicationTrace.Step.written ∧
    activeSteps.flatMap ApplicationTrace.Step.readBytes <+: passiveSteps.flatMap ApplicationTrace.Step.written

theorem Complete.application_prefix (value : Complete input)
    (activeChain : ApplicationTrace.Chain value.activeSeed activeSteps activeFinal)
    (passiveChain : ApplicationTrace.Chain value.passiveSeed passiveSteps passiveFinal)
    (forward : ApplicationTrace.DeliveryHistory activeSteps passiveSteps)
    (backward : ApplicationTrace.DeliveryHistory passiveSteps activeSteps)
    (activeEpoch : (activeSteps.flatMap ApplicationTrace.Step.emitted).length < Seq.halfSpace)
    (passiveEpoch : (passiveSteps.flatMap ApplicationTrace.Step.emitted).length < Seq.halfSpace) :
    passiveSteps.flatMap ApplicationTrace.Step.readBytes <+: activeSteps.flatMap ApplicationTrace.Step.written ∧
      activeSteps.flatMap ApplicationTrace.Step.readBytes <+: passiveSteps.flatMap ApplicationTrace.Step.written := by
  exact ApplicationTrace.paired_application_prefix activeChain passiveChain forward backward
    value.empty.1 value.empty.2.2.2.1 value.empty.2.1 value.empty.2.2.2.2.1
    value.empty.2.2.1 value.empty.2.2.2.2.2
    value.empty_receiveStore.1 value.empty_receiveStore.2
    value.cursors.1 value.cursors.2 activeEpoch passiveEpoch

theorem Complete.startup_to_application (value : Complete input)
    (activeChain : ApplicationTrace.Chain value.activeSeed activeSteps activeFinal)
    (passiveChain : ApplicationTrace.Chain value.passiveSeed passiveSteps passiveFinal)
    (forward : ApplicationTrace.DeliveryHistory activeSteps passiveSteps)
    (backward : ApplicationTrace.DeliveryHistory passiveSteps activeSteps)
    (activeEpoch : (activeSteps.flatMap ApplicationTrace.Step.emitted).length < Seq.halfSpace)
    (passiveEpoch : (passiveSteps.flatMap ApplicationTrace.Step.emitted).length < Seq.halfSpace)
    (environment : Environment value currentInstance)
    (quiet : QuietBoundary value activeSteps passiveSteps)
    (activeSupported : activeSteps.all ApplicationTrace.Step.supported = true)
    (passiveSupported : passiveSteps.all ApplicationTrace.Step.supported = true)
    (activeInputs : ∀ step ∈ activeSteps, ∀ packet,
      step.event = .receive packet → currentInstance step.stamp packet)
    (passiveInputs : ∀ step ∈ passiveSteps, ∀ packet,
      step.event = .receive packet → currentInstance step.stamp packet) :
    ApplicationAssurance value currentInstance activeSteps passiveSteps :=
  ⟨environment, quiet, activeSupported, passiveSupported, activeInputs, passiveInputs,
    value.application_prefix activeChain passiveChain forward backward activeEpoch passiveEpoch⟩

end Netlib.Protocol.TCP.HandshakeExchange
