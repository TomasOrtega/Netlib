import Netlib.Protocol.IPv4Reassembly
import Netlib.Protocol.IPv4Refragmentation
import Netlib.Protocol.MTUForwarding
import Netlib.Protocol.ICMPForwardingFacts

/-! Reassembly precedes UDP attachment; the completion event selects current policy. -/

namespace Netlib.Protocol.ReassemblyForwarding

open Packet

structure Source (reassembled : IPv4Reassembly.Output) where
  bytes : List UInt8
  packet : UDP.DecodedIPv4
  decoded : UDP.decodeIPv4 bytes = .ok packet
  same : packet.ip.packet = reassembled.packet

def source (reassembled : IPv4Reassembly.Output) : Except String (Source reassembled) := do
  let bytes ← IPv4.encode reassembled.packet
  match decoded : UDP.decodeIPv4 bytes with
  | .error error => throw error
  | .ok packet =>
    if same : packet.ip.packet = reassembled.packet then return ⟨bytes, packet, decoded, same⟩
    else throw "The decoded UDP packet must equal the completed IPv4 datagram."

theorem Source.valid (source : Source reassembled) : UDPRewrite.SourceValid source.packet :=
  UDPRewrite.sourceValid_of_encoded source.packet source.bytes
    (UDP.encodeIPv4_decodeIPv4 source.bytes source.packet source.decoded)

structure Pipeline where
  forwarding : MTUForwarding.Pipeline
  candidate : Nat → Header → NetfilterNAT.Entry

structure State where
  fragments : IPv4Reassembly.State := .initial
  conntrack : ConntrackLifecycle.State := .initial

def State.initial : State := ⟨.initial, .initial⟩

structure Input where
  now : Nat
  domain : IPv4Reassembly.Domain
  zone : Nat
  fragment : IPv4Fragment.Decoded

def input (pipeline : Pipeline) (before : ConntrackLifecycle.State) (zone : Nat)
    (source : Source reassembled) : WireForwarding.Input :=
  ⟨zone, source.packet, if (before.model.lookup zone source.packet.header).isNone then
    some (pipeline.candidate zone source.packet.header) else none⟩

def exceeds (reassembled : IPv4Reassembly.Output) (mtu : IPv4Fragmentation.MTU) : Bool :=
  reassembled.packet.dontFragment && decide (mtu.val < reassembled.packet.wireLength) &&
    (!reassembled.reassembled || decide (mtu.val < reassembled.maxSize))

def budget (reassembled : IPv4Reassembly.Output) (mtu : IPv4Fragmentation.MTU) :
    Except String IPv4Refragmentation.Budget :=
  let route : IPv4Refragmentation.Budget := ⟨mtu.val, by have := mtu.property; omega⟩
  if reassembled.reassembled then
    if bounded : 28 ≤ reassembled.maxSize ∧ reassembled.maxSize < 65536 then
      .ok (route.cap ⟨reassembled.maxSize, bounded⟩)
    else .error "The completed fragment-size maximum must lie between 28 and 65535."
  else .ok route

def allowsDF (reassembled : IPv4Reassembly.Output) (df : Bool) : Bool :=
  if reassembled.reassembled then !df || decide (reassembled.maxDFSize = reassembled.maxSize)
  else df == reassembled.packet.dontFragment

structure Outcome (packet : UDP.DecodedIPv4) where
  state : ConntrackLifecycle.State
  valid : state.Valid
  parent : Option (WireForwarding.Outcome packet)
  attachment : ConntrackLifecycle.Attachment
  afterDestination : Header
  afterSource : Option Header
  nextHop : Option String
  disposition : MTUForwarding.Disposition
  selectedMTU : Option IPv4Fragmentation.MTU
  sizeCap : Option IPv4Refragmentation.Budget
  output : Option (WireForwarding.Emission packet)

def ofParent (parent : WireForwarding.Outcome packet) (mtu : Option IPv4Fragmentation.MTU)
    (cap : Option IPv4Refragmentation.Budget) : Outcome packet :=
  ⟨parent.state, parent.valid, some parent, parent.attachment, parent.afterDestination, parent.afterSource,
    parent.nextHop, MTUForwarding.parentDisposition parent.disposition, mtu, cap, parent.output⟩

def blocked (wire : WireForwarding.Input) (prepared : ConntrackLifecycle.Prepared wire.lifecycle)
    (hop : String) (mtu : IPv4Fragmentation.MTU) : Outcome wire.packet :=
  ⟨prepared.state, prepared.valid, none, prepared.attachment, WireForwarding.destination wire prepared,
    none, some hop, .mtuExceeded, some mtu, none, none⟩

def process (pipeline : Pipeline) (reassembled : IPv4Reassembly.Output) (source : Source reassembled)
    (wire : WireForwarding.Input) (same : wire.packet = source.packet)
    (prepared : ConntrackLifecycle.Prepared wire.lifecycle) : Except String (Outcome wire.packet) := do
  let valid : UDPRewrite.SourceValid wire.packet := same ▸ source.valid
  match WireForwarding.route pipeline.forwarding.forwarding wire prepared with
  | none =>
    let parent ← (WireForwarding.process pipeline.forwarding.forwarding wire valid prepared).mapError (·.describe)
    return ofParent parent none none
  | some hop =>
    if wire.packet.ip.packet.ttl.toNat ≤ 1 then
      return ofParent (WireForwarding.expired pipeline.forwarding.forwarding wire prepared) none none
    else
      let mtu := pipeline.forwarding.mtu hop
      if exceeds reassembled mtu then return blocked wire prepared hop mtu
      else
        let cap ← budget reassembled mtu
        let parent ← (WireForwarding.finish pipeline.forwarding.forwarding wire valid prepared).mapError (·.describe)
        return ofParent parent (some mtu) (some cap)

structure Completed where
  reassembled : IPv4Reassembly.Output
  source : Source reassembled
  wire : WireForwarding.Input
  same : wire.packet = source.packet
  outcome : Outcome wire.packet

structure Result where
  state : State
  valid : state.conntrack.Valid
  reassembly : IPv4Reassembly.Result
  completed : Option Completed

def step (pipeline : Pipeline) (policy : IPv4Reassembly.Policy) (before : State) (arrival : Input) :
    Except String Result := do
  if valid : before.conntrack.check = true then
    let fragments ← (IPv4Reassembly.arrive policy before.fragments arrival.now arrival.domain arrival.fragment).mapError (·.describe)
    match fragments.output with
    | none =>
      return ⟨⟨fragments.state, before.conntrack⟩,
        (ConntrackLifecycle.State.check_correct _).mp valid, fragments, none⟩
    | some packet =>
      let decoded ← source packet
      let wire := input pipeline before.conntrack arrival.zone decoded
      let prepared ← (ConntrackLifecycle.prepare before.conntrack wire.lifecycle).mapError (·.describe)
      let outcome ← process pipeline packet decoded wire rfl prepared
      return ⟨⟨fragments.state, outcome.state⟩, outcome.valid, fragments, some ⟨packet, decoded, wire, rfl, outcome⟩⟩
  else throw "The ordinary conntrack table is invalid."

theorem step_valid (pipeline : Pipeline) (policy : IPv4Reassembly.Policy) (before : State) (arrival : Input)
    (result : Result) (_computed : step pipeline policy before arrival = .ok result) :
    result.state.conntrack.Valid := result.valid

theorem step_incomplete (pipeline : Pipeline) (policy : IPv4Reassembly.Policy) (before : State) (arrival : Input)
    (result : Result) (computed : step pipeline policy before arrival = .ok result)
    (fragments : IPv4Reassembly.Result)
    (arrived : IPv4Reassembly.arrive policy before.fragments arrival.now arrival.domain arrival.fragment = .ok fragments)
    (incomplete : fragments.output = none) :
    result.state.conntrack = before.conntrack ∧ result.completed = none ∧ result.state.fragments = fragments.state := by
  unfold step at computed
  split at computed
  · simp [arrived, incomplete, Except.mapError, bind, Except.bind, pure] at computed
    cases computed
    exact ⟨rfl, rfl, rfl⟩
  · cases computed

def Outcome.controlProjection (outcome : Outcome packet) : MTUForwarding.Outcome packet where
  state := outcome.state
  valid := outcome.valid
  parent := outcome.parent
  attachment := outcome.attachment
  afterDestination := outcome.afterDestination
  afterSource := outcome.afterSource
  nextHop := outcome.nextHop
  disposition := outcome.disposition
  selectedMTU := outcome.selectedMTU
  output := none

def Completed.control (completed : Completed) (context : ICMPForwarding.Context)
    (identification : InternetChecksum.Word) (linkGroup : Bool := false) : ICMPForwarding.Control completed.wire.packet :=
  ICMPForwarding.generate context ⟨completed.wire, linkGroup⟩ completed.outcome.controlProjection identification
    (completed.same ▸ completed.source.valid)

theorem source_payload (source : Source reassembled) :
    source.packet.ip.packet.payload = reassembled.packet.payload := congrArg (·.payload) source.same

theorem unfragmented_exceeds (packet : IPv4Reassembly.Output) (whole : packet.reassembled = false)
    (mtu : IPv4Fragmentation.MTU) :
    exceeds packet mtu = true ↔ packet.packet.dontFragment = true ∧ mtu.val < packet.packet.wireLength := by
  simp [exceeds, whole]

theorem reassembled_exceeds (packet : IPv4Reassembly.Output) (assembled : packet.reassembled = true)
    (mtu : IPv4Fragmentation.MTU) :
    exceeds packet mtu = true ↔ packet.packet.dontFragment = true ∧
      mtu.val < packet.packet.wireLength ∧ mtu.val < packet.maxSize := by
  simp [exceeds, assembled, and_assoc]

theorem budget_bounds (packet : IPv4Reassembly.Output) (mtu : IPv4Fragmentation.MTU)
    (cap : IPv4Refragmentation.Budget) (computed : budget packet mtu = .ok cap) :
    cap.val ≤ mtu.val ∧ (packet.reassembled = true → cap.val ≤ packet.maxSize) := by
  unfold budget at computed
  split at computed
  · split at computed
    · cases computed
      exact ⟨Nat.min_le_left _ _, fun _ => Nat.min_le_right _ _⟩
    · cases computed
  · rename_i whole
    cases computed
    exact ⟨Nat.le_refl _, fun assembled => False.elim (whole assembled)⟩

theorem process_output_cap (pipeline : Pipeline) (reassembled : IPv4Reassembly.Output)
    (source : Source reassembled) (wire : WireForwarding.Input) (same : wire.packet = source.packet)
    (prepared : ConntrackLifecycle.Prepared wire.lifecycle) (outcome : Outcome wire.packet)
    (computed : process pipeline reassembled source wire same prepared = .ok outcome)
    (cap : IPv4Refragmentation.Budget) (sized : outcome.sizeCap = some cap)
    (emission : WireForwarding.Emission wire.packet) (output : outcome.output = some emission) :
    ∃ (hop : String) (parent : WireForwarding.Outcome wire.packet),
      WireForwarding.route pipeline.forwarding.forwarding wire prepared = some hop ∧
      1 < wire.packet.ip.packet.ttl.toNat ∧ exceeds reassembled (pipeline.forwarding.mtu hop) = false ∧
      budget reassembled (pipeline.forwarding.mtu hop) = .ok cap ∧
      WireForwarding.finish pipeline.forwarding.forwarding wire (same ▸ source.valid) prepared = .ok parent ∧
      outcome = ofParent parent (some (pipeline.forwarding.mtu hop)) (some cap) ∧
      parent.output = some emission := by
  unfold process at computed
  split at computed
  · rename_i noRoute
    cases processed : WireForwarding.process pipeline.forwarding.forwarding wire (same ▸ source.valid) prepared with
    | error error => simp [processed, Except.mapError, bind, Except.bind] at computed
    | ok parent =>
      simp [processed, Except.mapError, bind, Except.bind, pure] at computed
      cases computed
      cases sized
  · rename_i hop routed
    split at computed
    · cases computed
      cases sized
    · rename_i live
      dsimp only at computed
      split at computed
      · cases computed
        cases sized
      · rename_i allowed
        cases selected : budget reassembled (pipeline.forwarding.mtu hop) with
        | error error => simp [selected, bind, Except.bind] at computed
        | ok actual =>
          cases processed : WireForwarding.finish pipeline.forwarding.forwarding wire (same ▸ source.valid) prepared with
          | error error => simp [selected, processed, Except.mapError, bind, Except.bind] at computed
          | ok parent =>
            simp [selected, processed, Except.mapError, bind, Except.bind, pure] at computed
            cases computed
            have equal : actual = cap := Option.some.inj sized
            subst actual
            exact ⟨hop, parent, routed, by omega, Bool.eq_false_iff.mpr allowed, selected, rfl, rfl, output⟩

theorem process_output_has_cap (pipeline : Pipeline) (reassembled : IPv4Reassembly.Output)
    (source : Source reassembled) (wire : WireForwarding.Input) (same : wire.packet = source.packet)
    (prepared : ConntrackLifecycle.Prepared wire.lifecycle) (outcome : Outcome wire.packet)
    (computed : process pipeline reassembled source wire same prepared = .ok outcome)
    (emission : WireForwarding.Emission wire.packet) (output : outcome.output = some emission) :
    ∃ cap, outcome.sizeCap = some cap := by
  unfold process at computed
  split at computed
  · rename_i noRoute
    cases processed : WireForwarding.process pipeline.forwarding.forwarding wire (same ▸ source.valid) prepared with
    | error error => simp [processed, Except.mapError, bind, Except.bind] at computed
    | ok parent =>
      simp [processed, Except.mapError, bind, Except.bind, pure] at computed
      cases computed
      obtain ⟨model, modelComputed, _, modelOutput, _⟩ :=
        WireForwarding.process_output pipeline.forwarding.forwarding wire (same ▸ source.valid)
          prepared parent processed emission output
      have filtered := ConntrackLifecycle.process_filters pipeline.forwarding.forwarding prepared
        model emission.target modelComputed modelOutput
      have routed : (WireForwarding.route pipeline.forwarding.forwarding wire prepared).isSome = true := by
        unfold WireForwarding.route WireForwarding.destination
        change (Routing.nextHop pipeline.forwarding.forwarding.routes
          ((ConntrackLifecycle.destinationStage prepared.attachment.entry prepared.attachment.direction).apply
            wire.lifecycle.packet).destination).isSome = true
        rw [← ConntrackLifecycle.process_destination pipeline.forwarding.forwarding prepared model modelComputed,
          filtered.2.2.2.1]
        exact filtered.2.2.2.2
      simp [noRoute] at routed
  · rename_i hop routed
    split at computed
    · cases computed
      cases output
    · dsimp only at computed
      split at computed
      · cases computed
        cases output
      · cases selected : budget reassembled (pipeline.forwarding.mtu hop) with
        | error error => simp [selected, bind, Except.bind] at computed
        | ok cap =>
          cases processed : WireForwarding.finish pipeline.forwarding.forwarding wire (same ▸ source.valid) prepared with
          | error error => simp [selected, processed, Except.mapError, bind, Except.bind] at computed
          | ok parent =>
            simp [selected, processed, Except.mapError, bind, Except.bind, pure] at computed
            cases computed
            exact ⟨cap, rfl⟩

end Netlib.Protocol.ReassemblyForwarding
