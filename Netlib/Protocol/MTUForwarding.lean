import Netlib.Protocol.WireForwarding
import Netlib.Protocol.IPv4Fragmentation

/-!
# MTU-aware tracked forwarding

The selected route supplies a validated IPv4 MTU. DF rejection follows destination
routing and TTL expiry, before filtering or confirmation. Successful NAT output is
fragmented after the single lifecycle execution. ICMP generation is outside this model.
-/

namespace Netlib.Protocol.MTUForwarding

open Packet
abbrev Input := WireForwarding.Input
abbrev MTU := IPv4Fragmentation.MTU
abbrev Error := WireForwarding.Error

structure Pipeline where
  forwarding : ConntrackLifecycle.Pipeline
  mtu : String → MTU

structure Emission (input : UDP.DecodedIPv4) where
  transit : WireForwarding.Emission input
  mtu : MTU
  fragments : IPv4Fragmentation.Certified transit.decoded.ip.packet mtu

def Emission.bytes (emission : Emission input) : List (List UInt8) := emission.fragments.bytes

theorem Emission.nonempty (emission : Emission input) : emission.fragments.fragments ≠ [] := emission.fragments.nonempty

theorem Emission.fits (emission : Emission input) (part : IPv4Fragment.Decoded) (member : part ∈ emission.fragments.fragments) :
    part.packet.wireLength ≤ emission.mtu.val := emission.fragments.fits part member

theorem Emission.payload (emission : Emission input) :
    emission.fragments.fragments.flatMap (·.packet.payload) = emission.transit.decoded.ip.packet.payload := emission.fragments.payload

theorem Emission.datagram_reassembled (emission : Emission input) :
    UDP.decode emission.transit.decoded.ip.packet.source emission.transit.decoded.ip.packet.destination
      (emission.fragments.fragments.flatMap (·.packet.payload)) = .ok emission.transit.decoded.datagram := by
  rw [emission.payload]
  exact (UDP.decodeIPv4_layers _ _ emission.transit.decoded_eq).2.2

theorem Emission.fragment_header (emission : Emission input) (part : IPv4Fragment.Decoded)
    (member : part ∈ emission.fragments.fragments) :
    part.packet.toPacket = { emission.transit.decoded.ip.packet with payload := part.packet.payload } := by
  rw [emission.fragments.generated] at member
  unfold IPv4Fragmentation.generatedFragments at member
  obtain ⟨piece, _, same⟩ := List.mem_map.mp member
  subst part
  rfl

theorem Emission.no_split_df (emission : Emission input) (df : input.ip.packet.dontFragment = true) :
    emission.fragments.fragments.length = 1 := by
  have outputDF : emission.transit.decoded.ip.packet.dontFragment = true := emission.transit.metadata.2.2.trans df
  rw [emission.fragments.no_split_df outputDF]
  rfl

theorem Emission.decoded (emission : Emission input) (part : IPv4Fragment.Decoded)
    (member : part ∈ emission.fragments.fragments) :
    IPv4Fragment.decode (IPv4Fragmentation.fragmentBytes part) = .ok part := emission.fragments.decoded part member

theorem Emission.reassembled (emission : Emission input) :
    IPv4Fragmentation.reassemble emission.fragments.fragments = .ok emission.transit.decoded.ip.packet :=
  emission.fragments.reassembled

theorem Emission.bytes_valid (emission : Emission input) (bytes : List UInt8) (member : bytes ∈ emission.bytes) :
    ∃ part ∈ emission.fragments.fragments, IPv4Fragment.decode bytes = .ok part ∧ bytes.length ≤ emission.mtu.val := by
  rw [Emission.bytes, emission.fragments.wire] at member
  obtain ⟨part, belongs, same⟩ := List.mem_map.mp member
  subst bytes
  refine ⟨part, belongs, emission.decoded part belongs, ?_⟩
  have length : (IPv4Fragmentation.fragmentBytes part).length = part.packet.wireLength := by
    simp [IPv4Fragmentation.fragmentBytes, IPv4Fragment.Packet.wireLength, IPv4.Packet.wireLength, Nat.add_comm]
  rw [length]
  exact emission.fits part belongs

def ofTransit (input : UDP.DecodedIPv4) (valid : UDPRewrite.SourceValid input) (mtu : MTU)
    (allowed : IPv4Fragmentation.Allowed input.ip.packet mtu) (transit : WireForwarding.Emission input) : Emission input :=
  ⟨transit, mtu, IPv4Fragmentation.fragment transit.decoded.ip.packet mtu
    (UDPRewrite.sourceValid_of_encoded transit.decoded transit.bytes transit.encoded).2.1 (by
      intro df
      have sourceDF : input.ip.packet.dontFragment = true := transit.metadata.2.2.symm.trans df
      change transit.rewritten.packet.ip.packet.wireLength ≤ mtu.val
      rw [transit.rewritten.length valid]
      exact allowed sourceDF)⟩

inductive Disposition where
  | forwarded
  | routeDrop
  | ttlExpired
  | mtuExceeded
  | forwardDrop
  | lateDrop
  deriving Repr, BEq, DecidableEq

def parentDisposition : WireForwarding.Disposition → Disposition
  | .forwarded => .forwarded
  | .routeDrop => .routeDrop
  | .ttlExpired => .ttlExpired
  | .forwardDrop => .forwardDrop
  | .lateDrop => .lateDrop

structure Outcome (input : UDP.DecodedIPv4) where
  state : ConntrackLifecycle.State
  valid : state.Valid
  parent : Option (WireForwarding.Outcome input)
  attachment : ConntrackLifecycle.Attachment
  afterDestination : Header
  afterSource : Option Header
  nextHop : Option String
  disposition : Disposition
  selectedMTU : Option MTU
  output : Option (Emission input)

def Outcome.mtuNeeded (outcome : Outcome input) : Option Nat :=
  if outcome.disposition = .mtuExceeded then outcome.selectedMTU.map (·.val) else none

def ofParent (input : UDP.DecodedIPv4) (valid : UDPRewrite.SourceValid input) (mtu : MTU)
    (allowed : IPv4Fragmentation.Allowed input.ip.packet mtu) (parent : WireForwarding.Outcome input) : Outcome input where
  state := parent.state
  valid := parent.valid
  parent := some parent
  attachment := parent.attachment
  afterDestination := parent.afterDestination
  afterSource := parent.afterSource
  nextHop := parent.nextHop
  disposition := parentDisposition parent.disposition
  selectedMTU := some mtu
  output := parent.output.map (ofTransit input valid mtu allowed)

def ofDroppedParent (parent : WireForwarding.Outcome input) (_dropped : parent.output = none) : Outcome input where
  state := parent.state
  valid := parent.valid
  parent := some parent
  attachment := parent.attachment
  afterDestination := parent.afterDestination
  afterSource := parent.afterSource
  nextHop := parent.nextHop
  disposition := parentDisposition parent.disposition
  selectedMTU := none
  output := none

def exceeded (_pipeline : Pipeline) (input : Input) (prepared : ConntrackLifecycle.Prepared input.lifecycle)
    (hop : String) (mtu : MTU) : Outcome input.packet where
  state := prepared.state
  valid := prepared.valid
  parent := none
  attachment := prepared.attachment
  afterDestination := WireForwarding.destination input prepared
  afterSource := none
  nextHop := some hop
  disposition := .mtuExceeded
  selectedMTU := some mtu
  output := none

private theorem early_dropped (pipeline : Pipeline) (input : Input) (valid : UDPRewrite.SourceValid input.packet)
    (prepared : ConntrackLifecycle.Prepared input.lifecycle) (parent : WireForwarding.Outcome input.packet)
    (processed : WireForwarding.process pipeline.forwarding input valid prepared = .ok parent)
    (early : WireForwarding.route pipeline.forwarding input prepared = none ∨ input.packet.ip.packet.ttl.toNat ≤ 1) :
    parent.output = none := by
  cases output : parent.output with
  | none => rfl
  | some emission =>
    obtain ⟨model, computed, _same, forwarded, live⟩ :=
      WireForwarding.process_output pipeline.forwarding input valid prepared parent processed emission output
    rcases early with noRoute | low
    · have filtered := ConntrackLifecycle.process_filters pipeline.forwarding prepared model emission.target computed forwarded
      have routed : (WireForwarding.route pipeline.forwarding input prepared).isSome = true := by
        unfold WireForwarding.route WireForwarding.destination
        change (Routing.nextHop pipeline.forwarding.routes
          ((ConntrackLifecycle.destinationStage prepared.attachment.entry prepared.attachment.direction).apply
            input.lifecycle.packet).destination).isSome = true
        rw [← ConntrackLifecycle.process_destination pipeline.forwarding prepared model computed, filtered.2.2.2.1]
        exact filtered.2.2.2.2
      simp [noRoute] at routed
    · omega

def early (pipeline : Pipeline) (input : Input) (valid : UDPRewrite.SourceValid input.packet)
    (prepared : ConntrackLifecycle.Prepared input.lifecycle)
    (beforeMTU : WireForwarding.route pipeline.forwarding input prepared = none ∨ input.packet.ip.packet.ttl.toNat ≤ 1) :
    Except ConntrackLifecycle.Error (Outcome input.packet) :=
  match processed : WireForwarding.process pipeline.forwarding input valid prepared with
  | .error error => .error error
  | .ok parent => .ok (ofDroppedParent parent (early_dropped pipeline input valid prepared parent processed beforeMTU))

def finish (pipeline : Pipeline) (input : Input) (valid : UDPRewrite.SourceValid input.packet)
    (prepared : ConntrackLifecycle.Prepared input.lifecycle) (mtu : MTU)
    (allowed : IPv4Fragmentation.Allowed input.packet.ip.packet mtu) : Except ConntrackLifecycle.Error (Outcome input.packet) :=
  match _processed : WireForwarding.finish pipeline.forwarding input valid prepared with
  | .error error => .error error
  | .ok parent => .ok (ofParent input.packet valid mtu allowed parent)

def process (pipeline : Pipeline) (input : Input) (valid : UDPRewrite.SourceValid input.packet)
    (prepared : ConntrackLifecycle.Prepared input.lifecycle) : Except ConntrackLifecycle.Error (Outcome input.packet) :=
  match routed : WireForwarding.route pipeline.forwarding input prepared with
  | none => early pipeline input valid prepared (Or.inl routed)
  | some hop =>
    if low : input.packet.ip.packet.ttl.toNat ≤ 1 then early pipeline input valid prepared (Or.inr low)
    else
      let mtu := pipeline.mtu hop
      if blocked : input.packet.ip.packet.dontFragment = true ∧ mtu.val < input.packet.ip.packet.wireLength then
        .ok (exceeded pipeline input prepared hop mtu)
      else finish pipeline input valid prepared mtu (by
        intro df
        have noOverflow : ¬mtu.val < input.packet.ip.packet.wireLength := fun bound => blocked ⟨df, bound⟩
        omega)

def step (pipeline : Pipeline) (state : ConntrackLifecycle.State) (input : Input) : Except Error (Outcome input.packet) := do
  match encoded : UDP.encodeIPv4 input.packet with
  | .error error => throw (.input error)
  | .ok bytes =>
    let prepared ← (ConntrackLifecycle.prepare state input.lifecycle).mapError WireForwarding.Error.lifecycle
    (process pipeline input (UDPRewrite.sourceValid_of_encoded input.packet bytes encoded) prepared).mapError WireForwarding.Error.lifecycle

theorem step_valid (pipeline : Pipeline) (state : ConntrackLifecycle.State) (input : Input)
    (outcome : Outcome input.packet) (_accepted : step pipeline state input = .ok outcome) : outcome.state.Valid := outcome.valid

private theorem ofParent_output (input : UDP.DecodedIPv4) (valid : UDPRewrite.SourceValid input) (mtu : MTU)
    (allowed : IPv4Fragmentation.Allowed input.ip.packet mtu) (parent : WireForwarding.Outcome input)
    (emission : Emission input) (forwarded : (ofParent input valid mtu allowed parent).output = some emission) :
    parent.output = some emission.transit ∧ emission.mtu = mtu := by
  cases found : parent.output with
  | none => simp [ofParent, found] at forwarded
  | some transit =>
    simp only [ofParent, found, Option.map_some, Option.some.injEq] at forwarded
    have sameTransit := congrArg Emission.transit forwarded
    have sameMTU := congrArg Emission.mtu forwarded
    exact ⟨congrArg some sameTransit, sameMTU.symm⟩

theorem finish_output (pipeline : Pipeline) (input : Input) (valid : UDPRewrite.SourceValid input.packet)
    (prepared : ConntrackLifecycle.Prepared input.lifecycle) (mtu : MTU)
    (allowed : IPv4Fragmentation.Allowed input.packet.ip.packet mtu) (outcome : Outcome input.packet)
    (accepted : finish pipeline input valid prepared mtu allowed = .ok outcome) (emission : Emission input.packet)
    (forwarded : outcome.output = some emission) :
    ∃ parent, WireForwarding.finish pipeline.forwarding input valid prepared = .ok parent ∧
      outcome = ofParent input.packet valid mtu allowed parent ∧ parent.output = some emission.transit ∧ emission.mtu = mtu := by
  unfold finish at accepted
  split at accepted
  · cases accepted
  · rename_i parent processed
    cases accepted
    exact ⟨parent, processed, rfl, ofParent_output input.packet valid mtu allowed parent emission forwarded⟩

theorem early_output_none (pipeline : Pipeline) (input : Input) (valid : UDPRewrite.SourceValid input.packet)
    (prepared : ConntrackLifecycle.Prepared input.lifecycle)
    (beforeMTU : WireForwarding.route pipeline.forwarding input prepared = none ∨ input.packet.ip.packet.ttl.toNat ≤ 1)
    (outcome : Outcome input.packet) (accepted : early pipeline input valid prepared beforeMTU = .ok outcome) :
    outcome.output = none := by
  unfold early at accepted
  split at accepted <;> cases accepted
  rfl

theorem process_output (pipeline : Pipeline) (input : Input) (valid : UDPRewrite.SourceValid input.packet)
    (prepared : ConntrackLifecycle.Prepared input.lifecycle) (outcome : Outcome input.packet)
    (accepted : process pipeline input valid prepared = .ok outcome) (emission : Emission input.packet)
    (forwarded : outcome.output = some emission) :
    ∃ (mtu : MTU) (allowed : IPv4Fragmentation.Allowed input.packet.ip.packet mtu)
      (parent : WireForwarding.Outcome input.packet),
      WireForwarding.finish pipeline.forwarding input valid prepared = .ok parent ∧
      outcome = ofParent input.packet valid mtu allowed parent ∧ parent.output = some emission.transit ∧
      emission.mtu = mtu ∧ 1 < input.packet.ip.packet.ttl.toNat := by
  unfold process at accepted
  split at accepted
  · have empty := early_output_none pipeline input valid prepared _ outcome accepted
    simp [empty] at forwarded
  · split at accepted
    · have empty := early_output_none pipeline input valid prepared _ outcome accepted
      simp [empty] at forwarded
    · dsimp only at accepted
      split at accepted
      · cases accepted
        cases forwarded
      · obtain ⟨parent, processed, same, output, selected⟩ := finish_output pipeline input valid prepared _ _ outcome accepted emission forwarded
        exact ⟨_, _, parent, processed, same, output, selected, by omega⟩

theorem step_prepared (pipeline : Pipeline) (state : ConntrackLifecycle.State) (input : Input)
    (outcome : Outcome input.packet) (accepted : step pipeline state input = .ok outcome) :
    ∃ (bytes : List UInt8) (_encoded : UDP.encodeIPv4 input.packet = .ok bytes)
      (valid : UDPRewrite.SourceValid input.packet) (prepared : ConntrackLifecycle.Prepared input.lifecycle),
      ConntrackLifecycle.prepare state input.lifecycle = .ok prepared ∧ process pipeline input valid prepared = .ok outcome := by
  unfold step at accepted
  split at accepted
  · cases accepted
  · rename_i bytes encoded
    cases found : ConntrackLifecycle.prepare state input.lifecycle with
    | error error => simp [found, Except.mapError, bind, Except.bind] at accepted
    | ok prepared =>
      refine ⟨bytes, encoded, UDPRewrite.sourceValid_of_encoded input.packet bytes encoded, prepared, rfl, ?_⟩
      cases computed : process pipeline input (UDPRewrite.sourceValid_of_encoded input.packet bytes encoded) prepared with
      | error error => simp [found, computed, Except.mapError, bind, Except.bind] at accepted
      | ok result =>
        simp [found, computed, Except.mapError, bind, Except.bind] at accepted
        cases accepted
        rfl

private theorem parent_step (pipeline : Pipeline) (state : ConntrackLifecycle.State) (input : Input)
    (bytes : List UInt8) (encoded : UDP.encodeIPv4 input.packet = .ok bytes) (valid : UDPRewrite.SourceValid input.packet)
    (prepared : ConntrackLifecycle.Prepared input.lifecycle) (attached : ConntrackLifecycle.prepare state input.lifecycle = .ok prepared)
    (parent : WireForwarding.Outcome input.packet)
    (processed : WireForwarding.process pipeline.forwarding input valid prepared = .ok parent) :
    WireForwarding.step pipeline.forwarding state input = .ok parent := by
  unfold WireForwarding.step
  split
  · rename_i error failed
    rw [encoded] at failed
    cases failed
  · simp [attached, processed, Except.mapError, bind, Except.bind]

theorem step_output (pipeline : Pipeline) (state : ConntrackLifecycle.State) (input : Input)
    (outcome : Outcome input.packet) (accepted : step pipeline state input = .ok outcome) (emission : Emission input.packet)
    (forwarded : outcome.output = some emission) :
    ∃ parent, WireForwarding.step pipeline.forwarding state input = .ok parent ∧ parent.output = some emission.transit ∧
      outcome.afterDestination = parent.afterDestination ∧ outcome.state = parent.state ∧ outcome.parent = some parent ∧
      outcome.selectedMTU = some emission.mtu ∧ 1 < input.packet.ip.packet.ttl.toNat := by
  obtain ⟨bytes, encoded, valid, prepared, attached, computed⟩ := step_prepared pipeline state input outcome accepted
  obtain ⟨mtu, allowed, parent, processed, same, output, selected, live⟩ :=
    process_output pipeline input valid prepared outcome computed emission forwarded
  have ordinary : WireForwarding.process pipeline.forwarding input valid prepared = .ok parent := by
    rw [WireForwarding.process_long pipeline.forwarding input valid prepared live]
    exact processed
  refine ⟨parent, parent_step pipeline state input bytes encoded valid prepared attached parent ordinary, output, ?_, ?_, ?_, ?_, live⟩
  · rw [same]; rfl
  · rw [same]; rfl
  · rw [same]; rfl
  · rw [same, selected]; rfl

theorem step_filters (pipeline : Pipeline) (state : ConntrackLifecycle.State) (input : Input)
    (outcome : Outcome input.packet) (accepted : step pipeline state input = .ok outcome) (emission : Emission input.packet)
    (forwarded : outcome.output = some emission) :
    StatefulACL.Policy.evaluate pipeline.forwarding.forwardDefault pipeline.forwarding.forward
        outcome.attachment.classification outcome.afterDestination = .permit ∧
      StatefulACL.Policy.evaluate pipeline.forwarding.lateDefault pipeline.forwarding.late
        outcome.attachment.classification emission.transit.target = .permit := by
  obtain ⟨bytes, encoded, valid, prepared, attached, computed⟩ := step_prepared pipeline state input outcome accepted
  obtain ⟨mtu, allowed, parent, processed, same, output, _, live⟩ := process_output pipeline input valid prepared outcome computed emission forwarded
  have ordinary : WireForwarding.process pipeline.forwarding input valid prepared = .ok parent := by
    rw [WireForwarding.process_long pipeline.forwarding input valid prepared live]
    exact processed
  have filtered := WireForwarding.step_filters pipeline.forwarding state input parent
    (parent_step pipeline state input bytes encoded valid prepared attached parent ordinary) emission.transit output
  rw [same]
  exact ⟨filtered.2.2.1, filtered.2.2.2.1⟩

theorem process_output_routeMTU (pipeline : Pipeline) (input : Input) (valid : UDPRewrite.SourceValid input.packet)
    (prepared : ConntrackLifecycle.Prepared input.lifecycle) (outcome : Outcome input.packet)
    (accepted : process pipeline input valid prepared = .ok outcome) (emission : Emission input.packet)
    (forwarded : outcome.output = some emission) :
    ∃ hop, outcome.nextHop = some hop ∧ emission.mtu = pipeline.mtu hop := by
  unfold process at accepted
  split at accepted
  · have empty := early_output_none pipeline input valid prepared _ outcome accepted
    simp [empty] at forwarded
  · rename_i hop routed
    split at accepted
    · have empty := early_output_none pipeline input valid prepared _ outcome accepted
      simp [empty] at forwarded
    · rename_i long
      dsimp only at accepted
      split at accepted
      · cases accepted; cases forwarded
      · obtain ⟨parent, processed, same, output, selected⟩ := finish_output pipeline input valid prepared _ _ outcome accepted emission forwarded
        have ordinary : WireForwarding.process pipeline.forwarding input valid prepared = .ok parent := by
          rw [WireForwarding.process_long pipeline.forwarding input valid prepared (by omega)]
          exact processed
        obtain ⟨model, computed, parentSame, modelOutput, _⟩ :=
          WireForwarding.process_output pipeline.forwarding input valid prepared parent ordinary emission.transit output
        have filtered := ConntrackLifecycle.process_filters pipeline.forwarding prepared model emission.transit.target computed modelOutput
        have next : parent.nextHop = WireForwarding.route pipeline.forwarding input prepared := by
          rw [parentSame]
          change model.nextHop = WireForwarding.route pipeline.forwarding input prepared
          unfold WireForwarding.route WireForwarding.destination
          change model.nextHop = Routing.nextHop pipeline.forwarding.routes
            ((ConntrackLifecycle.destinationStage prepared.attachment.entry prepared.attachment.direction).apply
              input.lifecycle.packet).destination
          rw [← ConntrackLifecycle.process_destination pipeline.forwarding prepared model computed, filtered.2.2.2.1]
        refine ⟨hop, ?_, selected⟩
        rw [same]
        exact next.trans routed

theorem step_output_routeMTU (pipeline : Pipeline) (state : ConntrackLifecycle.State) (input : Input)
    (outcome : Outcome input.packet) (accepted : step pipeline state input = .ok outcome) (emission : Emission input.packet)
    (forwarded : outcome.output = some emission) :
    ∃ hop, outcome.nextHop = some hop ∧ emission.mtu = pipeline.mtu hop := by
  obtain ⟨_, _, valid, prepared, _, computed⟩ := step_prepared pipeline state input outcome accepted
  exact process_output_routeMTU pipeline input valid prepared outcome computed emission forwarded

private theorem parentDisposition_not_exceeded (disposition : WireForwarding.Disposition) :
    parentDisposition disposition ≠ .mtuExceeded := by cases disposition <;> decide

private theorem early_not_exceeded (pipeline : Pipeline) (input : Input) (valid : UDPRewrite.SourceValid input.packet)
    (prepared : ConntrackLifecycle.Prepared input.lifecycle)
    (beforeMTU : WireForwarding.route pipeline.forwarding input prepared = none ∨ input.packet.ip.packet.ttl.toNat ≤ 1)
    (outcome : Outcome input.packet) (accepted : early pipeline input valid prepared beforeMTU = .ok outcome) :
    outcome.disposition ≠ .mtuExceeded := by
  unfold early at accepted
  split at accepted
  · cases accepted
  · cases accepted
    apply parentDisposition_not_exceeded

private theorem finish_not_exceeded (pipeline : Pipeline) (input : Input) (valid : UDPRewrite.SourceValid input.packet)
    (prepared : ConntrackLifecycle.Prepared input.lifecycle) (mtu : MTU)
    (allowed : IPv4Fragmentation.Allowed input.packet.ip.packet mtu) (outcome : Outcome input.packet)
    (accepted : finish pipeline input valid prepared mtu allowed = .ok outcome) : outcome.disposition ≠ .mtuExceeded := by
  unfold finish at accepted
  split at accepted
  · cases accepted
  · cases accepted
    apply parentDisposition_not_exceeded

theorem process_mtuExceeded (pipeline : Pipeline) (input : Input) (valid : UDPRewrite.SourceValid input.packet)
    (prepared : ConntrackLifecycle.Prepared input.lifecycle) (outcome : Outcome input.packet)
    (accepted : process pipeline input valid prepared = .ok outcome) (dropped : outcome.disposition = .mtuExceeded) :
    ∃ hop, WireForwarding.route pipeline.forwarding input prepared = some hop ∧
      1 < input.packet.ip.packet.ttl.toNat ∧ input.packet.ip.packet.dontFragment = true ∧
      (pipeline.mtu hop).val < input.packet.ip.packet.wireLength ∧
      outcome = exceeded pipeline input prepared hop (pipeline.mtu hop) := by
  unfold process at accepted
  split at accepted
  · exact False.elim (early_not_exceeded pipeline input valid prepared _ outcome accepted dropped)
  · rename_i hop routed
    split at accepted
    · exact False.elim (early_not_exceeded pipeline input valid prepared _ outcome accepted dropped)
    · dsimp only at accepted
      split at accepted
      · rename_i blocked
        cases accepted
        exact ⟨hop, routed, by omega, blocked.1, blocked.2, rfl⟩
      · exact False.elim (finish_not_exceeded pipeline input valid prepared _ _ outcome accepted dropped)

theorem step_mtuExceeded (pipeline : Pipeline) (state : ConntrackLifecycle.State) (input : Input)
    (outcome : Outcome input.packet) (accepted : step pipeline state input = .ok outcome)
    (dropped : outcome.disposition = .mtuExceeded) :
    ∃ (prepared : ConntrackLifecycle.Prepared input.lifecycle) (hop : String),
      ConntrackLifecycle.prepare state input.lifecycle = .ok prepared ∧
      WireForwarding.route pipeline.forwarding input prepared = some hop ∧ 1 < input.packet.ip.packet.ttl.toNat ∧
      input.packet.ip.packet.dontFragment = true ∧ (pipeline.mtu hop).val < input.packet.ip.packet.wireLength ∧
      outcome = exceeded pipeline input prepared hop (pipeline.mtu hop) := by
  obtain ⟨_, _, valid, prepared, attached, computed⟩ := step_prepared pipeline state input outcome accepted
  obtain ⟨hop, routed, live, df, large, same⟩ := process_mtuExceeded pipeline input valid prepared outcome computed dropped
  exact ⟨prepared, hop, attached, routed, live, df, large, same⟩

theorem mtuExceeded_fresh (pipeline : Pipeline) (state : ConntrackLifecycle.State) (input : Input)
    (outcome : Outcome input.packet) (accepted : step pipeline state input = .ok outcome)
    (dropped : outcome.disposition = .mtuExceeded) (fresh : outcome.attachment.fresh = true) :
    outcome.state = state ∧ outcome.output = none ∧ outcome.afterSource = none ∧ outcome.parent = none := by
  obtain ⟨prepared, hop, attached, _, _, _, _, same⟩ := step_mtuExceeded pipeline state input outcome accepted dropped
  rw [same] at fresh ⊢
  exact ⟨(ConntrackLifecycle.prepare_fresh state input.lifecycle prepared attached fresh).1, rfl, rfl, rfl⟩

theorem mtuExceeded_reply (pipeline : Pipeline) (state : ConntrackLifecycle.State) (input : Input)
    (outcome : Outcome input.packet) (accepted : step pipeline state input = .ok outcome)
    (dropped : outcome.disposition = .mtuExceeded) (reply : outcome.attachment.direction = .reply) :
    outcome.attachment.classification = .established ∧ outcome.attachment.fresh = false ∧
      outcome.state = state.markReply outcome.attachment.entry.flow ∧ outcome.output = none := by
  obtain ⟨prepared, hop, attached, _, _, _, _, same⟩ := step_mtuExceeded pipeline state input outcome accepted dropped
  rw [same] at reply ⊢
  obtain ⟨classification, fresh, changed⟩ := ConntrackLifecycle.prepare_reply state input.lifecycle prepared attached reply
  exact ⟨classification, fresh, changed, rfl⟩

theorem mtuExceeded_model (pipeline : Pipeline) (state : ConntrackLifecycle.State) (input : Input)
    (outcome : Outcome input.packet) (accepted : step pipeline state input = .ok outcome)
    (dropped : outcome.disposition = .mtuExceeded) : outcome.state.model = state.model := by
  obtain ⟨prepared, hop, attached, _, _, _, _, same⟩ := step_mtuExceeded pipeline state input outcome accepted dropped
  rw [same]
  exact ConntrackLifecycle.prepare_model state input.lifecycle prepared attached

theorem process_route_none (pipeline : Pipeline) (input : Input) (valid : UDPRewrite.SourceValid input.packet)
    (prepared : ConntrackLifecycle.Prepared input.lifecycle) (routed : WireForwarding.route pipeline.forwarding input prepared = none) :
    process pipeline input valid prepared = early pipeline input valid prepared (Or.inl routed) := by
  unfold process
  split
  · rfl
  · rename_i hop found
    rw [routed] at found
    cases found

theorem process_low_ttl (pipeline : Pipeline) (input : Input) (valid : UDPRewrite.SourceValid input.packet)
    (prepared : ConntrackLifecycle.Prepared input.lifecycle) (low : input.packet.ip.packet.ttl.toNat ≤ 1) :
    process pipeline input valid prepared = early pipeline input valid prepared (Or.inr low) := by
  unfold process
  split
  · rfl
  · rw [dite_eq_left low]

theorem early_completes (pipeline : Pipeline) (input : Input) (valid : UDPRewrite.SourceValid input.packet)
    (prepared : ConntrackLifecycle.Prepared input.lifecycle)
    (beforeMTU : WireForwarding.route pipeline.forwarding input prepared = none ∨ input.packet.ip.packet.ttl.toNat ≤ 1)
    (model : ConntrackLifecycle.Outcome) (processed : ConntrackLifecycle.process pipeline.forwarding prepared = .ok model) :
    ∃ outcome, early pipeline input valid prepared beforeMTU = .ok outcome := by
  obtain ⟨parent, computed⟩ := WireForwarding.process_completes pipeline.forwarding input valid prepared model processed
  unfold early
  split
  · rename_i error failed
    rw [computed] at failed
    cases failed
  · exact ⟨_, rfl⟩

theorem finish_completes (pipeline : Pipeline) (input : Input) (valid : UDPRewrite.SourceValid input.packet)
    (prepared : ConntrackLifecycle.Prepared input.lifecycle) (mtu : MTU)
    (allowed : IPv4Fragmentation.Allowed input.packet.ip.packet mtu)
    (model : ConntrackLifecycle.Outcome) (processed : ConntrackLifecycle.process pipeline.forwarding prepared = .ok model) :
    ∃ outcome, finish pipeline input valid prepared mtu allowed = .ok outcome := by
  obtain ⟨parent, computed⟩ := WireForwarding.finish_completes pipeline.forwarding input valid prepared model processed
  unfold finish
  split
  · rename_i error failed
    rw [computed] at failed
    cases failed
  · exact ⟨_, rfl⟩

theorem process_completes (pipeline : Pipeline) (input : Input) (valid : UDPRewrite.SourceValid input.packet)
    (prepared : ConntrackLifecycle.Prepared input.lifecycle)
    (model : ConntrackLifecycle.Outcome) (processed : ConntrackLifecycle.process pipeline.forwarding prepared = .ok model) :
    ∃ outcome, process pipeline input valid prepared = .ok outcome := by
  unfold process
  split
  · exact early_completes pipeline input valid prepared _ model processed
  · split
    · exact early_completes pipeline input valid prepared _ model processed
    · dsimp only
      split
      · exact ⟨_, rfl⟩
      · exact finish_completes pipeline input valid prepared _ _ model processed

theorem step_completes (pipeline : Pipeline) (state : ConntrackLifecycle.State) (input : Input)
    (bytes : List UInt8) (encoded : UDP.encodeIPv4 input.packet = .ok bytes)
    (prepared : ConntrackLifecycle.Prepared input.lifecycle) (attached : ConntrackLifecycle.prepare state input.lifecycle = .ok prepared)
    (model : ConntrackLifecycle.Outcome) (processed : ConntrackLifecycle.process pipeline.forwarding prepared = .ok model) :
    ∃ outcome, step pipeline state input = .ok outcome := by
  obtain ⟨outcome, completed⟩ := process_completes pipeline input
    (UDPRewrite.sourceValid_of_encoded input.packet bytes encoded) prepared model processed
  refine ⟨outcome, ?_⟩
  unfold step
  split
  · rename_i error failed
    rw [encoded] at failed
    cases failed
  · simp [attached, completed, Except.mapError, bind, Except.bind]

end Netlib.Protocol.MTUForwarding
