import Netlib.Protocol.ConntrackLifecycle
import Netlib.Protocol.TCP.ApplicationTrace
import Netlib.Protocol.WireSource

/-!
# Tracked TCP wire forwarding

Attachment and destination routing precede TTL expiry. A routed TTL-expired packet
retains reply observations but never reaches filtering, source NAT, or confirmation.
TCP admission remains a separate checked history.
This module does not prove Linux TCP tracker acceptance.
ICMP generation, MTU handling, and fragmentation are outside this profile.
-/

namespace Netlib.Protocol.TCP.WireForwarding

open Packet


abbrev Source := WireSource TCP.DecodedIPv4 TCP.decodeIPv4

def source (bytes : List UInt8) : Except String Source := WireSource.read TCP.decodeIPv4 bytes

theorem Source.encoded (value : Source) : TCP.encodeIPv4 value.packet = .ok value.bytes :=
  TCP.encodeIPv4_decodeIPv4 _ _ value.decoded

theorem Source.valid (value : Source) : TCPRewrite.SourceValid value.packet :=
  TCPRewrite.sourceValid_of_decoded _ _ value.decoded

def Source.asInput (value : Source) : EstablishedReceive.Input := ⟨value.bytes, value.packet, value.decoded⟩

def Source.ofInput (value : EstablishedReceive.Input) : Source := ⟨value.bytes, value.packet, value.checked⟩


@[simp] theorem Source.asInput_ofInput (value : EstablishedReceive.Input) : (Source.ofInput value).asInput = value := by
  cases value
  rfl

@[simp] theorem Source.ofInput_asInput (value : Source) : Source.ofInput value.asInput = value := by
  cases value
  rfl

structure Input where
  zone : Nat
  packet : TCP.DecodedIPv4
  candidate : Option NetfilterNAT.Entry := none

def Input.lifecycle (input : Input) : ConntrackLifecycle.Input := ⟨input.zone, input.packet.header, input.candidate⟩

def decrementTTL (packet : TCP.DecodedIPv4) : UInt8 := UInt8.ofNat (packet.ip.packet.ttl.toNat - 1)

theorem decrementTTL_exact (packet : TCP.DecodedIPv4) :
    (decrementTTL packet).toNat = packet.ip.packet.ttl.toNat - 1 := by
  have bounded := packet.ip.packet.ttl.toNat_lt
  simp only [decrementTTL, UInt8.toNat_ofNat']
  exact Nat.mod_eq_of_lt (by omega)

structure Emission (input : TCP.DecodedIPv4) where
  target : Header
  rewritten : TCPRewrite.Certified input target (decrementTTL input)

def Emission.decoded (emission : Emission input) : TCP.DecodedIPv4 := emission.rewritten.packet
def Emission.bytes (emission : Emission input) : List UInt8 := emission.rewritten.bytes

theorem Emission.transport (emission : Emission input) : emission.target.protocol = Packet.Protocol.tcp := by
  have valid := (TCPRewrite.sourceValid_of_encoded emission.rewritten.packet emission.bytes emission.rewritten.encoded).1.1
  rw [emission.rewritten.generated] at valid
  exact valid

theorem Emission.encoded (emission : Emission input) : TCP.encodeIPv4 emission.decoded = .ok emission.bytes :=
  emission.rewritten.encoded

theorem Emission.decoded_eq (emission : Emission input) : TCP.decodeIPv4 emission.bytes = .ok emission.decoded :=
  emission.rewritten.decoded

theorem Emission.header (emission : Emission input) : emission.decoded.header = emission.target :=
  emission.rewritten.header emission.transport

theorem Emission.payload (emission : Emission input) : emission.decoded.segment.payload = input.segment.payload :=
  emission.rewritten.payload

theorem Emission.ttl (emission : Emission input) :
    emission.decoded.ip.packet.ttl.toNat = input.ip.packet.ttl.toNat - 1 := by
  rw [show emission.decoded.ip.packet.ttl = decrementTTL input from emission.rewritten.ttl, decrementTTL_exact]

theorem Emission.metadata (emission : Emission input) :
    emission.decoded.ip.packet.tos = input.ip.packet.tos ∧
      emission.decoded.ip.packet.identification = input.ip.packet.identification ∧
      emission.decoded.ip.packet.dontFragment = input.ip.packet.dontFragment := emission.rewritten.metadata

theorem Emission.ipv4_checksum (emission : Emission input) :
    InternetChecksum.valid (IPv4.headerBytes emission.decoded.ip.packet emission.decoded.ip.checksum) = true :=
  emission.rewritten.ipv4_checksum

theorem Emission.tcp_checksum (emission : Emission input) :
    InternetChecksum.valid (TCP.pseudoHeader emission.decoded.ip.packet.source emission.decoded.ip.packet.destination
      emission.decoded.segment.lengthWord ++ emission.decoded.ip.packet.payload) = true := emission.rewritten.tcp_checksum

theorem Emission.control (emission : Emission input) :
    emission.decoded.segment.sequence = input.segment.sequence ∧
      emission.decoded.segment.acknowledgment = input.segment.acknowledgment ∧
      emission.decoded.segment.reserved = input.segment.reserved ∧
      emission.decoded.segment.flags = input.segment.flags ∧
      emission.decoded.segment.window = input.segment.window ∧
      emission.decoded.segment.urgentPointer = input.segment.urgentPointer ∧
      emission.decoded.segment.options = input.segment.options := emission.rewritten.transport


def Emission.asSource (emission : Emission input) : Source :=
  ⟨emission.bytes, emission.decoded, emission.decoded_eq⟩

def Emission.asInput (emission : Emission input) : EstablishedReceive.Input := emission.asSource.asInput

theorem Emission.bytePath (source : Source) (emission : Emission source.packet) :
    ApplicationTrace.BytePath source.asInput emission.asInput := by
  apply ApplicationTrace.BytePath.rewrite emission.target (decrementTTL source.packet) emission.transport
  change emission.rewritten.bytes = TCPRewrite.wireBytes source.packet emission.target (decrementTTL source.packet)
  have encoded := emission.rewritten.encoded
  rw [emission.rewritten.generated] at encoded
  exact Except.ok.inj (encoded.symm.trans (TCPRewrite.transformed_encoded _ _ _ source.valid emission.transport))

inductive Disposition where
  | forwarded
  | routeDrop
  | ttlExpired
  | forwardDrop
  | lateDrop
  deriving Repr, BEq, DecidableEq

def lifecycleDisposition : ConntrackLifecycle.Disposition → Disposition
  | .forwarded => .forwarded
  | .routeDrop => .routeDrop
  | .forwardDrop => .forwardDrop
  | .lateDrop => .lateDrop

structure Outcome (input : TCP.DecodedIPv4) where
  state : ConntrackLifecycle.State
  valid : state.Valid
  lifecycle : Option ConntrackLifecycle.Outcome
  attachment : ConntrackLifecycle.Attachment
  afterDestination : Header
  afterSource : Option Header
  nextHop : Option String
  disposition : Disposition
  output : Option (Emission input)

inductive Error where
  | input (reason : String)
  | lifecycle (reason : ConntrackLifecycle.Error)
  deriving Repr, BEq, DecidableEq

def Error.describe : Error → String
  | .input reason => reason
  | .lifecycle reason => reason.describe

def destination (input : Input) (prepared : ConntrackLifecycle.Prepared input.lifecycle) : Header :=
  (ConntrackLifecycle.destinationStage prepared.attachment.entry prepared.attachment.direction).apply input.packet.header

def route (pipeline : ConntrackLifecycle.Pipeline) (input : Input)
    (prepared : ConntrackLifecycle.Prepared input.lifecycle) : Option String :=
  Routing.nextHop pipeline.routes (destination input prepared).destination

private theorem output_tcp (pipeline : ConntrackLifecycle.Pipeline) (input : Input)
    (prepared : ConntrackLifecycle.Prepared input.lifecycle) (model : ConntrackLifecycle.Outcome)
    (processed : ConntrackLifecycle.process pipeline prepared = .ok model) (target : Header)
    (output : model.output = some target) : target.protocol = Packet.Protocol.tcp := by
  rw [ConntrackLifecycle.process_output pipeline prepared model target processed output]
  rw [prepared.attachment.entry.flow.output_protocol prepared.compatible.1]
  have attached := congrArg (fun key : Nat × Header => key.2.protocol) prepared.attached
  exact attached

def ofLifecycle (pipeline : ConntrackLifecycle.Pipeline) (input : Input) (valid : TCPRewrite.SourceValid input.packet)
    (prepared : ConntrackLifecycle.Prepared input.lifecycle) (model : ConntrackLifecycle.Outcome)
    (processed : ConntrackLifecycle.process pipeline prepared = .ok model) : Outcome input.packet where
  state := model.state
  valid := model.valid
  lifecycle := some model
  attachment := model.attachment
  afterDestination := model.afterDestination
  afterSource := model.afterSource
  nextHop := model.nextHop
  disposition := lifecycleDisposition model.disposition
  output := match found : model.output with
    | none => none
    | some target => some ⟨target, TCPRewrite.rewrite input.packet target (decrementTTL input.packet)
        valid (output_tcp pipeline input prepared model processed target found)⟩

def finish (pipeline : ConntrackLifecycle.Pipeline) (input : Input) (valid : TCPRewrite.SourceValid input.packet)
    (prepared : ConntrackLifecycle.Prepared input.lifecycle) : Except ConntrackLifecycle.Error (Outcome input.packet) :=
  match processed : ConntrackLifecycle.process pipeline prepared with
  | .error error => .error error
  | .ok model => .ok (ofLifecycle pipeline input valid prepared model processed)

def expired (pipeline : ConntrackLifecycle.Pipeline) (input : Input)
    (prepared : ConntrackLifecycle.Prepared input.lifecycle) : Outcome input.packet where
  state := prepared.state
  valid := prepared.valid
  lifecycle := none
  attachment := prepared.attachment
  afterDestination := destination input prepared
  afterSource := none
  nextHop := route pipeline input prepared
  disposition := .ttlExpired
  output := none

def process (pipeline : ConntrackLifecycle.Pipeline) (input : Input) (valid : TCPRewrite.SourceValid input.packet)
    (prepared : ConntrackLifecycle.Prepared input.lifecycle) : Except ConntrackLifecycle.Error (Outcome input.packet) :=
  match route pipeline input prepared with
  | none => finish pipeline input valid prepared
  | some _ =>
    if input.packet.ip.packet.ttl.toNat ≤ 1 then .ok (expired pipeline input prepared)
    else finish pipeline input valid prepared

def step (pipeline : ConntrackLifecycle.Pipeline) (state : ConntrackLifecycle.State) (input : Input) :
    Except Error (Outcome input.packet) := do
  match encoded : TCP.encodeIPv4 input.packet with
  | .error error => throw (.input error)
  | .ok bytes =>
    let prepared ← (ConntrackLifecycle.prepare state input.lifecycle).mapError Error.lifecycle
    (process pipeline input (TCPRewrite.sourceValid_of_encoded input.packet bytes encoded) prepared).mapError Error.lifecycle


theorem step_of_process (pipeline : ConntrackLifecycle.Pipeline) (state : ConntrackLifecycle.State) (input : Input)
    (bytes : List UInt8) (encoded : TCP.encodeIPv4 input.packet = .ok bytes)
    (valid : TCPRewrite.SourceValid input.packet) (prepared : ConntrackLifecycle.Prepared input.lifecycle)
    (attached : ConntrackLifecycle.prepare state input.lifecycle = .ok prepared) (outcome : Outcome input.packet)
    (computed : process pipeline input valid prepared = .ok outcome) : step pipeline state input = .ok outcome := by
  unfold step
  split
  · rename_i reason failed
    rw [encoded] at failed
    cases failed
  · simp only [attached, Except.mapError, bind, Except.bind]
    rw [computed]

theorem step_valid (pipeline : ConntrackLifecycle.Pipeline) (state : ConntrackLifecycle.State) (input : Input)
    (outcome : Outcome input.packet) (_accepted : step pipeline state input = .ok outcome) : outcome.state.Valid := outcome.valid

private theorem ofLifecycle_output (pipeline : ConntrackLifecycle.Pipeline) (input : Input)
    (valid : TCPRewrite.SourceValid input.packet) (prepared : ConntrackLifecycle.Prepared input.lifecycle)
    (model : ConntrackLifecycle.Outcome) (processed : ConntrackLifecycle.process pipeline prepared = .ok model)
    (emission : Emission input.packet)
    (output : (ofLifecycle pipeline input valid prepared model processed).output = some emission) :
    model.output = some emission.target := by
  unfold ofLifecycle at output
  split at output
  · cases output
  · cases output
    assumption

theorem finish_output (pipeline : ConntrackLifecycle.Pipeline) (input : Input) (valid : TCPRewrite.SourceValid input.packet)
    (prepared : ConntrackLifecycle.Prepared input.lifecycle) (outcome : Outcome input.packet)
    (accepted : finish pipeline input valid prepared = .ok outcome) (emission : Emission input.packet)
    (output : outcome.output = some emission) :
    ∃ model, ConntrackLifecycle.process pipeline prepared = .ok model ∧ outcome.lifecycle = some model ∧
      outcome.state = model.state ∧ model.output = some emission.target := by
  unfold finish at accepted
  split at accepted
  · cases accepted
  · rename_i model processed
    cases accepted
    exact ⟨model, processed, rfl, rfl, ofLifecycle_output pipeline input valid prepared model processed emission output⟩

theorem finish_realizes (pipeline : ConntrackLifecycle.Pipeline) (input : Input) (valid : TCPRewrite.SourceValid input.packet)
    (prepared : ConntrackLifecycle.Prepared input.lifecycle) (outcome : Outcome input.packet)
    (accepted : finish pipeline input valid prepared = .ok outcome) :
    ∃ (model : ConntrackLifecycle.Outcome) (processed : ConntrackLifecycle.process pipeline prepared = .ok model),
      outcome = ofLifecycle pipeline input valid prepared model processed := by
  unfold finish at accepted
  split at accepted
  · cases accepted
  · rename_i model processed
    cases accepted
    exact ⟨model, processed, rfl⟩


theorem finish_attachment (pipeline : ConntrackLifecycle.Pipeline) (input : Input)
    (valid : TCPRewrite.SourceValid input.packet) (prepared : ConntrackLifecycle.Prepared input.lifecycle)
    (outcome : Outcome input.packet) (accepted : finish pipeline input valid prepared = .ok outcome) :
    outcome.attachment = prepared.attachment := by
  obtain ⟨model, processed, same⟩ := finish_realizes pipeline input valid prepared outcome accepted
  rw [same]
  exact ConntrackLifecycle.process_attachment pipeline prepared model processed

theorem process_attachment (pipeline : ConntrackLifecycle.Pipeline) (input : Input)
    (valid : TCPRewrite.SourceValid input.packet) (prepared : ConntrackLifecycle.Prepared input.lifecycle)
    (outcome : Outcome input.packet) (accepted : process pipeline input valid prepared = .ok outcome) :
    outcome.attachment = prepared.attachment := by
  unfold process at accepted
  split at accepted
  · exact finish_attachment pipeline input valid prepared outcome accepted
  · split at accepted
    · cases accepted
      rfl
    · exact finish_attachment pipeline input valid prepared outcome accepted

theorem finish_routed (pipeline : ConntrackLifecycle.Pipeline) (input : Input) (valid : TCPRewrite.SourceValid input.packet)
    (prepared : ConntrackLifecycle.Prepared input.lifecycle) (outcome : Outcome input.packet)
    (accepted : finish pipeline input valid prepared = .ok outcome) (emission : Emission input.packet)
    (output : outcome.output = some emission) : (route pipeline input prepared).isSome = true := by
  obtain ⟨model, processed, _, _, modelOutput⟩ := finish_output pipeline input valid prepared outcome accepted emission output
  have filtered := ConntrackLifecycle.process_filters pipeline prepared model emission.target processed modelOutput
  unfold route destination
  change (Routing.nextHop pipeline.routes
    ((ConntrackLifecycle.destinationStage prepared.attachment.entry prepared.attachment.direction).apply
      input.lifecycle.packet).destination).isSome = true
  rw [← ConntrackLifecycle.process_destination pipeline prepared model processed, filtered.2.2.2.1]
  exact filtered.2.2.2.2

theorem process_output (pipeline : ConntrackLifecycle.Pipeline) (input : Input) (valid : TCPRewrite.SourceValid input.packet)
    (prepared : ConntrackLifecycle.Prepared input.lifecycle) (outcome : Outcome input.packet)
    (accepted : process pipeline input valid prepared = .ok outcome) (emission : Emission input.packet)
    (output : outcome.output = some emission) :
    ∃ (model : ConntrackLifecycle.Outcome) (processed : ConntrackLifecycle.process pipeline prepared = .ok model),
      outcome = ofLifecycle pipeline input valid prepared model processed ∧ model.output = some emission.target ∧
        1 < input.packet.ip.packet.ttl.toNat := by
  unfold process at accepted
  split at accepted
  · rename_i noRoute
    have routed := finish_routed pipeline input valid prepared outcome accepted emission output
    simp [noRoute] at routed
  · split at accepted
    · cases accepted
      cases output
    · obtain ⟨model, processed, same⟩ := finish_realizes pipeline input valid prepared outcome accepted
      refine ⟨model, processed, same, ?_, by omega⟩
      rw [same] at output
      exact ofLifecycle_output pipeline input valid prepared model processed emission output

theorem step_prepared (pipeline : ConntrackLifecycle.Pipeline) (state : ConntrackLifecycle.State) (input : Input)
    (outcome : Outcome input.packet) (accepted : step pipeline state input = .ok outcome) :
    ∃ (valid : TCPRewrite.SourceValid input.packet) (prepared : ConntrackLifecycle.Prepared input.lifecycle),
      ConntrackLifecycle.prepare state input.lifecycle = .ok prepared ∧ process pipeline input valid prepared = .ok outcome := by
  unfold step at accepted
  split at accepted
  · cases accepted
  · rename_i bytes encoded
    cases preparedFound : ConntrackLifecycle.prepare state input.lifecycle with
    | error error => simp [preparedFound, Except.mapError, bind, Except.bind] at accepted
    | ok prepared =>
      refine ⟨TCPRewrite.sourceValid_of_encoded input.packet bytes encoded, prepared, rfl, ?_⟩
      cases processed : process pipeline input (TCPRewrite.sourceValid_of_encoded input.packet bytes encoded) prepared with
      | error error => simp [preparedFound, processed, Except.mapError, bind, Except.bind] at accepted
      | ok value =>
        simp [preparedFound, processed, Except.mapError, bind, Except.bind] at accepted
        cases accepted
        rfl

theorem step_output_prepared (pipeline : ConntrackLifecycle.Pipeline) (state : ConntrackLifecycle.State) (input : Input)
    (outcome : Outcome input.packet) (accepted : step pipeline state input = .ok outcome) (emission : Emission input.packet)
    (output : outcome.output = some emission) :
    ∃ (valid : TCPRewrite.SourceValid input.packet) (prepared : ConntrackLifecycle.Prepared input.lifecycle)
      (model : ConntrackLifecycle.Outcome) (processed : ConntrackLifecycle.process pipeline prepared = .ok model),
      ConntrackLifecycle.prepare state input.lifecycle = .ok prepared ∧
      outcome = ofLifecycle pipeline input valid prepared model processed ∧ model.output = some emission.target ∧
        1 < input.packet.ip.packet.ttl.toNat := by
  obtain ⟨valid, prepared, preparedFound, computed⟩ := step_prepared pipeline state input outcome accepted
  obtain ⟨model, processed, same, forwarded, ttl⟩ := process_output pipeline input valid prepared outcome computed emission output
  exact ⟨valid, prepared, model, processed, preparedFound, same, forwarded, ttl⟩

theorem step_output (pipeline : ConntrackLifecycle.Pipeline) (state : ConntrackLifecycle.State) (input : Input)
    (outcome : Outcome input.packet) (accepted : step pipeline state input = .ok outcome) (emission : Emission input.packet)
    (output : outcome.output = some emission) :
    ∃ model, ConntrackLifecycle.step pipeline state input.lifecycle = .ok model ∧ model.output = some emission.target ∧
      outcome.afterDestination = model.afterDestination ∧ outcome.state = model.state ∧ outcome.lifecycle = some model ∧
        1 < input.packet.ip.packet.ttl.toNat := by
  obtain ⟨valid, prepared, model, processed, preparedFound, same, forwarded, ttl⟩ :=
    step_output_prepared pipeline state input outcome accepted emission output
  refine ⟨model, ?_, forwarded, ?_, ?_, ?_, ttl⟩
  · simp [ConntrackLifecycle.step, preparedFound, processed, bind, Except.bind]
  · rw [same]; rfl
  · rw [same]; rfl
  · rw [same]; rfl

theorem step_filters (pipeline : ConntrackLifecycle.Pipeline) (state : ConntrackLifecycle.State) (input : Input)
    (outcome : Outcome input.packet) (accepted : step pipeline state input = .ok outcome) (emission : Emission input.packet)
    (output : outcome.output = some emission) :
    outcome.disposition = .forwarded ∧ 1 < input.packet.ip.packet.ttl.toNat ∧
      StatefulACL.Policy.evaluate pipeline.forwardDefault pipeline.forward outcome.attachment.classification
        outcome.afterDestination = .permit ∧
      StatefulACL.Policy.evaluate pipeline.lateDefault pipeline.late outcome.attachment.classification emission.target = .permit ∧
      Routing.nextHop pipeline.routes outcome.afterDestination.destination = outcome.nextHop ∧ outcome.nextHop.isSome = true := by
  obtain ⟨valid, prepared, model, processed, _, same, forwarded, ttl⟩ := step_output_prepared pipeline state input outcome accepted emission output
  have filtered := ConntrackLifecycle.process_filters pipeline prepared model emission.target processed forwarded
  rw [← ConntrackLifecycle.process_attachment pipeline prepared model processed] at filtered
  rw [same]
  exact ⟨congrArg lifecycleDisposition filtered.1, ttl, filtered.2⟩


theorem step_nat (pipeline : ConntrackLifecycle.Pipeline) (state : ConntrackLifecycle.State) (input : Input)
    (outcome : Outcome input.packet) (accepted : step pipeline state input = .ok outcome)
    (emission : Emission input.packet) (output : outcome.output = some emission) :
    emission.target = outcome.attachment.entry.flow.output outcome.attachment.direction ∧
      outcome.attachment.entry.flow.key outcome.attachment.direction = (input.zone, input.packet.header) ∧
      outcome.attachment.entry.Compatible ∧
      outcome.afterDestination =
        (ConntrackLifecycle.destinationStage outcome.attachment.entry outcome.attachment.direction).apply input.packet.header := by
  obtain ⟨valid, prepared, model, processed, _, same, forwarded, _⟩ :=
    step_output_prepared pipeline state input outcome accepted emission output
  rw [same]
  dsimp only [ofLifecycle]
  have attachment := ConntrackLifecycle.process_attachment pipeline prepared model processed
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [attachment]
    exact ConntrackLifecycle.process_output pipeline prepared model emission.target processed forwarded
  · rw [attachment]
    exact prepared.attached
  · rw [attachment]
    exact prepared.compatible
  · rw [attachment]
    exact ConntrackLifecycle.process_destination pipeline prepared model processed

structure Forwarded (pipeline : ConntrackLifecycle.Pipeline) (state : ConntrackLifecycle.State)
    (source : Source) (zone : Nat) (candidate : Option NetfilterNAT.Entry) where
  outcome : Outcome source.packet
  computed : step pipeline state ⟨zone, source.packet, candidate⟩ = .ok outcome
  emission : Emission source.packet
  emitted : outcome.output = some emission

theorem Forwarded.bytePath {source : Source} (value : Forwarded pipeline state source zone candidate) :
    ApplicationTrace.BytePath source.asInput value.emission.asInput := value.emission.bytePath source

theorem Forwarded.facts {source : Source} (value : Forwarded pipeline state source zone candidate) :
    value.emission.target = value.outcome.attachment.entry.flow.output value.outcome.attachment.direction ∧
      value.outcome.attachment.entry.flow.key value.outcome.attachment.direction = (zone, source.packet.header) ∧
      value.outcome.attachment.entry.Compatible ∧
      value.outcome.disposition = .forwarded ∧ 1 < source.packet.ip.packet.ttl.toNat ∧
      StatefulACL.Policy.evaluate pipeline.forwardDefault pipeline.forward value.outcome.attachment.classification
        value.outcome.afterDestination = .permit ∧
      StatefulACL.Policy.evaluate pipeline.lateDefault pipeline.late value.outcome.attachment.classification
        value.emission.target = .permit ∧
      Routing.nextHop pipeline.routes value.outcome.afterDestination.destination = value.outcome.nextHop ∧
      value.outcome.nextHop.isSome = true := by
  have nat := step_nat pipeline state ⟨zone, source.packet, candidate⟩ value.outcome value.computed value.emission value.emitted
  exact ⟨nat.1, nat.2.1, nat.2.2.1, step_filters _ _ _ _ value.computed _ value.emitted⟩

theorem process_expired (pipeline : ConntrackLifecycle.Pipeline) (input : Input) (valid : TCPRewrite.SourceValid input.packet)
    (prepared : ConntrackLifecycle.Prepared input.lifecycle) (hop : String) (routed : route pipeline input prepared = some hop)
    (low : input.packet.ip.packet.ttl.toNat ≤ 1) :
    process pipeline input valid prepared = .ok (expired pipeline input prepared) := by simp [process, routed, low]

theorem process_long (pipeline : ConntrackLifecycle.Pipeline) (input : Input) (valid : TCPRewrite.SourceValid input.packet)
    (prepared : ConntrackLifecycle.Prepared input.lifecycle) (long : 1 < input.packet.ip.packet.ttl.toNat) :
    process pipeline input valid prepared = finish pipeline input valid prepared := by
  unfold process
  split
  · rfl
  · rw [ite_eq_right (by omega)]

theorem step_lifecycle (pipeline : ConntrackLifecycle.Pipeline) (state : ConntrackLifecycle.State) (input : Input)
    (outcome : Outcome input.packet) (accepted : step pipeline state input = .ok outcome)
    (long : 1 < input.packet.ip.packet.ttl.toNat) :
    ∃ model, ConntrackLifecycle.step pipeline state input.lifecycle = .ok model ∧ outcome.lifecycle = some model ∧
      outcome.state = model.state := by
  obtain ⟨valid, prepared, preparedFound, computed⟩ := step_prepared pipeline state input outcome accepted
  rw [process_long pipeline input valid prepared long] at computed
  obtain ⟨model, processed, same⟩ := finish_realizes pipeline input valid prepared outcome computed
  refine ⟨model, ?_, ?_, ?_⟩
  · simp [ConntrackLifecycle.step, preparedFound, processed, bind, Except.bind]
  · rw [same]; rfl
  · rw [same]; rfl

private theorem finish_not_expired (pipeline : ConntrackLifecycle.Pipeline) (input : Input)
    (valid : TCPRewrite.SourceValid input.packet) (prepared : ConntrackLifecycle.Prepared input.lifecycle)
    (outcome : Outcome input.packet) (accepted : finish pipeline input valid prepared = .ok outcome) :
    outcome.disposition ≠ .ttlExpired := by
  obtain ⟨model, processed, same⟩ := finish_realizes pipeline input valid prepared outcome accepted
  rw [same]
  change lifecycleDisposition model.disposition ≠ .ttlExpired
  cases model.disposition <;> decide

theorem process_ttlExpired (pipeline : ConntrackLifecycle.Pipeline) (input : Input)
    (valid : TCPRewrite.SourceValid input.packet) (prepared : ConntrackLifecycle.Prepared input.lifecycle)
    (outcome : Outcome input.packet) (accepted : process pipeline input valid prepared = .ok outcome)
    (low : outcome.disposition = .ttlExpired) :
    (route pipeline input prepared).isSome = true ∧ input.packet.ip.packet.ttl.toNat ≤ 1 ∧
      outcome = expired pipeline input prepared := by
  unfold process at accepted
  split at accepted
  · exact False.elim (finish_not_expired pipeline input valid prepared outcome accepted low)
  · rename_i hop routed
    split at accepted
    · cases accepted
      exact ⟨by simp [routed], by assumption, rfl⟩
    · exact False.elim (finish_not_expired pipeline input valid prepared outcome accepted low)

theorem step_ttlExpired (pipeline : ConntrackLifecycle.Pipeline) (state : ConntrackLifecycle.State) (input : Input)
    (outcome : Outcome input.packet) (accepted : step pipeline state input = .ok outcome)
    (low : outcome.disposition = .ttlExpired) :
    ∃ (_valid : TCPRewrite.SourceValid input.packet) (prepared : ConntrackLifecycle.Prepared input.lifecycle),
      ConntrackLifecycle.prepare state input.lifecycle = .ok prepared ∧
      (route pipeline input prepared).isSome = true ∧ input.packet.ip.packet.ttl.toNat ≤ 1 ∧
      outcome = expired pipeline input prepared := by
  obtain ⟨valid, prepared, preparedFound, computed⟩ := step_prepared pipeline state input outcome accepted
  exact ⟨valid, prepared, preparedFound, process_ttlExpired pipeline input valid prepared outcome computed low⟩

theorem ttlExpired_fresh (pipeline : ConntrackLifecycle.Pipeline) (state : ConntrackLifecycle.State) (input : Input)
    (outcome : Outcome input.packet) (accepted : step pipeline state input = .ok outcome)
    (low : outcome.disposition = .ttlExpired) (fresh : outcome.attachment.fresh = true) :
    outcome.state = state ∧ outcome.output = none ∧ outcome.afterSource = none ∧ outcome.lifecycle = none := by
  obtain ⟨_, prepared, preparedFound, _, _, same⟩ := step_ttlExpired pipeline state input outcome accepted low
  rw [same] at fresh ⊢
  have unchanged := (ConntrackLifecycle.prepare_fresh state input.lifecycle prepared preparedFound fresh).1
  exact ⟨unchanged, rfl, rfl, rfl⟩

theorem ttlExpired_reply (pipeline : ConntrackLifecycle.Pipeline) (state : ConntrackLifecycle.State) (input : Input)
    (outcome : Outcome input.packet) (accepted : step pipeline state input = .ok outcome)
    (low : outcome.disposition = .ttlExpired) (reply : outcome.attachment.direction = .reply) :
    outcome.attachment.classification = .established ∧ outcome.attachment.fresh = false ∧
      outcome.state = state.markReply outcome.attachment.entry.flow ∧ outcome.output = none := by
  obtain ⟨_, prepared, preparedFound, _, _, same⟩ := step_ttlExpired pipeline state input outcome accepted low
  rw [same] at reply ⊢
  obtain ⟨classification, fresh, changed⟩ := ConntrackLifecycle.prepare_reply state input.lifecycle prepared preparedFound reply
  exact ⟨classification, fresh, changed, rfl⟩

theorem ttlExpired_model (pipeline : ConntrackLifecycle.Pipeline) (state : ConntrackLifecycle.State) (input : Input)
    (outcome : Outcome input.packet) (accepted : step pipeline state input = .ok outcome)
    (low : outcome.disposition = .ttlExpired) : outcome.state.model = state.model := by
  obtain ⟨_, prepared, preparedFound, _, _, same⟩ := step_ttlExpired pipeline state input outcome accepted low
  rw [same]
  exact ConntrackLifecycle.prepare_model state input.lifecycle prepared preparedFound

theorem finish_completes (pipeline : ConntrackLifecycle.Pipeline) (input : Input)
    (valid : TCPRewrite.SourceValid input.packet) (prepared : ConntrackLifecycle.Prepared input.lifecycle)
    (model : ConntrackLifecycle.Outcome) (processed : ConntrackLifecycle.process pipeline prepared = .ok model) :
    ∃ outcome, finish pipeline input valid prepared = .ok outcome := by
  unfold finish
  split
  · rename_i error failed
    rw [processed] at failed
    cases failed
  · exact ⟨_, rfl⟩

theorem process_completes (pipeline : ConntrackLifecycle.Pipeline) (input : Input)
    (valid : TCPRewrite.SourceValid input.packet) (prepared : ConntrackLifecycle.Prepared input.lifecycle)
    (model : ConntrackLifecycle.Outcome) (processed : ConntrackLifecycle.process pipeline prepared = .ok model) :
    ∃ outcome, process pipeline input valid prepared = .ok outcome := by
  unfold process
  split
  · exact finish_completes pipeline input valid prepared model processed
  · split
    · exact ⟨_, rfl⟩
    · exact finish_completes pipeline input valid prepared model processed

theorem step_completes (pipeline : ConntrackLifecycle.Pipeline) (state : ConntrackLifecycle.State) (input : Input)
    (bytes : List UInt8) (encoded : TCP.encodeIPv4 input.packet = .ok bytes)
    (prepared : ConntrackLifecycle.Prepared input.lifecycle) (attached : ConntrackLifecycle.prepare state input.lifecycle = .ok prepared)
    (model : ConntrackLifecycle.Outcome) (processed : ConntrackLifecycle.process pipeline prepared = .ok model) :
    ∃ outcome, step pipeline state input = .ok outcome := by
  obtain ⟨outcome, completed⟩ := process_completes pipeline input
    (TCPRewrite.sourceValid_of_encoded input.packet bytes encoded) prepared model processed
  refine ⟨outcome, ?_⟩
  unfold step
  split
  · rename_i error failed
    rw [encoded] at failed
    cases failed
  · simp [attached, completed, Except.mapError, bind, Except.bind]

theorem finish_existing_state (pipeline : ConntrackLifecycle.Pipeline) (input : Input)
    (valid : TCPRewrite.SourceValid input.packet) (prepared : ConntrackLifecycle.Prepared input.lifecycle)
    (outcome : Outcome input.packet) (accepted : finish pipeline input valid prepared = .ok outcome)
    (existing : outcome.attachment.fresh = false) : outcome.state = prepared.state := by
  obtain ⟨model, processed, same⟩ := finish_realizes pipeline input valid prepared outcome accepted
  rw [same] at existing ⊢
  apply ConntrackLifecycle.process_existing_state pipeline prepared model processed
  rw [← ConntrackLifecycle.process_attachment pipeline prepared model processed]
  exact existing

theorem process_existing_state (pipeline : ConntrackLifecycle.Pipeline) (input : Input)
    (valid : TCPRewrite.SourceValid input.packet) (prepared : ConntrackLifecycle.Prepared input.lifecycle)
    (outcome : Outcome input.packet) (accepted : process pipeline input valid prepared = .ok outcome)
    (existing : outcome.attachment.fresh = false) : outcome.state = prepared.state := by
  unfold process at accepted
  split at accepted
  · exact finish_existing_state pipeline input valid prepared outcome accepted existing
  · split at accepted
    · cases accepted; rfl
    · exact finish_existing_state pipeline input valid prepared outcome accepted existing

theorem step_existing_model (pipeline : ConntrackLifecycle.Pipeline) (state : ConntrackLifecycle.State) (input : Input)
    (outcome : Outcome input.packet) (accepted : step pipeline state input = .ok outcome)
    (existing : outcome.attachment.fresh = false) : outcome.state.model = state.model := by
  obtain ⟨valid, prepared, preparedFound, computed⟩ := step_prepared pipeline state input outcome accepted
  rw [process_existing_state pipeline input valid prepared outcome computed existing]
  exact ConntrackLifecycle.prepare_model state input.lifecycle prepared preparedFound


theorem step_reply_state (pipeline : ConntrackLifecycle.Pipeline) (state : ConntrackLifecycle.State) (input : Input)
    (outcome : Outcome input.packet) (accepted : step pipeline state input = .ok outcome)
    (reply : outcome.attachment.direction = .reply) :
    outcome.attachment.classification = .established ∧ outcome.attachment.fresh = false ∧
      outcome.state = state.markReply outcome.attachment.entry.flow := by
  obtain ⟨valid, prepared, attached, computed⟩ := step_prepared pipeline state input outcome accepted
  have same := process_attachment pipeline input valid prepared outcome computed
  have preparedReply : prepared.attachment.direction = .reply := by rw [← same]; exact reply
  obtain ⟨classification, fresh, marked⟩ := ConntrackLifecycle.prepare_reply state input.lifecycle prepared attached preparedReply
  have existing : outcome.attachment.fresh = false := by rw [same]; exact fresh
  refine ⟨by rw [same]; exact classification, existing, ?_⟩
  rw [process_existing_state pipeline input valid prepared outcome computed existing, marked, same]

private theorem ofLifecycle_output_isSome (pipeline : ConntrackLifecycle.Pipeline) (input : Input)
    (valid : TCPRewrite.SourceValid input.packet) (prepared : ConntrackLifecycle.Prepared input.lifecycle)
    (model : ConntrackLifecycle.Outcome) (processed : ConntrackLifecycle.process pipeline prepared = .ok model) :
    (ofLifecycle pipeline input valid prepared model processed).output.isSome = model.output.isSome := by
  unfold ofLifecycle
  split <;> simp_all

theorem process_forwarded_iff (pipeline : ConntrackLifecycle.Pipeline) (input : Input)
    (valid : TCPRewrite.SourceValid input.packet) (prepared : ConntrackLifecycle.Prepared input.lifecycle)
    (outcome : Outcome input.packet) (accepted : process pipeline input valid prepared = .ok outcome) :
    outcome.output.isSome = true ↔ outcome.disposition = .forwarded := by
  have finished (accepted : finish pipeline input valid prepared = .ok outcome) :
      outcome.output.isSome = true ↔ outcome.disposition = .forwarded := by
    obtain ⟨model, processed, same⟩ := finish_realizes pipeline input valid prepared outcome accepted
    rw [same, ofLifecycle_output_isSome, ConntrackLifecycle.process_forwarded_iff pipeline prepared model processed]
    change model.disposition = .forwarded ↔ lifecycleDisposition model.disposition = .forwarded
    cases model.disposition <;> simp [lifecycleDisposition]
  unfold process at accepted
  split at accepted
  · exact finished accepted
  · split at accepted
    · cases accepted; simp [expired]
    · exact finished accepted

theorem step_forwarded_iff (pipeline : ConntrackLifecycle.Pipeline) (state : ConntrackLifecycle.State) (input : Input)
    (outcome : Outcome input.packet) (accepted : step pipeline state input = .ok outcome) :
    outcome.output.isSome = true ↔ outcome.disposition = .forwarded := by
  obtain ⟨valid, prepared, _, computed⟩ := step_prepared pipeline state input outcome accepted
  exact process_forwarded_iff pipeline input valid prepared outcome computed

end Netlib.Protocol.TCP.WireForwarding
