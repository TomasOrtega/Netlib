import Netlib.Protocol.ConntrackLifecycle
import Netlib.Protocol.ICMPPrefixNAT
import Netlib.Protocol.ICMP
import Netlib.Protocol.IPv4Fragmentation

namespace Netlib.Protocol.RelatedICMP

open Packet InternetChecksum

/-- Outer checksums are verified; the quoted datagram remains untrusted wire data. -/
structure Source where
  bytes : List UInt8
  ip : IPv4.Decoded
  icmp : ICMP.Decoded
  quote : IPv4QuotePrefix.Decoded
  network : IPv4.decode bytes = .ok ip
  protocol : ip.packet.protocol = Packet.Protocol.icmp
  transport : ICMP.decode ip.packet.payload = .ok icmp
  quotation : IPv4QuotePrefix.decode icmp.message.quote = .ok quote

def decode (bytes : List UInt8) : Except String Source :=
  match network : IPv4.decode bytes with
  | .error error => .error error
  | .ok ip =>
    if protocol : ip.packet.protocol = Packet.Protocol.icmp then
      match transport : ICMP.decode ip.packet.payload with
      | .error error => .error error
      | .ok icmp =>
        match quotation : IPv4QuotePrefix.decode icmp.message.quote with
        | .error error => .error error
        | .ok quote =>
          .ok ⟨bytes, ip, icmp, quote, network, protocol, transport, quotation⟩
    else .error "Require outer IPv4 protocol ICMP."

theorem Source.quote_shape (source : Source) : source.quote.Shape :=
  (IPv4QuotePrefix.decode_fields _ _ source.quotation).1

def opposite : FlowNAT.Direction → FlowNAT.Direction
  | .original => .reply
  | .reply => .original

@[simp] theorem opposite_opposite (direction : FlowNAT.Direction) : opposite (opposite direction) = direction := by
  cases direction <;> rfl

structure Input where
  zone : Nat
  source : Source

def Input.header (input : Input) : Header :=
  ⟨input.source.ip.packet.source, input.source.ip.packet.destination, Packet.Protocol.icmp, 0, 0⟩

structure Association (before : ConntrackLifecycle.State) (input : Input) where
  record : ConntrackLifecycle.Record
  direction : FlowNAT.Direction
  member : record ∈ before.records
  compatible : record.entry.Compatible
  attached : record.entry.flow.key direction = (input.zone, (IPv4QuotePrefix.header input.source.quote).reverse)
  outerDestination : input.source.ip.packet.destination = (record.entry.flow.input direction).destination
  initial : IPv4QuotePrefix.offset input.source.quote = 0
  protocol : input.source.quote.packet.protocol = Packet.Protocol.udp

def Association.entry (association : Association before input) : NetfilterNAT.Entry := association.record.entry

def Association.hit (association : Association before input) : FlowNAT.Hit :=
  ⟨association.entry.flow, association.direction⟩

inductive Error where
  | invalidState | invalidZone
  deriving Repr, BEq, DecidableEq

def Error.describe : Error → String
  | .invalidState => "The confirmed table is invalid."
  | .invalidZone => "The lookup zone exceeds 16 bits."

structure Prepared (before : ConntrackLifecycle.State) (input : Input) where
  valid : before.Valid
  association : Option (Association before input)

/-- A miss or inconsistent outer destination is unassociated, without creating a candidate. -/
def prepare (before : ConntrackLifecycle.State) (input : Input) : Except Error (Prepared before input) :=
  if valid : before.check = true then
    if input.zone ≥ 65536 then .error .invalidZone
    else if unsupported : IPv4QuotePrefix.offset input.source.quote ≠ 0 ∨ input.source.quote.packet.protocol ≠ Packet.Protocol.udp then
      .ok ⟨(ConntrackLifecycle.State.check_correct _).mp valid, none⟩
    else match found : before.model.lookup input.zone (IPv4QuotePrefix.header input.source.quote).reverse with
      | none => .ok ⟨(ConntrackLifecycle.State.check_correct _).mp valid, none⟩
      | some hit =>
        match recordFound : before.records.find? (fun record => decide (record.entry.flow = hit.entry)) with
        | none => .error .invalidState
        | some record =>
          have member := List.mem_of_find?_eq_some recordFound
          have same : record.entry.flow = hit.entry := of_decide_eq_true (List.find?_some
            (p := fun record : ConntrackLifecycle.Record => decide (record.entry.flow = hit.entry)) (a := record) recordFound)
          have checked := (ConntrackLifecycle.State.check_correct _).mp valid
          if destination : input.source.ip.packet.destination = (record.entry.flow.input hit.direction).destination then
            .ok ⟨checked, some ⟨record, hit.direction, member, checked.2 _ member,
              by rw [same]; exact (FlowNAT.Snapshot.lookup_sound _ _ _ _ found).2, destination, by
                by_cases zero : IPv4QuotePrefix.offset input.source.quote = 0
                · exact zero
                · exact False.elim (unsupported (Or.inl zero)), by
                by_cases sameProtocol : input.source.quote.packet.protocol = Packet.Protocol.udp
                · exact sameProtocol
                · exact False.elim (unsupported (Or.inr sameProtocol))⟩⟩
          else .ok ⟨checked, none⟩
  else .error .invalidState

theorem association_unique (valid : before.Valid) (left right : Association before input) : left.hit = right.hit := by
  apply FlowNAT.Snapshot.lookup_unique before.model valid.1
  · exact List.mem_map.mpr ⟨left.record, left.member, rfl⟩
  · exact List.mem_map.mpr ⟨right.record, right.member, rfl⟩
  · exact left.attached.trans right.attached.symm

theorem association_unique_for_quote (valid : before.Valid)
    (left : Association before first) (right : Association before second)
    (zone : first.zone = second.zone)
    (quote : IPv4QuotePrefix.header first.source.quote = IPv4QuotePrefix.header second.source.quote) :
    left.hit = right.hit := by
  apply FlowNAT.Snapshot.lookup_unique before.model valid.1
  · exact List.mem_map.mpr ⟨left.record, left.member, rfl⟩
  · exact List.mem_map.mpr ⟨right.record, right.member, rfl⟩
  · have sameKey : (first.zone, (IPv4QuotePrefix.header first.source.quote).reverse) =
        (second.zone, (IPv4QuotePrefix.header second.source.quote).reverse) := by rw [zone, quote]
    exact left.attached.trans (sameKey.trans right.attached.symm)

theorem prepare_miss (checked : before.check = true) (zone : input.zone < 65536)
    (missing : before.model.lookup input.zone (IPv4QuotePrefix.header input.source.quote).reverse = none) :
    prepare before input = .ok ⟨(ConntrackLifecycle.State.check_correct _).mp checked, none⟩ := by
  have bounded : ¬input.zone ≥ 65536 := by omega
  simp only [prepare, checked, dite_true, bounded, ite_false]
  split
  · rfl
  · split
    · rfl
    · rename_i hit found
      rw [missing] at found
      cases found

def Association.innerDestinationTarget (association : Association before input) : Header :=
  ((ConntrackLifecycle.destinationStage association.entry association.direction).apply
    (IPv4QuotePrefix.header input.source.quote).reverse).reverse

def Association.destinationQuote (association : Association before input) : IPv4QuotePrefix.Decoded :=
  if association.entry.changesDestination association.direction then
    ICMPPrefixNAT.patch input.source.quote association.innerDestinationTarget
  else input.source.quote

def Association.innerSourceTarget (association : Association before input) : Header :=
  ((ConntrackLifecycle.sourceStage association.entry association.direction).apply
    (IPv4QuotePrefix.header association.destinationQuote).reverse).reverse

def Association.quote (association : Association before input) : IPv4QuotePrefix.Decoded :=
  if association.entry.changesSource association.direction then
    ICMPPrefixNAT.patch association.destinationQuote association.innerSourceTarget
  else association.destinationQuote

def Association.beforeSource (association : Association before input) : Header :=
  let change := association.entry.rewrite association.direction
  ({ destination := change.destination } : Rewrite).apply input.header

def Association.afterSource (association : Association before input) : Header :=
  let change := association.entry.rewrite association.direction
  ({ source := change.source } : Rewrite).apply association.beforeSource

private theorem header_protocol (quote : IPv4QuotePrefix.Decoded) :
    (IPv4QuotePrefix.header quote).protocol = quote.packet.protocol := by
  unfold IPv4QuotePrefix.header IPv4Quote.header
  split <;> rfl

theorem Association.destination_protocol (association : Association before input) :
    association.innerDestinationTarget.protocol = input.source.quote.packet.protocol := by
  change (IPv4QuotePrefix.header input.source.quote).protocol = input.source.quote.packet.protocol
  exact header_protocol _

theorem Association.source_protocol (association : Association before input) :
    association.innerSourceTarget.protocol = association.destinationQuote.packet.protocol := by
  change (IPv4QuotePrefix.header association.destinationQuote).protocol = association.destinationQuote.packet.protocol
  exact header_protocol _

theorem Association.destinationQuote_shape (association : Association before input) : association.destinationQuote.Shape := by
  unfold Association.destinationQuote
  split
  · exact ICMPPrefixNAT.patch_shape _ input.source.quote_shape _
  · exact input.source.quote_shape

theorem Association.quote_shape (association : Association before input) : association.quote.Shape := by
  unfold Association.quote
  split
  · exact ICMPPrefixNAT.patch_shape _ association.destinationQuote_shape _
  · exact association.destinationQuote_shape

theorem Association.destinationQuote_header (association : Association before input) :
    IPv4QuotePrefix.header association.destinationQuote = association.innerDestinationTarget := by
  cases selected : association.entry.changesDestination association.direction
  · simp only [Association.destinationQuote, selected, Bool.false_eq_true, ite_false]
    simp [Association.innerDestinationTarget, ConntrackLifecycle.destinationStage,
      NetfilterNAT.Entry.rewrite, selected, Rewrite.apply, Header.reverse]
  · simp only [Association.destinationQuote, selected, ite_true]
    exact ICMPPrefixNAT.patch_header _ input.source.quote_shape _ association.destination_protocol

theorem Association.sourceQuote_header (association : Association before input) :
    IPv4QuotePrefix.header association.quote = association.innerSourceTarget := by
  cases selected : association.entry.changesSource association.direction
  · simp only [Association.quote, selected, Bool.false_eq_true, ite_false]
    simp [Association.innerSourceTarget, ConntrackLifecycle.sourceStage,
      NetfilterNAT.Entry.rewrite, selected, Rewrite.apply, Header.reverse]
  · simp only [Association.quote, selected, ite_true]
    exact ICMPPrefixNAT.patch_header _ association.destinationQuote_shape _ association.source_protocol

theorem Association.quote_header (association : Association before input) :
    IPv4QuotePrefix.header association.quote = association.entry.flow.input (opposite association.direction) := by
  rw [association.sourceQuote_header]
  unfold Association.innerSourceTarget
  rw [association.destinationQuote_header]
  unfold Association.innerDestinationTarget
  rw [Header.reverse_reverse]
  have attached : association.entry.flow.input association.direction = (IPv4QuotePrefix.header input.source.quote).reverse :=
    congrArg Prod.snd association.attached
  rw [← attached, ConntrackLifecycle.stages_correct association.entry association.compatible association.direction]
  cases association.direction <;> exact Header.reverse_reverse _

theorem Association.destinationQuote_preserves_destination (association : Association before input) :
    (IPv4QuotePrefix.header association.destinationQuote).destinationEndpoint =
      (IPv4QuotePrefix.header input.source.quote).destinationEndpoint := by
  rw [association.destinationQuote_header]
  rfl

theorem Association.sourceQuote_preserves_source (association : Association before input) :
    (IPv4QuotePrefix.header association.quote).sourceEndpoint =
      (IPv4QuotePrefix.header association.destinationQuote).sourceEndpoint := by
  rw [association.sourceQuote_header]
  rfl

theorem Association.outer_stages (association : Association before input) :
    association.beforeSource.source = input.header.source ∧
    association.afterSource.destination = association.beforeSource.destination ∧
    association.beforeSource.protocol = Packet.Protocol.icmp ∧
    association.afterSource.protocol = Packet.Protocol.icmp ∧
    association.beforeSource.sourcePort = 0 ∧ association.beforeSource.destinationPort = 0 ∧
    association.afterSource.sourcePort = 0 ∧ association.afterSource.destinationPort = 0 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem Association.destinationQuote_app_prefix (association : Association before input) :
    association.destinationQuote.packet.payload.drop 8 = input.source.quote.packet.payload.drop 8 := by
  unfold Association.destinationQuote
  split
  · exact ICMPPrefixNAT.patch_appPrefix _ _
  · rfl

theorem Association.quoted_app_prefix (association : Association before input) :
    association.quote.packet.payload.drop 8 = input.source.quote.packet.payload.drop 8 := by
  unfold Association.quote
  split
  · rw [ICMPPrefixNAT.patch_appPrefix, association.destinationQuote_app_prefix]
  · exact association.destinationQuote_app_prefix

theorem Association.quoted_prefix (association : Association before input) (length : Nat) :
    (association.quote.packet.payload.drop 8).take length =
      (input.source.quote.packet.payload.drop 8).take length := by
  rw [association.quoted_app_prefix]

theorem Association.quoted_ip_checksum (association : Association before input) :
    InternetChecksum.valid (IPv4QuotePrefix.headerBytes association.quote) =
      InternetChecksum.valid (IPv4QuotePrefix.headerBytes input.source.quote) := by
  unfold Association.quote
  split
  · rw [ICMPPrefixNAT.patch_ip_checksum_valid_eq]
    unfold Association.destinationQuote
    split
    · exact ICMPPrefixNAT.patch_ip_checksum_valid_eq _ _
    · rfl
  · unfold Association.destinationQuote
    split
    · exact ICMPPrefixNAT.patch_ip_checksum_valid_eq _ _
    · rfl

theorem Association.quoted_metadata (association : Association before input) :
    association.quote.packet.ttl = input.source.quote.packet.ttl ∧
    association.quote.packet.identification = input.source.quote.packet.identification ∧
    association.quote.packet.tos = input.source.quote.packet.tos ∧
    association.quote.packet.dontFragment = input.source.quote.packet.dontFragment ∧
    association.quote.declaredLength = input.source.quote.declaredLength ∧
    association.quote.flags = input.source.quote.flags := by
  cases destination : association.entry.changesDestination association.direction <;>
    cases source : association.entry.changesSource association.direction <;>
    simp [Association.quote, Association.destinationQuote, destination, source, ICMPPrefixNAT.patch]

theorem Association.quoted_checksum_omission (association : Association before input) :
    ICMPNAT.quotedChecksum association.quote.packet.payload = 0 ↔
      ICMPNAT.quotedChecksum input.source.quote.packet.payload = 0 := by
  unfold Association.quote
  split
  · rw [ICMPPrefixNAT.patch_omission _ association.destinationQuote_shape]
    unfold Association.destinationQuote
    split
    · exact ICMPPrefixNAT.patch_omission _ input.source.quote_shape _
    · rfl
  · unfold Association.destinationQuote
    split
    · exact ICMPPrefixNAT.patch_omission _ input.source.quote_shape _
    · rfl

theorem Association.quote_payload_length (association : Association before input) :
    association.quote.packet.payload.length = input.source.quote.packet.payload.length := by
  unfold Association.quote
  split
  · rw [ICMPPrefixNAT.patch_payload_length]
    unfold Association.destinationQuote
    split
    · exact ICMPPrefixNAT.patch_payload_length _ _
    · rfl
  · unfold Association.destinationQuote
    split
    · exact ICMPPrefixNAT.patch_payload_length _ _
    · rfl

theorem Association.no_nat_quote (association : Association before input)
    (source : association.entry.changesSource association.direction = false)
    (destination : association.entry.changesDestination association.direction = false) :
    association.quote = input.source.quote := by
  simp [Association.quote, Association.destinationQuote, source, destination]

def Association.message (association : Association before input) : ICMP.Message :=
  ⟨input.source.icmp.message.kind, IPv4QuotePrefix.bytes association.quote⟩

def Association.packet (association : Association before input) : IPv4.Packet :=
  { input.source.ip.packet with
    ttl := UInt8.ofNat (input.source.ip.packet.ttl.toNat - 1)
    source := association.afterSource.source
    destination := association.afterSource.destination
    payload := ICMP.encode association.message }

theorem Association.ttl (association : Association before input) :
    association.packet.ttl.toNat = input.source.ip.packet.ttl.toNat - 1 := by
  have bounded := input.source.ip.packet.ttl.toNat_lt
  simp only [Association.packet, UInt8.toNat_ofNat']
  exact Nat.mod_eq_of_lt (by omega)

theorem Association.kind (association : Association before input) :
    association.message.kind = input.source.icmp.message.kind := rfl

theorem Association.packet_length (association : Association before input) :
    association.packet.wireLength = input.source.ip.packet.wireLength := by
  have transport := congrArg List.length (ICMP.decode_fields _ _ input.source.transport).2
  have quotation := congrArg List.length (IPv4QuotePrefix.decode_fields _ _ input.source.quotation).2
  simp only [ICMP.bytes_length] at transport
  simp only [IPv4QuotePrefix.bytes, List.length_append, IPv4QuotePrefix.headerBytes_length] at quotation
  simp only [Association.packet, IPv4.Packet.wireLength, ICMP.encode, ICMP.bytes_length,
    Association.message, IPv4QuotePrefix.bytes, List.length_append, IPv4QuotePrefix.headerBytes_length,
    association.quote_payload_length]
  omega

theorem Association.packet_bounded (association : Association before input) : association.packet.Encodable := by
  have bounded := (IPv4.decode_valid _ _ input.source.network).1
  unfold IPv4.Packet.Encodable at *
  rw [association.packet_length]
  exact bounded

def Association.bytes (association : Association before input) : List UInt8 :=
  IPv4.headerBytes association.packet (IPv4.computedChecksum association.packet) ++ association.packet.payload

theorem Association.encoded (association : Association before input) :
    IPv4.encode association.packet = .ok association.bytes := by
  simp only [IPv4.encode, association.packet_bounded, ite_true, Association.bytes]

theorem Association.decoded (association : Association before input) :
    IPv4.decode association.bytes = .ok ⟨association.packet, IPv4.computedChecksum association.packet, []⟩ :=
  IPv4.decode_encode _ _ association.encoded

theorem Association.icmp_decoded (association : Association before input) :
    ICMP.decode association.packet.payload = .ok ⟨association.message, ICMP.computedChecksum association.message⟩ :=
  ICMP.decode_encode association.message

theorem Association.quoted_decoded (association : Association before input) :
    IPv4QuotePrefix.decode association.message.quote = .ok association.quote :=
  IPv4QuotePrefix.decode_bytes _ association.quote_shape

theorem Association.checksums (association : Association before input) :
    InternetChecksum.valid (IPv4.headerBytes association.packet (IPv4.computedChecksum association.packet)) = true ∧
    InternetChecksum.valid association.packet.payload = true :=
  ⟨IPv4.computedChecksum_valid _, ICMP.computedChecksum_valid _⟩

structure Pipeline where
  forwarding : ConntrackLifecycle.Pipeline
  mtu : String → IPv4Fragmentation.MTU

structure Emission (before : ConntrackLifecycle.State) (input : Input) where
  association : Association before input
  mtu : IPv4Fragmentation.MTU
  allowed : IPv4Fragmentation.Allowed association.packet mtu

def Emission.family (emission : Emission before input) :
    IPv4Fragmentation.Certified emission.association.packet emission.mtu :=
  IPv4Fragmentation.fragment _ _ emission.association.packet_bounded emission.allowed

theorem Emission.reassembled (emission : Emission before input) :
    IPv4Fragmentation.reassemble emission.family.fragments = .ok emission.association.packet :=
  emission.family.reassembled

inductive Disposition where
  | unrelated | routeDrop | ttlExpired | forwardDrop | lateDrop | mtuExceeded | forwarded
  deriving Repr, BEq, DecidableEq

structure Outcome (before : ConntrackLifecycle.State) (input : Input) where
  valid : before.Valid
  disposition : Disposition
  association : Option (Association before input) := none
  afterDestination : Option Header := none
  afterSource : Option Header := none
  nextHop : Option String := none
  output : Option (Emission before input) := none

def Outcome.state (_outcome : Outcome before input) : ConntrackLifecycle.State := before

private def dropped (prepared : Prepared before input) (association : Association before input)
    (disposition : Disposition) (nextHop : Option String) (afterSource : Option Header := none) : Outcome before input :=
  ⟨prepared.valid, disposition, some association, some association.beforeSource, afterSource, nextHop, none⟩

def process (pipeline : Pipeline) (prepared : Prepared before input) : Outcome before input :=
  match prepared.association with
  | none => ⟨prepared.valid, .unrelated, none, none, none, none, none⟩
  | some association =>
    match Routing.nextHop pipeline.forwarding.routes association.beforeSource.destination with
    | none => dropped prepared association .routeDrop none
    | some hop =>
      if input.source.ip.packet.ttl.toNat ≤ 1 then dropped prepared association .ttlExpired (some hop)
      else if allowed : IPv4Fragmentation.Allowed association.packet (pipeline.mtu hop) then
        if StatefulACL.Policy.evaluate pipeline.forwarding.forwardDefault pipeline.forwarding.forward
            .related association.beforeSource = .deny then dropped prepared association .forwardDrop (some hop)
        else if StatefulACL.Policy.evaluate pipeline.forwarding.lateDefault pipeline.forwarding.late
            .related association.afterSource = .deny then
          dropped prepared association .lateDrop (some hop) (some association.afterSource)
        else ⟨prepared.valid, .forwarded, some association, some association.beforeSource,
          some association.afterSource, some hop, some ⟨association, pipeline.mtu hop, allowed⟩⟩
      else dropped prepared association .mtuExceeded (some hop)

def step (pipeline : Pipeline) (before : ConntrackLifecycle.State) (input : Input) :
    Except Error (Outcome before input) := (prepare before input).map (process pipeline)

@[simp] theorem outcome_state (outcome : Outcome before input) : outcome.state = before := rfl

theorem step_state (pipeline : Pipeline) (before : ConntrackLifecycle.State) (input : Input)
    (outcome : Outcome before input) (_accepted : step pipeline before input = .ok outcome) :
    outcome.state = before := rfl

theorem step_valid (pipeline : Pipeline) (before : ConntrackLifecycle.State) (input : Input)
    (outcome : Outcome before input) (_accepted : step pipeline before input = .ok outcome) :
    outcome.state.Valid := outcome.valid

theorem process_association (pipeline : Pipeline) (prepared : Prepared before input) :
    (process pipeline prepared).association = prepared.association := by
  unfold process
  repeat' first | (symm; assumption) | split

theorem process_unrelated (pipeline : Pipeline) (prepared : Prepared before input)
    (missing : prepared.association = none) : (process pipeline prepared).disposition = .unrelated := by
  simp [process, missing]

theorem process_low_ttl (pipeline : Pipeline) (prepared : Prepared before input)
    (low : input.source.ip.packet.ttl.toNat ≤ 1) : (process pipeline prepared).output = none := by
  unfold process
  split
  · rfl
  · split
    · rfl
    · simp only [low, ite_true, dropped]

theorem step_prepared (pipeline : Pipeline) (before : ConntrackLifecycle.State) (input : Input)
    (outcome : Outcome before input) (accepted : step pipeline before input = .ok outcome) :
    ∃ prepared, prepare before input = .ok prepared ∧ process pipeline prepared = outcome := by
  cases found : prepare before input with
  | error error => simp only [step, found, Except.map] at accepted; cases accepted
  | ok prepared =>
    exact ⟨prepared, rfl, by simpa only [step, found, Except.map, Except.ok.injEq] using accepted⟩

theorem process_output (pipeline : Pipeline) (prepared : Prepared before input) (emission : Emission before input)
    (forwarded : (process pipeline prepared).output = some emission) :
    prepared.association = some emission.association ∧
      (process pipeline prepared).disposition = .forwarded ∧
      (process pipeline prepared).afterDestination = some emission.association.beforeSource ∧
      (process pipeline prepared).afterSource = some emission.association.afterSource ∧
      1 < input.source.ip.packet.ttl.toNat ∧
      StatefulACL.Policy.evaluate pipeline.forwarding.forwardDefault pipeline.forwarding.forward
        .related emission.association.beforeSource = .permit ∧
      StatefulACL.Policy.evaluate pipeline.forwarding.lateDefault pipeline.forwarding.late
        .related emission.association.afterSource = .permit ∧
      ∃ hop, (process pipeline prepared).nextHop = some hop ∧ emission.mtu = pipeline.mtu hop := by
  unfold process at forwarded
  split at forwarded
  · cases forwarded
  · rename_i association associated
    split at forwarded
    · cases forwarded
    · rename_i hop routed
      split at forwarded
      · cases forwarded
      · rename_i live
        split at forwarded
        · rename_i allowed
          split at forwarded
          · cases forwarded
          · rename_i forward
            split at forwarded
            · cases forwarded
            · rename_i late
              cases Option.some.inj forwarded
              have computed : process pipeline prepared =
                  ⟨prepared.valid, .forwarded, some association, some association.beforeSource,
                    some association.afterSource, some hop, some ⟨association, pipeline.mtu hop, allowed⟩⟩ := by
                simp [process, associated, routed, live, forward, late, allowed]
              rw [computed]
              have forwardPermit : StatefulACL.Policy.evaluate pipeline.forwarding.forwardDefault pipeline.forwarding.forward
                  .related association.beforeSource = .permit := by
                cases action : StatefulACL.Policy.evaluate _ _ _ _ <;> simp_all
              have latePermit : StatefulACL.Policy.evaluate pipeline.forwarding.lateDefault pipeline.forwarding.late
                  .related association.afterSource = .permit := by
                cases action : StatefulACL.Policy.evaluate _ _ _ _ <;> simp_all
              exact ⟨associated, rfl, rfl, rfl, by omega, forwardPermit, latePermit, hop, rfl, rfl⟩
        · cases forwarded

theorem step_low_ttl (pipeline : Pipeline) (before : ConntrackLifecycle.State) (input : Input)
    (outcome : Outcome before input) (accepted : step pipeline before input = .ok outcome)
    (low : input.source.ip.packet.ttl.toNat ≤ 1) : outcome.output = none := by
  obtain ⟨prepared, _, processed⟩ := step_prepared pipeline before input outcome accepted
  rw [← processed]
  exact process_low_ttl pipeline prepared low

theorem step_filters (pipeline : Pipeline) (before : ConntrackLifecycle.State) (input : Input)
    (outcome : Outcome before input) (accepted : step pipeline before input = .ok outcome)
    (emission : Emission before input) (forwarded : outcome.output = some emission) :
    outcome.disposition = .forwarded ∧ outcome.association = some emission.association ∧
      outcome.afterDestination = some emission.association.beforeSource ∧
      outcome.afterSource = some emission.association.afterSource ∧
      1 < input.source.ip.packet.ttl.toNat ∧
      StatefulACL.Policy.evaluate pipeline.forwarding.forwardDefault pipeline.forwarding.forward
        .related emission.association.beforeSource = .permit ∧
      StatefulACL.Policy.evaluate pipeline.forwarding.lateDefault pipeline.forwarding.late
        .related emission.association.afterSource = .permit ∧
      ∃ hop, outcome.nextHop = some hop ∧ emission.mtu = pipeline.mtu hop := by
  obtain ⟨prepared, _, processed⟩ := step_prepared pipeline before input outcome accepted
  have evidence := process_output pipeline prepared emission (by rw [processed]; exact forwarded)
  refine ⟨?_, ?_, ?_, ?_, evidence.2.2.2.2.1, evidence.2.2.2.2.2.1, evidence.2.2.2.2.2.2.1, ?_⟩
  · rw [← processed]; exact evidence.2.1
  · rw [← processed, process_association, evidence.1]
  · rw [← processed]; exact evidence.2.2.1
  · rw [← processed]; exact evidence.2.2.2.1
  · rw [← processed]; exact evidence.2.2.2.2.2.2.2

end Netlib.Protocol.RelatedICMP
