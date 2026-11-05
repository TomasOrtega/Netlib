import Netlib.Protocol.MTUForwarding
import Netlib.Protocol.ICMP
import Netlib.Protocol.ICMPNAT

/-!
# Locally generated forwarding errors

The selected profile disables ICMP rate limiting and assumes successful allocation.
Return routing supplies source address, effective MTU, and TTL. Identification is a
nondeterministic choice. Related NAT restores the quotation after destination NAT.
-/

namespace Netlib.Protocol.ICMPForwarding

open Packet InternetChecksum

structure ReturnPath where
  nextHop : String
  source : Address
  mtu : IPv4Fragmentation.MTU
  ttl : UInt8

structure Context where
  returnPath : Address → Option ReturnPath
  broadcasts : List Address := []
  output : StatefulACL.Policy := []
  outputDefault : Action := .permit
  late : StatefulACL.Policy := []
  lateDefault : Action := .permit

structure Pipeline where
  forwarding : MTUForwarding.Pipeline
  control : Context

structure Input where
  transit : MTUForwarding.Input
  linkGroup : Bool := false

def opposite : FlowNAT.Direction → FlowNAT.Direction
  | .original => .reply
  | .reply => .original

@[simp] theorem opposite_opposite (direction : FlowNAT.Direction) : opposite (opposite direction) = direction := by
  cases direction <;> rfl

def addressDestination (attachment : ConntrackLifecycle.Attachment) : Rewrite :=
  let change := attachment.entry.rewrite (opposite attachment.direction)
  { destination := change.destination }

def addressSource (attachment : ConntrackLifecycle.Attachment) : Rewrite :=
  let change := attachment.entry.rewrite (opposite attachment.direction)
  { source := change.source }

def errorTos (tos : UInt8) : UInt8 := (tos &&& 30) ||| 192

def quoteLimit (path : ReturnPath) : Nat := min path.mtu.val 576 - 28

def quoteLength (source : UDP.DecodedIPv4) (path : ReturnPath) : Nat :=
  min source.ip.packet.wireLength (quoteLimit path)

theorem source_minimum (source : UDP.DecodedIPv4) (valid : UDPRewrite.SourceValid source) :
    28 ≤ source.ip.packet.wireLength := by
  have fields := UDP.decode_fields _ _ _ _ valid.1.2
  have size := congrArg List.length fields.2.2
  simp only [UDP.Datagram.encodeBytes_length, UDP.Datagram.wireLength] at size
  unfold IPv4.Packet.wireLength
  omega

theorem quoteLength_bounds (source : UDP.DecodedIPv4) (valid : UDPRewrite.SourceValid source) (path : ReturnPath) :
    28 ≤ quoteLength source path ∧ quoteLength source path ≤ source.ip.packet.wireLength ∧
      quoteLength source path + 28 ≤ path.mtu.val ∧ quoteLength source path + 28 ≤ 576 := by
  have minimum := source_minimum source valid
  have mtu := path.mtu.property.1
  unfold quoteLength quoteLimit
  omega

def cause (outcome : MTUForwarding.Outcome source) : Option ICMP.Kind :=
  match outcome.disposition, outcome.selectedMTU with
  | .ttlExpired, _ => some .timeExceeded
  | .mtuExceeded, some mtu => some (.fragmentationNeeded ⟨mtu.val, mtu.property.2⟩)
  | _, _ => none

def unicastSource (broadcasts : List Address) (address : Address) : Bool :=
  decide (16777216 ≤ address.val ∧ address.val < 3758096384 ∧ address.val / 16777216 ≠ 127) &&
    !broadcasts.contains address

def eligible (context : Context) (input : Input) : Bool :=
  !input.linkGroup && unicastSource context.broadcasts input.transit.packet.ip.packet.source &&
    decide (input.transit.packet.ip.packet.destination.val < 3758096384) &&
    !context.broadcasts.contains input.transit.packet.ip.packet.destination

structure Emission (source : UDP.DecodedIPv4) where
  kind : ICMP.Kind
  path : ReturnPath
  identification : Word
  attachment : ConntrackLifecycle.Attachment
  destinationTarget : Header
  valid : UDPRewrite.SourceValid source

def Emission.length (emission : Emission source) : Nat := quoteLength source emission.path

def Emission.initialQuote (emission : Emission source) : IPv4Quote.Decoded :=
  IPv4Quote.make source emission.length

def Emission.destinationQuote (emission : Emission source) : IPv4Quote.Decoded :=
  ICMPNAT.patch emission.initialQuote { emission.destinationTarget with protocol := Packet.Protocol.udp }

def Emission.restoreTarget (emission : Emission source) : Header :=
  { emission.attachment.entry.flow.input emission.attachment.direction with protocol := Packet.Protocol.udp }

def Emission.quote (emission : Emission source) : IPv4Quote.Decoded :=
  ICMPNAT.patch emission.destinationQuote emission.restoreTarget

def Emission.initialHeader (emission : Emission source) : Header :=
  ⟨emission.path.source, source.ip.packet.source, Packet.Protocol.icmp, 0, 0⟩

def Emission.beforeSource (emission : Emission source) : Header :=
  (addressDestination emission.attachment).apply emission.initialHeader

def Emission.afterSource (emission : Emission source) : Header :=
  (addressSource emission.attachment).apply emission.beforeSource

def Emission.message (emission : Emission source) : ICMP.Message := ⟨emission.kind, IPv4Quote.bytes emission.quote⟩

def Emission.packet (emission : Emission source) : IPv4.Packet :=
  ⟨errorTos source.ip.packet.tos, emission.identification, false, emission.path.ttl, Packet.Protocol.icmp,
    emission.afterSource.source, emission.afterSource.destination, ICMP.encode emission.message⟩

def Emission.bytes (emission : Emission source) : List UInt8 :=
  IPv4.headerBytes emission.packet (IPv4.computedChecksum emission.packet) ++ emission.packet.payload

theorem Emission.initialQuote_valid (emission : Emission source) : emission.initialQuote.Valid :=
  IPv4Quote.make_valid source emission.valid emission.length
    (quoteLength_bounds source emission.valid emission.path).1 (quoteLength_bounds source emission.valid emission.path).2.1

theorem Emission.destinationQuote_valid (emission : Emission source) : emission.destinationQuote.Valid :=
  ICMPNAT.patch_valid emission.initialQuote emission.initialQuote_valid _ rfl

theorem Emission.quote_valid (emission : Emission source) : emission.quote.Valid :=
  ICMPNAT.patch_valid emission.destinationQuote emission.destinationQuote_valid _ rfl

theorem Emission.quote_length (emission : Emission source) : (IPv4Quote.bytes emission.quote).length = emission.length := by
  simp only [IPv4Quote.bytes, List.length_append, IPv4Quote.headerBytes_length, Emission.quote,
    Emission.destinationQuote, ICMPNAT.patch_payload, ICMPNAT.patchPayload_length, Emission.initialQuote,
    IPv4Quote.make, List.length_take]
  have bound := (quoteLength_bounds source emission.valid emission.path).2.1
  have minimum := (quoteLength_bounds source emission.valid emission.path).1
  unfold Emission.length IPv4.Packet.wireLength at *
  omega

theorem Emission.fits (emission : Emission source) :
    emission.packet.wireLength ≤ emission.path.mtu.val ∧ emission.packet.wireLength ≤ 576 := by
  have bounds := quoteLength_bounds source emission.valid emission.path
  simpa only [Emission.packet, IPv4.Packet.wireLength, ICMP.encode, ICMP.bytes_length,
    Emission.message, emission.quote_length, Emission.length, Nat.add_assoc] using bounds.2.2

theorem Emission.encoded (emission : Emission source) : IPv4.encode emission.packet = .ok emission.bytes := by
  have fits := emission.fits
  have bounded : emission.packet.Encodable := by unfold IPv4.Packet.Encodable; omega
  simp only [IPv4.encode, bounded, ite_true, Emission.bytes]

theorem Emission.decoded (emission : Emission source) :
    IPv4.decode emission.bytes = .ok ⟨emission.packet, IPv4.computedChecksum emission.packet, []⟩ :=
  IPv4.decode_encode _ _ emission.encoded

theorem Emission.icmp_decoded (emission : Emission source) :
    ICMP.decode emission.packet.payload = .ok ⟨emission.message, ICMP.computedChecksum emission.message⟩ :=
  ICMP.decode_encode emission.message

theorem Emission.quoted_decoded (emission : Emission source) :
    IPv4Quote.decode emission.message.quote = .ok emission.quote :=
  IPv4Quote.decode_bytes emission.quote emission.quote_valid

theorem Emission.quoted_app_prefix (emission : Emission source) :
    emission.quote.packet.payload.drop 8 = emission.initialQuote.packet.payload.drop 8 := by
  rw [Emission.quote, ICMPNAT.patch_appPrefix, Emission.destinationQuote, ICMPNAT.patch_appPrefix]

inductive Disposition where
  | notNeeded | suppressed | noReturnRoute | outputDrop | lateDrop | sent
  deriving Repr, BEq, DecidableEq

structure Control (source : UDP.DecodedIPv4) where
  reason : Option ICMP.Kind
  disposition : Disposition
  beforeSource : Option Header := none
  afterSource : Option Header := none
  output : Option (Emission source) := none

def generate (context : Context) (input : Input) (outcome : MTUForwarding.Outcome input.transit.packet)
    (identification : Word) (valid : UDPRewrite.SourceValid input.transit.packet) : Control input.transit.packet :=
  match cause outcome with
  | none => ⟨none, .notNeeded, none, none, none⟩
  | some kind =>
    if !eligible context input then ⟨some kind, .suppressed, none, none, none⟩
    else match context.returnPath input.transit.packet.ip.packet.source with
      | none => ⟨some kind, .noReturnRoute, none, none, none⟩
      | some path =>
        let emission : Emission input.transit.packet :=
          ⟨kind, path, identification, outcome.attachment, outcome.afterDestination, valid⟩
        if StatefulACL.Policy.evaluate context.outputDefault context.output .related emission.beforeSource = .deny then
          ⟨some kind, .outputDrop, some emission.beforeSource, none, none⟩
        else if StatefulACL.Policy.evaluate context.lateDefault context.late .related emission.afterSource = .deny then
          ⟨some kind, .lateDrop, some emission.beforeSource, some emission.afterSource, none⟩
        else ⟨some kind, .sent, some emission.beforeSource, some emission.afterSource, some emission⟩

structure Outcome (source : UDP.DecodedIPv4) where
  transit : MTUForwarding.Outcome source
  control : Control source

theorem sourceValid_of_step (pipeline : MTUForwarding.Pipeline) (before : ConntrackLifecycle.State)
    (input : MTUForwarding.Input) (outcome : MTUForwarding.Outcome input.packet)
    (accepted : MTUForwarding.step pipeline before input = .ok outcome) : UDPRewrite.SourceValid input.packet := by
  obtain ⟨_, _, valid, _⟩ := MTUForwarding.step_prepared pipeline before input outcome accepted
  exact valid

def step (pipeline : Pipeline) (before : ConntrackLifecycle.State) (input : Input) (identification : Word) :
    Except MTUForwarding.Error (Outcome input.transit.packet) :=
  match accepted : MTUForwarding.step pipeline.forwarding before input.transit with
  | .error error => .error error
  | .ok outcome => .ok ⟨outcome, generate pipeline.control input outcome identification
      (sourceValid_of_step pipeline.forwarding before input.transit outcome accepted)⟩

theorem step_transit (pipeline : Pipeline) (before : ConntrackLifecycle.State) (input : Input) (identification : Word)
    (outcome : Outcome input.transit.packet) (accepted : step pipeline before input identification = .ok outcome) :
    MTUForwarding.step pipeline.forwarding before input.transit = .ok outcome.transit := by
  unfold step at accepted
  split at accepted
  · cases accepted
  · cases accepted
    assumption

theorem step_valid (pipeline : Pipeline) (before : ConntrackLifecycle.State) (input : Input) (identification : Word)
    (outcome : Outcome input.transit.packet) (_accepted : step pipeline before input identification = .ok outcome) :
    outcome.transit.state.Valid := outcome.transit.valid

end Netlib.Protocol.ICMPForwarding
