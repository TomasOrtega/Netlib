import Netlib.Protocol.TCP.IPv4
import Netlib.Protocol.TCP.SequenceSpace
import Netlib.Import.PacketFields
import Netlib.Import.EAPOL
import Netlib.Standards.Basic

/-! TCP byte validation and serial-number calculations have no connection-state interpretation. -/

namespace Netlib.Check.TCP

open Protocol
namespace Model
export Netlib.Protocol.TCP (Segment Seq decode encode checksumAccepts pseudoHeader occupiedLength)
end Model

structure Checked (source destination : Packet.Address) (bytes : List UInt8) where
  segment : Model.Segment
  decoded : Model.decode source destination bytes = .ok segment

def checkBytes (source destination : Packet.Address) (bytes : List UInt8) : Except String (Checked source destination bytes) :=
  match decoded : Model.decode source destination bytes with
  | .error reason => .error reason
  | .ok segment => .ok ⟨segment, decoded⟩

def Checked.encode (checked : Checked source destination bytes) : Except String (List UInt8) :=
  Model.encode source destination checked.segment

theorem Checked.encode_eq (checked : Checked source destination bytes) : checked.encode = .ok bytes :=
  Protocol.TCP.encode_decode _ _ _ _ checked.decoded

theorem Checked.checksum (checked : Checked source destination bytes) :
    InternetChecksum.valid (Protocol.TCP.pseudoHeader source destination checked.segment.lengthWord ++ bytes) = true :=
  Protocol.TCP.decode_checksum _ _ _ _ checked.decoded

structure Input where
  source : Packet.Address
  destination : Packet.Address
  bytes : List UInt8

def Input.fromJson (json : Lean.Json) : Except String Input := do
  Import.PacketFields.fields json ["schema", "source", "destination", "raw"]
  if (← (← json.getObjVal? "schema").getNat?) != 1 then throw "Use TCP segment schema 1."
  return ⟨← Import.IPv4.parseAddress (← (← json.getObjVal? "source").getStr?),
    ← Import.IPv4.parseAddress (← (← json.getObjVal? "destination").getStr?),
    ← Import.EAPOL.bytesFromHex (← (← json.getObjVal? "raw").getStr?)⟩

def Input.parse (text : String) : Except String Input := do Input.fromJson (← Import.Json.parse text)

def Input.check (input : Input) : Except String (Checked input.source input.destination input.bytes) :=
  checkBytes input.source input.destination input.bytes

def flagNames (flags : UInt8) : List String :=
  [("CWR", Protocol.TCP.Flags.cwr flags), ("ECE", Protocol.TCP.Flags.ece flags),
    ("URG", Protocol.TCP.Flags.urg flags), ("ACK", Protocol.TCP.Flags.ack flags),
    ("PSH", Protocol.TCP.Flags.psh flags), ("RST", Protocol.TCP.Flags.rst flags),
    ("SYN", Protocol.TCP.Flags.syn flags), ("FIN", Protocol.TCP.Flags.fin flags)].filterMap
      (fun (name, present) => if present then some name else none)

def segmentJson (segment : Model.Segment) : Lean.Json := Lean.Json.mkObj [
  ("sourcePort", Lean.toJson segment.sourcePort.val), ("destinationPort", Lean.toJson segment.destinationPort.val),
  ("sequence", Lean.toJson segment.sequence.val), ("acknowledgment", Lean.toJson segment.acknowledgment.val),
  ("reserved", Lean.toJson segment.reserved.val), ("flags", Lean.toJson segment.flags.toNat),
  ("flagNames", Lean.toJson (flagNames segment.flags)), ("window", Lean.toJson segment.window.val),
  ("checksum", Lean.toJson segment.checksum.val), ("urgentPointer", Lean.toJson segment.urgentPointer.val),
  ("headerLength", Lean.toJson segment.headerLength), ("dataOffset", Lean.toJson segment.dataOffset),
  ("sequenceSpaceLength", Lean.toJson (Protocol.TCP.occupiedLength segment.payload.length segment.flags)),
  ("optionsHex", Lean.toJson (Import.EAPOL.bytesToHex segment.options)),
  ("payloadHex", Lean.toJson (Import.EAPOL.bytesToHex segment.payload)),
  ("mssValues", Lean.toJson ((Protocol.TCP.Options.maximumSegmentSizes segment.options).map (·.val))),
  ("selectedOptionSemantics", Lean.toJson (Protocol.TCP.Options.synCompatible segment.flags segment.options))]

def sources : List Standards.Source := [
  ⟨"Transmission Control Protocol", "RFC 9293", "3.1–3.4", "https://www.rfc-editor.org/rfc/rfc9293.html#section-3.1"⟩,
  ⟨"Computing the Internet Checksum", "RFC 1071", "1", "https://www.rfc-editor.org/rfc/rfc1071.html#section-1"⟩]

def assumptions : List String := [
  "The supplied addresses are the actual IPv4 pseudoheader addresses at the selected observation point.",
  "The bytes contain all bytes of one TCP segment with completed checksums and no offload intermediates.",
  "A zero checksum word has no omission meaning and must satisfy the same mandatory checksum equation.",
  "Received reserved bits and unknown well-formed options remain preserved; new endpoint generation sets reserved bits to zero.",
  "The selected option semantics include only MSS placement. Other option rules and TCP event processing remain separate.",
  "Byte validation establishes no connection, acceptable acknowledgment, authentication, routing permission, or eventual delivery."]

def Checked.renderJson (checked : Checked source destination bytes) : Lean.Json := Lean.Json.mkObj [
  ("scope", Lean.toJson "ipv4-tcp-segment-framing"), ("valid", Lean.toJson true),
  ("source", Lean.toJson (Import.PacketFields.addressText source)),
  ("destination", Lean.toJson (Import.PacketFields.addressText destination)),
  ("bytes", Lean.toJson bytes.length), ("checksumVerified", Lean.toJson true),
  ("segment", segmentJson checked.segment), ("assumptions", Lean.toJson assumptions),
  ("sources", Lean.toJson (sources.map fun source => Lean.Json.mkObj [
    ("document", Lean.toJson source.document), ("version", Lean.toJson source.version),
    ("clause", Lean.toJson source.clause), ("url", Lean.toJson source.url)]))]

def Checked.render (checked : Checked source destination bytes) : String :=
  "TCP SEGMENT BYTES VALID\n" ++ checked.renderJson.pretty

structure SequenceInput where
  first : Model.Seq
  second : Model.Seq
  length : Nat

private def sequence (json : Lean.Json) : Except String Model.Seq := do
  let value ← json.getNat?
  if bounded : value < 4294967296 then return ⟨⟨value, bounded⟩⟩
  else throw "Sequence words must fit in 32 bits."

def SequenceInput.fromJson (json : Lean.Json) : Except String SequenceInput := do
  Import.PacketFields.fields json ["schema", "first", "second", "length"]
  if (← (← json.getObjVal? "schema").getNat?) != 1 then throw "Use TCP sequence schema 1."
  let length ← (← json.getObjVal? "length").getNat?
  if 4294967296 < length then throw "A selected circular interval cannot exceed the sequence-space modulus."
  return ⟨← sequence (← json.getObjVal? "first"), ← sequence (← json.getObjVal? "second"), length⟩

def SequenceInput.parse (text : String) : Except String SequenceInput := do
  SequenceInput.fromJson (← Import.Json.parse text)

def SequenceInput.renderJson (input : SequenceInput) : Lean.Json := Lean.Json.mkObj [
  ("scope", Lean.toJson "tcp-serial-arithmetic"), ("first", Lean.toJson input.first.val),
  ("second", Lean.toJson input.second.val), ("distance", Lean.toJson (Protocol.TCP.Seq.distance input.first input.second)),
  ("before", Lean.toJson (Protocol.TCP.Seq.before input.first input.second)),
  ("reverseBefore", Lean.toJson (Protocol.TCP.Seq.before input.second input.first)),
  ("equal", Lean.toJson (input.first == input.second)), ("length", Lean.toJson input.length),
  ("contains", Lean.toJson (Protocol.TCP.Seq.inInterval input.first input.length input.second)),
  ("shortArc", Lean.toJson (decide (input.length < Protocol.TCP.Seq.halfSpace))),
  ("assumption", Lean.toJson "Transitivity and interval ordering require a common arc shorter than half the sequence space.")]

end Netlib.Check.TCP
