import Netlib.Protocol.ICMPNAT

namespace NetlibTest.ICMPNAT

open Netlib Netlib.Protocol Netlib.Protocol.ICMPNAT

example (quote : IPv4Quote.Decoded) (valid : quote.Valid) (target : Packet.Header)
    (protocol : target.protocol = Packet.Protocol.udp) : (patch quote target).Valid :=
  patch_valid quote valid target protocol

example (quote : IPv4Quote.Decoded) (valid : quote.Valid) (target : Packet.Header) :
    (patch (patch quote target) (IPv4Quote.header quote)).packet = quote.packet :=
  patch_roundtrip_packet quote valid target

private def ensure (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def unwrap (value : Except String α) : IO α :=
  match value with
  | .ok result => pure result
  | .error error => throw (IO.userError error)

private def source : Packet.Address := 3221225985
private def destination : Packet.Address := 3325256706
private def target : Packet.Header := ⟨3405803785, 3232235777, Packet.Protocol.udp, 65535, 8080⟩

private def makeInput (datagram : UDP.Datagram) : IO UDP.DecodedIPv4 := do
  let udp ← unwrap (UDP.encode source destination datagram)
  let ip : IPv4.Packet := ⟨7, 65535, true, 63, Packet.Protocol.udp, source, destination, udp⟩
  unwrap (UDP.decodeIPv4 (← unwrap (IPv4.encode ip)))

def run : IO Unit := do
  for payload in [[1], [1, 2], [1, 2, 3, 4, 5], [0, 255, 128, 0, 42], List.replicate 513 255] do
    for omitted in [false, true] do
      let datagram := if omitted then UDP.Datagram.mk 12345 53 0 payload
        else UDP.computed source destination 12345 53 payload
      let input ← makeInput datagram
      for length in [28, 29, input.ip.packet.wireLength] do
        let quote := IPv4Quote.make input length
        let translated := patch quote target
        let wire ← unwrap (IPv4Quote.encodeDecoded translated)
        let parsed ← unwrap (IPv4Quote.decode wire)
        ensure (parsed == translated && IPv4Quote.header parsed == target &&
            parsed.declaredLength == quote.declaredLength && parsed.packet.tos == quote.packet.tos &&
            parsed.packet.identification == quote.packet.identification && parsed.packet.ttl == quote.packet.ttl &&
            parsed.packet.dontFragment == quote.packet.dontFragment &&
            parsed.packet.payload.drop 8 == quote.packet.payload.drop 8 &&
            IPv4Quote.udpLength? parsed.packet.payload == IPv4Quote.udpLength? quote.packet.payload)
          "A partial NAT quote patch must change the tuple and preserve metadata, original lengths, and application prefix."
        let expected := if omitted then 0
          else (UDP.computed target.source target.destination target.sourcePort target.destinationPort payload).checksum
        ensure (quotedChecksum parsed.packet.payload == expected)
          "A partial quote checksum delta must agree with independent complete UDP checksum synthesis."
        let restored := patch parsed input.header
        ensure (restored.packet == quote.packet && restored.declaredLength == quote.declaredLength &&
            (← unwrap (IPv4Quote.encodeDecoded restored)) == (← unwrap (IPv4Quote.encodeDecoded (recompute quote))))
          "Inverting an actual translated partial quote must restore every semantic byte, including UDP checksum."
        if length == input.ip.packet.wireLength then
          let full ← unwrap (UDP.decode target.source target.destination parsed.packet.payload)
          ensure (full.payload == payload && full.sourcePort == target.sourcePort && full.destinationPort == target.destinationPort)
            "A complete patched quotation must pass UDP pseudoheader validation at its translated addresses."
  let omitted ← makeInput ⟨0, 0, 0, [1, 2, 3]⟩
  let quote := IPv4Quote.make omitted 28
  ensure (quotedChecksum (patch quote target).packet.payload == 0)
    "Incremental quotation translation must preserve explicitly omitted UDP checksums."
  IO.println "Partial ICMP quotation NAT tests passed."

end NetlibTest.ICMPNAT
