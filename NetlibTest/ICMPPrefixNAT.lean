import Netlib.Protocol.ICMPPrefixNAT

namespace NetlibTest.ICMPPrefixNAT

open Netlib Netlib.Protocol Netlib.Protocol.InternetChecksum Netlib.Protocol.ICMPPrefixNAT

private def original : IPv4QuotePrefix.Decoded :=
  ⟨⟨7, 0x1357, true, 31, Packet.Protocol.udp, 0xc0000201, 0xc6336402,
      [0x30, 0x39, 0, 53, 0, 3, 0x43, 0x21, 1, 2, 3]⟩, 0xe123, 0x1234, 1⟩

private def target : Packet.Header := ⟨0xcb007109, 0x0a000001, Packet.Protocol.udp, 0xabcd, 0x1234⟩

example : original.Shape := by decide
example : valid (IPv4QuotePrefix.headerBytes original) = false := by decide
example : valid (IPv4QuotePrefix.headerBytes (patch original target)) = false := by decide
example : (patch original target).declaredLength = 1 := rfl
example : (patch original target).flags = 0xe123 := rfl

private def ensure (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def unwrap (value : Except String α) : IO α :=
  match value with
  | .ok result => pure result
  | .error error => throw (IO.userError error)

private def udpBytes (quote : IPv4QuotePrefix.Decoded) : List UInt8 :=
  UDP.pseudoHeader quote.packet.source quote.packet.destination 3 ++ quote.packet.payload

def run : IO Unit := do
  ensure (!valid (IPv4QuotePrefix.headerBytes original) && !valid (udpBytes original))
    "The regression quotation must contain invalid IPv4 and UDP checksums."
  for flags in ([0, 0x4000, 0x8001, 0x2001, 0xe123, 0xffff] : List Word) do
    for rawChecksum in ([0, 1, 0x1234, 65535] : List Word) do
      let raw := { original with
        flags := flags
        checksum := rawChecksum
        packet := { original.packet with dontFragment := IPv4QuotePrefix.flagsDF flags } }
      let checked := { raw with checksum := checksum (IPv4QuotePrefix.headerBytes { raw with checksum := 0 }) }
      for quote in [raw, checked] do
        let decoded ← unwrap (IPv4QuotePrefix.decode (IPv4QuotePrefix.bytes quote))
        ensure (decoded == quote) "Raw quote parsing must preserve invalid checksums, declarations, flags, and odd prefixes."
        let translated := patch quote target
        let returned := patch translated (IPv4QuotePrefix.header quote)
        ensure (translated.flags == quote.flags && translated.declaredLength == 1 &&
            IPv4Quote.udpLength? translated.packet.payload == some 3 &&
            translated.packet.payload.drop 8 == [1, 2, 3] && translated.packet.payload.length == quote.packet.payload.length)
          "Prefix NAT must retain raw declarations, every flag bit, and the exact application prefix."
        ensure (IPv4QuotePrefix.header translated == target && translated.packet.tos == 7 &&
            translated.packet.identification == 0x1357 && translated.packet.ttl == 31 &&
            translated.packet.dontFragment == quote.packet.dontFragment)
          "Only the two quoted addresses, ports, and checksum residues may change."
        ensure (valid (IPv4QuotePrefix.headerBytes translated) == valid (IPv4QuotePrefix.headerBytes quote))
          "NAT must preserve a bad inner IPv4 checksum instead of repairing it."
        ensure ((sum (udpBytes translated)).val % 65535 == (sum (udpBytes quote)).val % 65535 &&
            !valid (udpBytes translated))
          "The invalid UDP checksum must be adjusted without becoming validated or repaired."
        ensure (returned.packet == quote.packet && returned.flags == quote.flags && returned.declaredLength == quote.declaredLength &&
            returned.checksum.val % 65535 == quote.checksum.val % 65535)
          "Reverse tuple translation must restore all packet bytes and the raw IPv4 checksum residue."
        let protocolTarget := { target with protocol := Packet.Protocol.tcp }
        ensure ((patch quote protocolTarget).packet.protocol == quote.packet.protocol)
          "A tuple target cannot change the quoted IP protocol."
  let omitted := { original with packet := { original.packet with
    payload := [0x30, 0x39, 0, 53, 0, 3, 0, 0, 1, 2, 3] } }
  ensure (quotedChecksum (patch omitted target).packet.payload == 0 &&
      (patch (patch omitted target) (IPv4QuotePrefix.header omitted)).packet == omitted.packet)
    "An omitted UDP checksum must remain exactly omitted through both translations."
  let zero := { original with checksum := 0 }
  ensure ((patch zero target).checksum != 0 &&
      (patch zero target).checksum == ChecksumRewriteRaw.update 0
        (addressTotal zero.packet.source zero.packet.destination) (addressTotal target.source target.destination))
    "The IPv4 zero checksum must use raw arithmetic while UDP zero retains its omission meaning."
  IO.println "Untrusted ICMP prefix NAT tests passed."

end NetlibTest.ICMPPrefixNAT
