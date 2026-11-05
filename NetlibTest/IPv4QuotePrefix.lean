import Netlib.Protocol.IPv4QuotePrefix

namespace NetlibTest.IPv4QuotePrefix

open Netlib Protocol InternetChecksum

private def ensure (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def unwrap (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

private def reject (result : Except String α) (message : String) : IO Unit :=
  match result with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError message)

def run : IO Unit := do
  for flags in ([0, 16384, 8192, 32768, 57344, 65535] : List Word) do
    for protocol in ([1, 6, 17, 255] : List Packet.Protocol) do
      let quote : IPv4QuotePrefix.Decoded :=
        ⟨⟨255, 1234, IPv4QuotePrefix.flagsDF flags, 0, protocol, 3221225986, 3405803778,
          [160, 40, 35, 40, 0, 1, 18, 52, 99]⟩, flags, 0, 0⟩
      let bytes := IPv4QuotePrefix.bytes quote
      let parsed ← unwrap (IPv4QuotePrefix.decode bytes)
      ensure (parsed == quote && (← unwrap (IPv4QuotePrefix.encodeDecoded parsed)) == bytes)
        "Raw quotations must preserve invalid declarations, checksums, flags, and protocol bytes exactly."
      ensure (parsed.declaredLength == 0 && parsed.packet.payload.length == 9 &&
          IPv4QuotePrefix.offset parsed == flags.val % 8192 &&
          (IPv4QuotePrefix.header parsed).sourcePort == 41000)
        "Tuple extraction must not substitute original-length or checksum validation."
      reject (IPv4QuotePrefix.decode (bytes.take 27)) "A selected NAT quote requires all eight UDP header bytes."
      reject (IPv4QuotePrefix.decode (bytes.modifyHead (fun _ => 70))) "IP options require a different quotation profile."
      reject (IPv4QuotePrefix.decode (bytes.modifyHead (fun _ => 101))) "Reject a non-IPv4 quotation."
  IO.println "Untrusted IPv4 quotation prefix tests passed."

end NetlibTest.IPv4QuotePrefix
