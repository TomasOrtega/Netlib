import Netlib.Import.EthernetIPv4

namespace NetlibTest.EthernetIPv4

open Netlib.Import

private def ensure (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def agrees [BEq α] (result : Except String α) (expected : α) : Bool :=
  match result with
  | .ok value => value == expected
  | .error _ => false

private def rejected : Except String α → Bool
  | .ok _ => false
  | .error _ => true

def run : IO Unit := do
  let frame : EthernetIPv4.Envelope := ⟨⟨0, 1, 2, 3, 4, 5⟩, ⟨6, 7, 8, 9, 10, 11⟩, [69, 0, 0, 20, 255]⟩
  let encoded := EthernetIPv4.encode frame
  ensure (agrees (EthernetIPv4.decode encoded) frame) "An IPv4 envelope must preserve every payload byte."
  ensure (agrees (EthernetIPv4.parseHex (EAPOL.bytesToHex encoded)) frame) "Hex parsing must preserve the envelope."
  for size in List.range 14 do
    ensure (rejected (EthernetIPv4.decode (encoded.take size))) "Truncated Ethernet headers must fail."
  let tagged := frame.destination.bytes ++ frame.source.bytes ++ [129, 0, 0, 1, 8, 0] ++ frame.payload
  ensure (rejected (EthernetIPv4.decode tagged)) "Tagged Ethernet is outside this envelope profile."
  ensure (rejected (EthernetIPv4.parseHex "0") && rejected (EthernetIPv4.parseHex "gg"))
    "Malformed hexadecimal input must fail."
  IO.println "Ethernet IPv4 capture envelope tests passed."

end NetlibTest.EthernetIPv4
