import Netlib.Import.PacketFields

namespace NetlibTest.PacketFields

open Netlib

private def unwrap (value : Except String α) : IO α :=
  match value with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

private def ensure (value : Bool) (message : String) : IO Unit :=
  unless value do throw (IO.userError message)

def run : IO Unit := do
  for packet in ([⟨0, 4294967295, 255, 0, 65535⟩,
      ⟨167772161, 3325256714, 6, 50000, 443⟩,
      ⟨4294967295, 0, 17, 65535, 0⟩] : List Packet.Header) do
    let decoded ← unwrap (Import.PacketFields.header (Import.PacketFields.headerJson packet))
    ensure (decoded == packet) "The packet-field JSON roundtrip changed a header."
    let endpoint := packet.sourceEndpoint
    let decoded ← unwrap (Import.PacketFields.endpoint (Import.PacketFields.endpointJson endpoint))
    ensure (decoded == endpoint) "The endpoint JSON roundtrip changed a value."
  let text := (Import.PacketFields.headerJson (⟨0, 4294967295, 6, 1000, 443⟩ : Packet.Header)).compress
  for invalid in [text.replace "\"protocol\":6" "\"protocol\":256",
      text.replace "\"sourcePort\":1000" "\"sourcePort\":65536",
      text.replace "\"destinationPort\":443" "\"destinationPort\":-1",
      text.replace "0.0.0.0" "0.0.0.256",
      text.replace "255.255.255.255" "::1",
      text.replace "\"protocol\":6" "\"protocol\":6,\"unknown\":true"] do
    ensure (invalid != text) "A packet-field mutation missed its input."
    let json ← unwrap (Import.Json.parse invalid)
    match Import.PacketFields.header json with
    | .error _ => pure ()
    | .ok _ => throw (IO.userError "An invalid packet field was accepted.")
  ensure (Import.PacketFields.optionalHeaderJson none == .null) "A dropped packet changed encoding."
  IO.println "Packet-field input tests passed."

end NetlibTest.PacketFields
