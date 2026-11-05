import Netlib.Packet.IPv4Envelope
import Netlib.Protocol.UDP

namespace NetlibTest.IPv4Envelope

open Netlib Packet Protocol

private def ensure (value : Bool) (message : String) : IO Unit := do
  unless value do throw (IO.userError message)

private def load : Except String α → IO α
  | .ok value => pure value
  | .error message => throw (IO.userError message)

private def failed : Except String α → Bool
  | .error _ => true
  | .ok _ => false

private def base : IPv4.Packet := ⟨187, 4137, false, 63, 17, 3221225986, 3405803778, []⟩

example (traffic : Match) (first second : Header) (same : Packet.IPv4Envelope.ofHeader first = Packet.IPv4Envelope.ofHeader second) :
    traffic.erasePorts.accepts first = traffic.erasePorts.accepts second := traffic.erasePorts_sameEnvelope first second same

example (bytes : List UInt8) (envelope : Packet.IPv4Envelope) (accepted : Packet.IPv4Envelope.decode bytes = .ok envelope) :
    ∃ fragment, IPv4InputFragment.decode bytes = .ok fragment ∧ Packet.IPv4Envelope.ofFragment fragment = envelope :=
  Packet.IPv4Envelope.decode_source bytes envelope accepted

def run : IO Unit := do
  for direction in [false, true] do
    for protocol in ([0, 1, 6, 17, 255] : List Packet.Protocol) do
      for offset in ([0, 1, 8191] : List (Fin 8192)) do
        for payload in [[], [0], [255, 255, 0, 1], List.replicate 11 91] do
          let packet : IPv4Fragment.Packet := ⟨{ base with
            source := if direction then base.destination else base.source
            destination := if direction then base.source else base.destination
            protocol, dontFragment := true, payload }, true, offset⟩
          let bytes ← load (IPv4InputFragment.encode packet)
          let envelope ← load (Packet.IPv4Envelope.decode (bytes ++ [91, 92]))
          ensure (envelope == Packet.IPv4Envelope.ofPacket packet.toPacket &&
            envelope.toHeader.sourcePort == 0 && envelope.toHeader.destinationPort == 0)
            "Envelope selection must preserve only source, destination, and protocol, regardless of flags, offset, payload, or padding."
  let later : IPv4Fragment.Packet := ⟨{ base with payload := [255, 255, 0, 1] }, false, 1⟩
  let bytes ← load (IPv4InputFragment.encode later)
  ensure (failed (UDP.decodeIPv4 bytes) && !(failed (Packet.IPv4Envelope.decode bytes)))
    "A noninitial fragment without a UDP header must still have a validated IPv4 envelope."
  ensure (failed (Packet.IPv4Envelope.decode (bytes.take 19)) &&
    failed (Packet.IPv4Envelope.decode (bytes.take (bytes.length - 1))))
    "Incomplete IPv4 framing must not produce an envelope."
  for position in [0, 2, 6, 10, 12] do
    let replacement : UInt8 := if position == 0 then 70 else if position == 2 then 255 else 128
    let malformed := bytes.take position ++ [replacement] ++ bytes.drop (position + 1)
    ensure (failed (Packet.IPv4Envelope.decode malformed))
      "Unsupported header shape, reserved flags, invalid lengths, and checksum corruption must reject before selection."
  let header : Header := ⟨base.source, base.destination, Packet.Protocol.udp, 41000, 8080⟩
  let traffic : Match := {
    source := some ⟨base.source, 32⟩, protocol := some Packet.Protocol.udp,
    sourcePorts := some (PortRange.single 41000), destinationPorts := some (PortRange.single 8080) }
  ensure (traffic.accepts header && !traffic.accepts { header with sourcePort := 9 } &&
    traffic.erasePorts.accepts { header with sourcePort := 9, destinationPort := 1 })
    "Coarse selection intentionally forgets ports and cannot certify the completed UDP tuple."

end NetlibTest.IPv4Envelope
