import Netlib.Protocol.TCP.Output

namespace NetlibTest.TCPOutput

open Netlib Protocol TCP

private def ensure (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def load : Except String α → IO α
  | .ok value => pure value
  | .error reason => throw (IO.userError reason)

private def seed : EstablishedReceive.State :=
  ⟨⟨3221225985, 3325256706, Packet.Protocol.tcp, 41000, 80⟩,
    Seq.ofNat 4294967295, 8, [10, 11], Seq.ofNat 99, Seq.ofNat 100, [12]⟩

def run : IO Unit := do
  let payload : List UInt8 := [0, 1, 255]
  let value ← load (Output.emit seed payload)
  let decoded ← load (EstablishedReceive.input value.bytes)
  ensure (decoded.packet == value.packet && value.packet.header == Output.reverse seed.inbound)
    "Output bytes must decode with the reverse endpoint tuple."
  let segment := value.packet.segment
  ensure (segment.payload == payload && segment.sequence == seed.sendNext &&
    segment.acknowledgment == seed.receiveNext && segment.window.val == 6 &&
    segment.flags == 16 && segment.reserved == 0 && segment.options.isEmpty && segment.urgentPointer == 0)
    "Output must use the current cursors, free receive space, and selected ACK fields."
  ensure (value.bytes.length == 43 && value.packet.ip.padding.isEmpty &&
    checksumAccepts value.packet.ip.packet.source value.packet.ip.packet.destination segment)
    "The output length and mandatory checksum must include the exact payload."
  let maximum ← load (Output.emit seed (List.replicate 65495 7))
  ensure (maximum.bytes.length == 65535) "The largest output must fit the IPv4 length field."
  match Output.emit seed (List.replicate 65496 7) with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "An output above the IPv4 size limit must fail.")
  match Output.emit { seed with capacity := 1 } [] with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "An invalid seed must not produce output bytes.")
  IO.println "TCP output tests passed."

end NetlibTest.TCPOutput
