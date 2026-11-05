import Netlib.Protocol.TCP.Options

namespace NetlibTest.TCPOptions

open Netlib.Protocol

private def ensure (value : Bool) (message : String) : IO Unit := do
  unless value do throw (IO.userError message)

def run : IO Unit := do
  for options in [[], [0], [0, 0, 0, 0], [1], [1, 1, 1, 1], [2, 4, 5, 180],
      [1, 2, 4, 5, 180, 0, 0, 0], [253, 2], [254, 4, 170, 187], [3, 2, 0, 0]] do
    ensure (TCP.Options.valid options) "Well-framed known, unknown, and unaligned options must be accepted."
  for options in [[0, 1], [253], [253, 0], [253, 1], [253, 4, 1], [2, 2], [2, 3, 0], [2, 5, 0, 0, 0]] do
    ensure (!TCP.Options.valid options) "Invalid lengths, truncated TLVs, MSS lengths, and nonzero EOL padding must reject."
  let options := [1, 2, 4, 5, 180, 0, 0, 0]
  ensure (TCP.Options.maximumSegmentSizes options == [1460]) "MSS recognition must respect unaligned option boundaries."
  ensure (TCP.Options.valid options && !TCP.Options.synCompatible 16 options && TCP.Options.synCompatible 2 options)
    "MSS framing and SYN placement are separate checks."
  ensure (TCP.Options.synCompatible 16 [253, 4, 2, 4]) "Bytes inside an unknown TLV are not independent MSS options."
  ensure (TCP.Options.maximumSegmentSizes [0, 0, 0, 0] == []) "Padding after EOL is not interpreted as more options."

end NetlibTest.TCPOptions
