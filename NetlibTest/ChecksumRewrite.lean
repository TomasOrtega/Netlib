import Netlib.Protocol.ChecksumRewrite

namespace NetlibTest.ChecksumRewrite

open Netlib Netlib.Protocol Netlib.Protocol.InternetChecksum Netlib.Protocol.ChecksumRewrite

example (checksum : Word) (removed added : Nat) :
    update (update checksum removed added) added removed = checksum :=
  update_inverse checksum removed added

example (checksum : Word) (removed added moreRemoved moreAdded : Nat) :
    update (update checksum removed added) moreRemoved moreAdded =
      update checksum (removed + moreRemoved) (added + moreAdded) :=
  update_compose checksum removed added moreRemoved moreAdded

example : update 0xdd2f 0x5555 0x3285 = 65535 := by decide
example : update 65535 0x3285 0x5555 = 0xdd2f := by decide
example : update 0 0x5555 0x3285 = 0 := by decide

example : udpTupleTotal 0xc0000201 0xc6336402 0x3039 0x35 =
    0xc000 + 0x0201 + 0xc633 + 0x6402 + 0x3039 + 0x35 := by decide

private def ensure (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def tuples : List (Packet.Address × Packet.Address × Word × Word) :=
  [(0xc0000201, 0xc6336402, 12345, 53), (0xcb007109, 0x0a000001, 0xabcd, 0x1234),
    (0, 0, 0, 0), (0xffffffff, 0xffffffff, 65535, 65535)]

private def udpTests : IO Unit := do
  for payload in ([[], [1], [1, 2], [1, 2, 3], [1, 2, 3, 4], [0x13, 0xa3],
      List.replicate 511 255, List.replicate 512 170] : List (List UInt8)) do
    for (oldSource, oldDestination, oldSourcePort, oldDestinationPort) in tuples do
      let old := UDP.computed oldSource oldDestination oldSourcePort oldDestinationPort payload
      for (newSource, newDestination, newSourcePort, newDestinationPort) in tuples do
        let removed := udpTupleTotal oldSource oldDestination oldSourcePort oldDestinationPort
        let added := udpTupleTotal newSource newDestination newSourcePort newDestinationPort
        let rewritten : UDP.Datagram :=
          ⟨newSourcePort, newDestinationPort, update old.checksum removed added, payload⟩
        let recomputed := UDP.computed newSource newDestination newSourcePort newDestinationPort payload
        ensure (rewritten == recomputed && rewritten.checksum != 0 &&
            InternetChecksum.valid (UDP.checksumBytes newSource newDestination rewritten))
          "Incremental address and port replacement must match full UDP checksum synthesis for odd and even payloads."
        ensure (update rewritten.checksum added removed == old.checksum)
          "Restoring both IPv4 addresses and UDP ports must recover the exact original checksum."
        let omitted := { old with checksum := 0 }
        let rewrittenOmitted : UDP.Datagram :=
          ⟨newSourcePort, newDestinationPort, update omitted.checksum removed added, payload⟩
        ensure (rewrittenOmitted.checksum == 0 && UDP.checksumAccepts newSource newDestination rewrittenOmitted)
          "Tuple changes must preserve an explicitly omitted UDP checksum."

def run : IO Unit := do
  ensure (update 0xdd2f 0x5555 0x3285 == 65535 && update 65535 0x3285 0x5555 == 0xdd2f)
    "The RFC1624 zero edge must transmit ffff and remain exactly reversible."
  for checksum in ([0, 1, 2, 32767, 32768, 65534, 65535] : List Word) do
    for (removed, added) in ([(0, 0), (0, 65535), (65535, 0), (65534, 1), (1, 65534),
        (6 * 65535, 6 * 65535 + 1), (1048576, 3141592)] : List (Nat × Nat)) do
      let rewritten := update checksum removed added
      ensure (update rewritten added removed == checksum && (rewritten == 0) == (checksum == 0))
        "Updates must preserve omission and all present values across repeated end-around carries."
      ensure (update checksum removed removed == checksum &&
          update rewritten 65536 131071 == update checksum (removed + 65536) (added + 131071))
        "Identity and composed rewrites must preserve the exact transmitted checksum representation."
  udpTests
  IO.println "Incremental checksum rewrite tests passed."

end NetlibTest.ChecksumRewrite
