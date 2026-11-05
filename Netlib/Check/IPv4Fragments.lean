import Netlib.Protocol.IPv4Fragmentation
import Netlib.Protocol.UDP
import Netlib.Import.EthernetIPv4

/-!
# Checked fragment families

Every Ethernet payload is checked as an IPv4 fragment. UDP is checked after strict
reassembly. Family comparison ignores capture order, Ethernet adjacency, padding,
and the two valid IPv4 checksum zero representations.
-/

namespace Netlib.Check.IPv4Fragments

open Protocol

structure Checked (bytes : List UInt8) where
  envelope : Import.EthernetIPv4.Envelope
  fragment : IPv4Fragment.Decoded
  ethernet : Import.EthernetIPv4.decode bytes = .ok envelope
  ipv4 : IPv4Fragment.decode envelope.payload = .ok fragment

def checkBytes (bytes : List UInt8) : Except String (Checked bytes) := do
  match ethernet : Import.EthernetIPv4.decode bytes with
  | .error error => throw error
  | .ok envelope =>
    match ipv4 : IPv4Fragment.decode envelope.payload with
    | .error error => throw error
    | .ok fragment => return ⟨envelope, fragment, ethernet, ipv4⟩

structure WireFragment where
  bytes : List UInt8
  checked : Checked bytes

def normalize (packets : List IPv4Fragment.Packet) : List IPv4Fragment.Packet :=
  packets.mergeSort (fun first second => first.offset.val ≤ second.offset.val)

abbrev Value := List IPv4Fragment.Packet × (IPv4.Packet × UDP.Datagram)

structure Family where
  fragments : List WireFragment
  packet : IPv4.Packet
  datagram : UDP.Datagram
  reassembled : IPv4Fragmentation.reassemble (fragments.map (·.checked.fragment)) = .ok packet
  protocol : packet.protocol = 17
  transport : UDP.decode packet.source packet.destination packet.payload = .ok datagram

def Family.value (family : Family) : Value :=
  (normalize (family.fragments.map (·.checked.fragment.packet)), family.packet, family.datagram)

def checkFamily (bytes : List (List UInt8)) : Except String Family := do
  let fragments ← bytes.mapM fun bytes => do return (⟨bytes, ← checkBytes bytes⟩ : WireFragment)
  match recovered : IPv4Fragmentation.reassemble (fragments.map (·.checked.fragment)) with
  | .error error => throw error
  | .ok packet =>
    if protocol : packet.protocol = 17 then
      match transport : UDP.decode packet.source packet.destination packet.payload with
      | .error error => throw error
      | .ok datagram => return ⟨fragments, packet, datagram, recovered, protocol, transport⟩
    else throw "The reassembled IPv4 packet must carry UDP."

end Netlib.Check.IPv4Fragments
