import Netlib.Protocol.IPv4
import Netlib.Packet.Basic

/-!
# IPv4 UDP framing

RFC 768 defines the header and pseudoheader checksum.
Zero denotes omission; synthesis maps a computed zero to 65535.
The selected profile requires the UDP length to consume the entire IPv4 payload.
Ethernet padding remains outside that payload.
https://www.rfc-editor.org/rfc/rfc768
-/

namespace Netlib.Protocol.UDP

open InternetChecksum

structure Datagram where
  sourcePort : Word
  destinationPort : Word
  checksum : Word
  payload : List UInt8
  deriving Repr, BEq, DecidableEq

namespace Datagram

def wireLength (datagram : Datagram) : Nat := datagram.payload.length + 8

def Encodable (datagram : Datagram) : Prop := datagram.wireLength < 65536

instance (datagram : Datagram) : Decidable datagram.Encodable :=
  inferInstanceAs (Decidable (datagram.wireLength < 65536))

def lengthWord (datagram : Datagram) : Word :=
  ⟨datagram.wireLength % 65536, Nat.mod_lt _ (by decide)⟩

theorem lengthWord_val (datagram : Datagram) (bounded : datagram.Encodable) :
    datagram.lengthWord.val = datagram.wireLength := Nat.mod_eq_of_lt bounded

def encodeBytes (datagram : Datagram) : List UInt8 :=
  wordBytes datagram.sourcePort ++ wordBytes datagram.destinationPort ++ wordBytes datagram.lengthWord ++
    wordBytes datagram.checksum ++ datagram.payload

theorem encodeBytes_length (datagram : Datagram) : datagram.encodeBytes.length = datagram.wireLength := by
  simp [encodeBytes, wireLength]
  omega

end Datagram

def pseudoHeader (source destination : Packet.Address) (length : Word) : List UInt8 :=
  IPv4.addressBytes source ++ IPv4.addressBytes destination ++ [0, 17] ++ wordBytes length

theorem pseudoHeader_length (source destination : Packet.Address) (length : Word) :
    (pseudoHeader source destination length).length = 12 := by
  simp [pseudoHeader, IPv4.addressBytes]

def checksumPrefix (source destination : Packet.Address) (datagram : Datagram) : List UInt8 :=
  pseudoHeader source destination datagram.lengthWord ++ wordBytes datagram.sourcePort ++
    wordBytes datagram.destinationPort ++ wordBytes datagram.lengthWord

theorem checksumPrefix_length (source destination : Packet.Address) (datagram : Datagram) :
    (checksumPrefix source destination datagram).length = 18 := by
  simp [checksumPrefix, pseudoHeader_length]

def checksumBytes (source destination : Packet.Address) (datagram : Datagram) : List UInt8 :=
  checksumPrefix source destination datagram ++ wordBytes datagram.checksum ++ datagram.payload

theorem checksumBytes_eq (source destination : Packet.Address) (datagram : Datagram) :
    checksumBytes source destination datagram = pseudoHeader source destination datagram.lengthWord ++ datagram.encodeBytes := by
  simp [checksumBytes, checksumPrefix, Datagram.encodeBytes, List.append_assoc]

def checksumAccepts (source destination : Packet.Address) (datagram : Datagram) : Bool :=
  datagram.checksum == 0 || InternetChecksum.valid (checksumBytes source destination datagram)

def decode (source destination : Packet.Address) : List UInt8 → Except String Datagram
  | s0 :: s1 :: d0 :: d1 :: l0 :: l1 :: c0 :: c1 :: payload =>
    let datagram : Datagram := ⟨read16 s0 s1, read16 d0 d1, read16 c0 c1, payload⟩
    if (read16 l0 l1).val = datagram.wireLength then
      if checksumAccepts source destination datagram = true then .ok datagram
      else .error "The UDP pseudoheader checksum is invalid."
    else .error "The UDP length must equal the entire selected IPv4 payload."
  | _ => .error "A UDP datagram requires an eight-byte header."

def encode (source destination : Packet.Address) (datagram : Datagram) : Except String (List UInt8) :=
  if datagram.Encodable then
    if checksumAccepts source destination datagram = true then .ok datagram.encodeBytes
    else .error "The UDP pseudoheader checksum is invalid."
  else .error "The UDP datagram exceeds its 16-bit length field."

def computed (source destination : Packet.Address) (sourcePort destinationPort : Word) (payload : List UInt8) : Datagram :=
  let blank : Datagram := ⟨sourcePort, destinationPort, 0, payload⟩
  { blank with checksum := transmittedChecksum (checksumPrefix source destination blank ++ [0, 0] ++ payload) }

theorem computed_nonzero (source destination : Packet.Address) (sourcePort destinationPort : Word) (payload : List UInt8) :
    (computed source destination sourcePort destinationPort payload).checksum ≠ 0 := by
  unfold computed
  dsimp only
  exact transmittedChecksum_nonzero (checksumPrefix source destination ⟨sourcePort, destinationPort, 0, payload⟩ ++ [0, 0] ++ payload)

theorem computed_valid (source destination : Packet.Address) (sourcePort destinationPort : Word) (payload : List UInt8) :
    InternetChecksum.valid (checksumBytes source destination (computed source destination sourcePort destinationPort payload)) = true := by
  have synthesized := synthesize_nonzero_valid (checksumPrefix source destination ⟨sourcePort, destinationPort, 0, payload⟩) payload
    (by rw [checksumPrefix_length])
  simpa only [computed, checksumBytes, checksumPrefix, Datagram.lengthWord, Datagram.wireLength] using synthesized

theorem computed_accepts (source destination : Packet.Address) (sourcePort destinationPort : Word) (payload : List UInt8) :
    checksumAccepts source destination (computed source destination sourcePort destinationPort payload) = true := by
  simp [checksumAccepts, computed_valid]

def encodeComputed (source destination : Packet.Address) (sourcePort destinationPort : Word) (payload : List UInt8) :
    Except String (List UInt8) := encode source destination (computed source destination sourcePort destinationPort payload)

theorem encode_conditions (source destination : Packet.Address) (datagram : Datagram) (bytes : List UInt8)
    (encoded : encode source destination datagram = .ok bytes) :
    datagram.Encodable ∧ checksumAccepts source destination datagram = true ∧ bytes = datagram.encodeBytes := by
  unfold encode at encoded
  split at encoded
  · split at encoded
    · cases encoded
      exact ⟨by assumption, by assumption, rfl⟩
    · cases encoded
  · cases encoded

theorem decode_encodeBytes (source destination : Packet.Address) (datagram : Datagram)
    (bounded : datagram.Encodable) (checked : checksumAccepts source destination datagram = true) :
    decode source destination datagram.encodeBytes = .ok datagram := by
  simp only [Datagram.encodeBytes, wordBytes, List.cons_append, List.nil_append, decode, read16_bytes]
  rw [datagram.lengthWord_val bounded]
  simp only [ite_true]
  exact ite_eq_left checked

theorem decode_encode (source destination : Packet.Address) (datagram : Datagram) (bytes : List UInt8)
    (encoded : encode source destination datagram = .ok bytes) : decode source destination bytes = .ok datagram := by
  obtain ⟨bounded, checked, rfl⟩ := encode_conditions source destination datagram bytes encoded
  exact decode_encodeBytes source destination datagram bounded checked

theorem decode_fields (source destination : Packet.Address) (bytes : List UInt8) (datagram : Datagram)
    (accepted : decode source destination bytes = .ok datagram) :
    datagram.Encodable ∧ checksumAccepts source destination datagram = true ∧ datagram.encodeBytes = bytes := by
  unfold decode at accepted
  split at accepted
  · rename_i s0 s1 d0 d1 l0 l1 c0 c1 payload
    dsimp only at accepted
    split at accepted
    · rename_i correct
      split at accepted
      · rename_i checked
        cases accepted
        have bounded : (Datagram.mk (read16 s0 s1) (read16 d0 d1) (read16 c0 c1) payload).Encodable := by
          unfold Datagram.Encodable
          rw [← correct]
          exact (read16 l0 l1).isLt
        refine ⟨bounded, checked, ?_⟩
        have length : (Datagram.mk (read16 s0 s1) (read16 d0 d1) (read16 c0 c1) payload).lengthWord = read16 l0 l1 := by
          apply Fin.ext
          rw [Datagram.lengthWord_val _ bounded]
          exact correct.symm
        simp [Datagram.encodeBytes, length, wordBytes]
      · cases accepted
    · cases accepted
  · cases accepted

theorem encode_decode (source destination : Packet.Address) (bytes : List UInt8) (datagram : Datagram)
    (accepted : decode source destination bytes = .ok datagram) : encode source destination datagram = .ok bytes := by
  obtain ⟨bounded, checked, exactBytes⟩ := decode_fields source destination bytes datagram accepted
  simp [encode, bounded, checked, exactBytes]

theorem decode_checksum (source destination : Packet.Address) (bytes : List UInt8) (datagram : Datagram)
    (accepted : decode source destination bytes = .ok datagram) :
    datagram.checksum = 0 ∨ InternetChecksum.valid (pseudoHeader source destination datagram.lengthWord ++ bytes) = true := by
  have checked := (decode_fields source destination bytes datagram accepted).2.1
  rw [checksumAccepts, Bool.or_eq_true, beq_iff_eq, checksumBytes_eq,
    (decode_fields source destination bytes datagram accepted).2.2] at checked
  exact checked

theorem decode_verified (source destination : Packet.Address) (bytes : List UInt8) (datagram : Datagram)
    (accepted : decode source destination bytes = .ok datagram) (present : datagram.checksum ≠ 0) :
    InternetChecksum.valid (pseudoHeader source destination datagram.lengthWord ++ bytes) = true :=
  (decode_checksum source destination bytes datagram accepted).resolve_left present

theorem decode_length (source destination : Packet.Address) (bytes : List UInt8) (datagram : Datagram)
    (accepted : decode source destination bytes = .ok datagram) : bytes.length = datagram.wireLength := by
  rw [← (decode_fields source destination bytes datagram accepted).2.2]
  exact datagram.encodeBytes_length

structure DecodedIPv4 where
  ip : IPv4.Decoded
  datagram : Datagram
  deriving Repr, BEq, DecidableEq

def DecodedIPv4.header (value : DecodedIPv4) : Packet.Header :=
  ⟨value.ip.packet.source, value.ip.packet.destination, Packet.Protocol.udp,
    value.datagram.sourcePort, value.datagram.destinationPort⟩

def DecodedIPv4.Valid (value : DecodedIPv4) : Prop :=
  value.ip.packet.protocol = Packet.Protocol.udp ∧
    decode value.ip.packet.source value.ip.packet.destination value.ip.packet.payload = .ok value.datagram

instance (value : DecodedIPv4) : Decidable value.Valid := by
  unfold DecodedIPv4.Valid
  cases decode value.ip.packet.source value.ip.packet.destination value.ip.packet.payload with
  | error error => simp; infer_instance
  | ok datagram => simp only [Except.ok.injEq]; infer_instance

def decodeIPv4 (bytes : List UInt8) : Except String DecodedIPv4 := do
  let ip ← IPv4.decode bytes
  if ip.packet.protocol != Packet.Protocol.udp then throw "The IPv4 protocol must be UDP."
  let datagram ← decode ip.packet.source ip.packet.destination ip.packet.payload
  return ⟨ip, datagram⟩

def encodeIPv4 (value : DecodedIPv4) : Except String (List UInt8) :=
  if value.Valid then IPv4.encodeDecoded value.ip
  else .error "The decoded UDP datagram must agree with the IPv4 fields and complete payload."

theorem decodeIPv4_layers (bytes : List UInt8) (value : DecodedIPv4)
    (accepted : decodeIPv4 bytes = .ok value) :
    IPv4.decode bytes = .ok value.ip ∧ value.Valid := by
  cases ip : IPv4.decode bytes with
  | error error => simp [decodeIPv4, ip, bind, Except.bind] at accepted
  | ok decoded =>
    simp only [decodeIPv4, ip, bind, Except.bind] at accepted
    split at accepted
    · simp [throw] at accepted
    · rename_i protocol
      cases transport : decode decoded.packet.source decoded.packet.destination decoded.packet.payload with
      | error error => simp [transport] at accepted
      | ok datagram =>
        simp [transport, pure] at accepted
        cases accepted
        exact ⟨rfl, by simpa [DecodedIPv4.Valid] using And.intro protocol transport⟩

theorem decodeIPv4_header (bytes : List UInt8) (value : DecodedIPv4)
    (accepted : decodeIPv4 bytes = .ok value) :
    value.header = ⟨value.ip.packet.source, value.ip.packet.destination, value.ip.packet.protocol,
      value.datagram.sourcePort, value.datagram.destinationPort⟩ := by
  simp [DecodedIPv4.header, (decodeIPv4_layers bytes value accepted).2.1]

theorem encodeIPv4_decodeIPv4 (bytes : List UInt8) (value : DecodedIPv4)
    (accepted : decodeIPv4 bytes = .ok value) : encodeIPv4 value = .ok bytes := by
  obtain ⟨ip, coherent⟩ := decodeIPv4_layers bytes value accepted
  rw [encodeIPv4, ite_eq_left coherent]
  exact IPv4.encode_decode bytes value.ip ip

theorem decodeIPv4_encodeIPv4 (value : DecodedIPv4) (bytes : List UInt8)
    (encoded : encodeIPv4 value = .ok bytes) : decodeIPv4 bytes = .ok value := by
  unfold encodeIPv4 at encoded
  split at encoded
  · rename_i coherent
    have ip := IPv4.decode_encodeDecoded value.ip bytes encoded
    have protocol := coherent.1
    simp [decodeIPv4, ip, protocol, coherent.2, bind, Except.bind, pure]
    rfl
  · cases encoded

end Netlib.Protocol.UDP
