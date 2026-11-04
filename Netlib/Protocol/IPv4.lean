import Netlib.Protocol.InternetChecksum
import Netlib.Packet.Basic

/-!
# Unfragmented IPv4 wire packets

The profile selects version 4 with IHL 5, preserves DF, and excludes other flags
and fragment offsets. Trailing link padding is separate from the IP payload.
-/

namespace Netlib.Protocol.IPv4

open InternetChecksum

def highWord (address : Netlib.Packet.Address) : Word :=
  ⟨address.val / 65536, by have := address.isLt; omega⟩

def lowWord (address : Netlib.Packet.Address) : Word :=
  ⟨address.val % 65536, Nat.mod_lt _ (by decide)⟩

def addressBytes (address : Netlib.Packet.Address) : List UInt8 :=
  wordBytes (highWord address) ++ wordBytes (lowWord address)

def readAddress (a b c d : UInt8) : Netlib.Packet.Address :=
  ⟨(read16 a b).val * 65536 + (read16 c d).val, by
    have := (read16 a b).isLt
    have := (read16 c d).isLt
    omega⟩

@[simp] theorem addressBytes_length (address : Netlib.Packet.Address) : (addressBytes address).length = 4 := by
  simp [addressBytes]

theorem readAddress_bytes (address : Netlib.Packet.Address) :
    readAddress (highByte (highWord address)) (lowByte (highWord address))
      (highByte (lowWord address)) (lowByte (lowWord address)) = address := by
  apply Fin.ext
  simp only [readAddress, read16_bytes, highWord, lowWord]
  omega

theorem addressBytes_readAddress (a b c d : UInt8) : addressBytes (readAddress a b c d) = [a, b, c, d] := by
  have high : highWord (readAddress a b c d) = read16 a b := by
    apply Fin.ext
    have lower := (read16 c d).isLt
    change ((read16 a b).val * 65536 + (read16 c d).val) / 65536 = (read16 a b).val
    omega
  have low : lowWord (readAddress a b c d) = read16 c d := by
    apply Fin.ext
    have lower := (read16 c d).isLt
    change ((read16 a b).val * 65536 + (read16 c d).val) % 65536 = (read16 c d).val
    omega
  simp [addressBytes, high, low, wordBytes]

structure Packet where
  tos : UInt8
  identification : Word
  dontFragment : Bool
  ttl : UInt8
  protocol : Netlib.Packet.Protocol
  source : Netlib.Packet.Address
  destination : Netlib.Packet.Address
  payload : List UInt8
  deriving Repr, BEq, DecidableEq

def Packet.wireLength (packet : Packet) : Nat := packet.payload.length + 20

def Packet.Encodable (packet : Packet) : Prop := packet.wireLength < 65536

instance (packet : Packet) : Decidable packet.Encodable := inferInstanceAs (Decidable (packet.wireLength < 65536))

structure Decoded where
  packet : Packet
  checksum : Word
  padding : List UInt8
  deriving Repr, BEq, DecidableEq

def lengthWord (packet : Packet) : Word := ⟨packet.wireLength % 65536, Nat.mod_lt _ (by decide)⟩

def protocolFromByte (value : UInt8) : Netlib.Packet.Protocol := ⟨value.toNat, value.toNat_lt⟩

theorem protocolFromByte_encode (value : Netlib.Packet.Protocol) :
    protocolFromByte (UInt8.ofNat value.val) = value := by
  apply Fin.ext
  simp [protocolFromByte]

@[simp] theorem protocolFromByte_bytes (value : UInt8) : UInt8.ofNat (protocolFromByte value).val = value := by
  simp [protocolFromByte]

def headerPrefix (packet : Packet) : List UInt8 :=
  [69, packet.tos] ++ wordBytes (lengthWord packet) ++ wordBytes packet.identification ++
    [if packet.dontFragment then 64 else 0, 0, packet.ttl, UInt8.ofNat packet.protocol.val]

def headerSuffix (packet : Packet) : List UInt8 := addressBytes packet.source ++ addressBytes packet.destination

def headerBytes (packet : Packet) (checksum : Word) : List UInt8 :=
  headerPrefix packet ++ wordBytes checksum ++ headerSuffix packet

@[simp] theorem headerPrefix_length (packet : Packet) : (headerPrefix packet).length = 10 := by
  simp [headerPrefix]

@[simp] theorem headerSuffix_length (packet : Packet) : (headerSuffix packet).length = 8 := by
  simp [headerSuffix]

@[simp] theorem headerBytes_length (packet : Packet) (checksum : Word) : (headerBytes packet checksum).length = 20 := by
  simp [headerBytes]

def computedChecksum (packet : Packet) : Word := InternetChecksum.checksum (headerBytes packet 0)

theorem computedChecksum_valid (packet : Packet) : valid (headerBytes packet (computedChecksum packet)) = true := by
  simpa only [computedChecksum, headerBytes, wordBytes_zero] using
    synthesize_valid (headerPrefix packet) (headerSuffix packet) (by simp)

def encode (packet : Packet) : Except String (List UInt8) :=
  if packet.Encodable then .ok (headerBytes packet (computedChecksum packet) ++ packet.payload)
  else .error "The IPv4 packet exceeds its 16-bit total length."

def encodeDecoded (value : Decoded) : Except String (List UInt8) := do
  if !decide value.packet.Encodable then throw "The IPv4 packet exceeds its 16-bit total length."
  if !valid (headerBytes value.packet value.checksum) then throw "The IPv4 header checksum is invalid."
  return headerBytes value.packet value.checksum ++ value.packet.payload ++ value.padding

def decode : List UInt8 → Except String Decoded
  | version :: tos :: lh :: ll :: ih :: il :: fh :: fl :: ttl :: protocol :: ch :: cl ::
      sa :: sb :: sc :: sd :: da :: db :: dc :: dd :: rest => do
    if version != 69 then throw "Require IPv4 version 4 and IHL 5."
    let declared := (read16 lh ll).val
    if declared < 20 then throw "The IPv4 total length is shorter than its header."
    if rest.length < declared - 20 then throw "The IPv4 total length exceeds the received bytes."
    if fl != 0 || (fh != 0 && fh != 64) then throw "IPv4 fragmentation and reserved flags are unsupported."
    let header := [version, tos, lh, ll, ih, il, fh, fl, ttl, protocol, ch, cl, sa, sb, sc, sd, da, db, dc, dd]
    if !valid header then throw "The IPv4 header checksum is invalid."
    let packet : Packet := ⟨tos, read16 ih il, fh == 64, ttl, protocolFromByte protocol,
      readAddress sa sb sc sd, readAddress da db dc dd, rest.take (declared - 20)⟩
    return ⟨packet, read16 ch cl, rest.drop (declared - 20)⟩
  | _ => .error "An IPv4 header requires twenty bytes."

theorem decode_headerBytes (packet : Packet) (checksum : Word) (padding : List UInt8)
    (bounded : packet.Encodable) (checked : valid (headerBytes packet checksum) = true) :
    decode (headerBytes packet checksum ++ packet.payload ++ padding) = .ok ⟨packet, checksum, padding⟩ := by
  have length : (lengthWord packet).val = packet.wireLength := Nat.mod_eq_of_lt bounded
  have minimum : ¬packet.wireLength < 20 := by unfold Packet.wireLength; omega
  have available : ¬(packet.payload ++ padding).length < packet.wireLength - 20 := by
    simp only [List.length_append, Packet.wireLength]
    omega
  simp only [headerBytes, headerPrefix, headerSuffix, addressBytes, wordBytes,
    List.cons_append, List.nil_append, decode, read16_bytes, readAddress_bytes,
    protocolFromByte_encode, length]
  rw [ite_eq_right minimum, ite_eq_right available]
  cases fragment : packet.dontFragment
  all_goals
    have headerValid : valid (headerBytes packet checksum) = true := checked
    simp [headerBytes, headerPrefix, headerSuffix, addressBytes, wordBytes, fragment] at headerValid
    simp [headerValid, Packet.wireLength]
    congr 1
    cases packet
    cases fragment
    rfl

theorem decode_encode (packet : Packet) (bytes : List UInt8) (encoded : encode packet = .ok bytes) :
    decode bytes = .ok ⟨packet, computedChecksum packet, []⟩ := by
  unfold encode at encoded
  split at encoded
  · cases encoded
    simpa using decode_headerBytes packet (computedChecksum packet) [] (by assumption) (computedChecksum_valid packet)
  · cases encoded

theorem decode_encodeDecoded (value : Decoded) (bytes : List UInt8)
    (encoded : encodeDecoded value = .ok bytes) : decode bytes = .ok value := by
  unfold encodeDecoded at encoded
  by_cases bounded : value.packet.Encodable
  · by_cases checked : valid (headerBytes value.packet value.checksum) = true
    · simp [bounded, checked, pure] at encoded
      cases encoded
      exact decode_headerBytes value.packet value.checksum value.padding bounded checked
    · simp [bounded, checked, bind, Except.bind, throw] at encoded
  · simp [bounded, bind, Except.bind, throw] at encoded

private theorem encode_decode_header (tos lh ll ih il fh fl ttl protocol ch cl sa sb sc sd da db dc dd : UInt8)
    (rest : List UInt8) (value : Decoded)
    (accepted : decode (69 :: tos :: lh :: ll :: ih :: il :: fh :: fl :: ttl :: protocol :: ch :: cl ::
      sa :: sb :: sc :: sd :: da :: db :: dc :: dd :: rest) = .ok value) :
    encodeDecoded value = .ok (69 :: tos :: lh :: ll :: ih :: il :: fh :: fl :: ttl :: protocol :: ch :: cl ::
      sa :: sb :: sc :: sd :: da :: db :: dc :: dd :: rest) := by
  by_cases short : (read16 lh ll).val < 20
  · simp [decode, short, bind, Except.bind, throw] at accepted
  · by_cases truncated : rest.length < (read16 lh ll).val - 20
    · simp [decode, short, truncated, bind, Except.bind, throw] at accepted
    · by_cases flagLow : fl = 0
      · have flags : (if fh == 64 then (64 : UInt8) else 0) = fh := by
          by_cases clear : fh = 0
          · simp [clear]
          · by_cases df : fh = 64
            · simp [df]
            · simp [decode, short, truncated, flagLow, clear, df, bind, Except.bind, throw] at accepted
        let parsed : Packet := ⟨tos, read16 ih il, fh == 64, ttl, protocolFromByte protocol,
          readAddress sa sb sc sd, readAddress da db dc dd, rest.take ((read16 lh ll).val - 20)⟩
        have length : parsed.wireLength = (read16 lh ll).val := by
          simp only [parsed, Packet.wireLength, List.length_take]
          omega
        have bounded : parsed.Encodable := by
          rw [Packet.Encodable, length]
          exact (read16 lh ll).isLt
        have lengthSame : lengthWord parsed = read16 lh ll := by
          apply Fin.ext
          change parsed.wireLength % 65536 = (read16 lh ll).val
          rw [Nat.mod_eq_of_lt bounded, length]
        have headerSame : headerBytes parsed (read16 ch cl) =
            [69, tos, lh, ll, ih, il, fh, fl, ttl, protocol, ch, cl, sa, sb, sc, sd, da, db, dc, dd] := by
          unfold headerBytes headerPrefix headerSuffix
          rw [lengthSame]
          simp only [parsed, flags, wordBytes, highByte_read16, lowByte_read16,
            addressBytes_readAddress, protocolFromByte_bytes, flagLow]
          rfl
        by_cases checked : valid (headerBytes parsed (read16 ch cl)) = true
        · have flagGuard : (fl != 0 || (fh != 0 && fh != 64)) = false := by
            by_cases clear : fh = 0
            · simp [flagLow, clear]
            · have df : fh = 64 := by
                by_cases df : fh = 64
                · exact df
                · simp [df] at flags
                  exact False.elim (clear flags.symm)
              simp [flagLow, df]
          have headerChecked := checked
          rw [headerSame] at headerChecked
          simp only [decode, short, truncated, flagGuard, Bool.false_eq_true, ite_false,
            headerChecked, Bool.not_true, bind, Except.bind, pure] at accepted
          cases accepted
          change encodeDecoded ⟨parsed, read16 ch cl, rest.drop ((read16 lh ll).val - 20)⟩ = _
          simp only [encodeDecoded, bounded, decide_true, Bool.not_true, Bool.false_eq_true, ite_false,
            checked, bind, Except.bind, pure]
          apply congrArg Except.ok
          rw [headerSame, List.append_assoc, List.take_append_drop]
          rfl
        · have headerRejected : valid [69, tos, lh, ll, ih, il, fh, fl, ttl, protocol,
              ch, cl, sa, sb, sc, sd, da, db, dc, dd] = false := by
            rw [← headerSame]
            exact Bool.eq_false_iff.mpr checked
          simp [decode, short, truncated, headerRejected, bind, Except.bind, throw] at accepted
          split at accepted <;> cases accepted
      · simp [decode, short, truncated, flagLow, bind, Except.bind, throw] at accepted

theorem encode_decode (bytes : List UInt8) (value : Decoded) (accepted : decode bytes = .ok value) :
    encodeDecoded value = .ok bytes := by
  unfold decode at accepted
  split at accepted
  · rename_i version tos lh ll ih il fh fl ttl protocol ch cl sa sb sc sd da db dc dd rest
    by_cases selected : version = 69
    · subst version
      apply encode_decode_header tos lh ll ih il fh fl ttl protocol ch cl sa sb sc sd da db dc dd rest value
      exact accepted
    · simp [selected, bind, Except.bind, throw] at accepted
  · cases accepted

theorem encodeDecoded_valid (value : Decoded) (bytes : List UInt8) (encoded : encodeDecoded value = .ok bytes) :
    value.packet.Encodable ∧ valid (headerBytes value.packet value.checksum) = true := by
  by_cases bounded : value.packet.Encodable
  · by_cases checked : valid (headerBytes value.packet value.checksum) = true
    · exact ⟨bounded, checked⟩
    · simp [encodeDecoded, bounded, checked, bind, Except.bind, throw] at encoded
  · simp [encodeDecoded, bounded, bind, Except.bind, throw] at encoded

theorem decode_valid (bytes : List UInt8) (value : Decoded) (accepted : decode bytes = .ok value) :
    value.packet.Encodable ∧ valid (headerBytes value.packet value.checksum) = true :=
  encodeDecoded_valid value bytes (encode_decode bytes value accepted)

end Netlib.Protocol.IPv4
