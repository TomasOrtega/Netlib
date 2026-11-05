import Netlib.Protocol.IPv4Quote

/-!
# Untrusted IPv4 transport quotations

This parser preserves inner checksums, declared lengths, and every flag bit.
Those fields are data, rather than evidence of a valid original datagram.
The selected shape is IHL five with at least eight quoted transport bytes.
-/

namespace Netlib.Protocol.IPv4QuotePrefix

open InternetChecksum

def flagsDF (flags : Word) : Bool := decide (flags.val / 16384 % 2 = 1)

structure Decoded where
  packet : IPv4.Packet
  flags : Word
  checksum : Word
  declaredLength : Word
  deriving Repr, BEq, DecidableEq

def Decoded.Shape (value : Decoded) : Prop :=
  8 ≤ value.packet.payload.length ∧ value.packet.dontFragment = flagsDF value.flags

instance (value : Decoded) : Decidable value.Shape := by unfold Decoded.Shape; infer_instance

def headerPrefix (value : Decoded) : List UInt8 :=
  [69, value.packet.tos] ++ wordBytes value.declaredLength ++ wordBytes value.packet.identification ++
    wordBytes value.flags ++ [value.packet.ttl, UInt8.ofNat value.packet.protocol.val]

def headerBytes (value : Decoded) : List UInt8 :=
  headerPrefix value ++ wordBytes value.checksum ++ IPv4.headerSuffix value.packet

@[simp] theorem headerPrefix_length (value : Decoded) : (headerPrefix value).length = 10 := by simp [headerPrefix]
@[simp] theorem headerBytes_length (value : Decoded) : (headerBytes value).length = 20 := by simp [headerBytes]

def bytes (value : Decoded) : List UInt8 := headerBytes value ++ value.packet.payload

def header (value : Decoded) : Packet.Header :=
  IPv4Quote.header ⟨value.packet, value.checksum, value.declaredLength⟩

def offset (value : Decoded) : Nat := value.flags.val % 8192

def encodeDecoded (value : Decoded) : Except String (List UInt8) :=
  if value.Shape then .ok (bytes value) else .error "Require eight transport bytes and consistent DF metadata."

def decode : List UInt8 → Except String Decoded
  | version :: tos :: lh :: ll :: ih :: il :: fh :: fl :: ttl :: protocol :: ch :: cl ::
      sa :: sb :: sc :: sd :: da :: db :: dc :: dd :: payload => do
    if version != 69 then throw "Require quoted IPv4 version four and IHL five."
    if payload.length < 8 then throw "The quoted transport header requires eight bytes."
    let flags := read16 fh fl
    return ⟨⟨tos, read16 ih il, flagsDF flags, ttl, IPv4.protocolFromByte protocol,
      IPv4.readAddress sa sb sc sd, IPv4.readAddress da db dc dd, payload⟩,
      flags, read16 ch cl, read16 lh ll⟩
  | _ => .error "The quotation requires a twenty-byte IPv4 header."

theorem decode_bytes (value : Decoded) (shape : value.Shape) : decode (bytes value) = .ok value := by
  have enough : ¬value.packet.payload.length < 8 := by have := shape.1; omega
  have coherent := shape.2
  simp only [bytes, headerBytes, headerPrefix, IPv4.headerSuffix, IPv4.addressBytes, wordBytes,
    List.cons_append, List.nil_append, decode, read16_bytes, IPv4.readAddress_bytes,
    IPv4.protocolFromByte_encode]
  simp only [bne_self_eq_false, Bool.false_eq_true, ite_false, enough, bind, Except.bind, pure, Except.pure]
  rw [← coherent]

theorem decode_fields (wire : List UInt8) (value : Decoded) (accepted : decode wire = .ok value) :
    value.Shape ∧ bytes value = wire := by
  unfold decode at accepted
  split at accepted
  · rename_i version tos lh ll ih il fh fl ttl protocol ch cl sa sb sc sd da db dc dd payload
    by_cases versionOK : version = 69
    · subst version
      by_cases enough : payload.length < 8
      · simp [enough, bind, Except.bind, throw] at accepted
      · simp [enough, pure] at accepted
        cases accepted
        constructor
        · exact ⟨by change 8 ≤ payload.length; omega, rfl⟩
        · simp only [bytes, headerBytes, headerPrefix, IPv4.headerSuffix, IPv4.addressBytes_readAddress,
            wordBytes, highByte_read16, lowByte_read16, IPv4.protocolFromByte_bytes]
          rfl
    · simp [versionOK, bind, Except.bind, throw] at accepted
  · cases accepted

theorem decode_encodeDecoded (value : Decoded) (wire : List UInt8)
    (encoded : encodeDecoded value = .ok wire) : decode wire = .ok value := by
  unfold encodeDecoded at encoded
  split at encoded
  · cases encoded
    exact decode_bytes value (by assumption)
  · cases encoded

theorem encode_decode (wire : List UInt8) (value : Decoded) (accepted : decode wire = .ok value) :
    encodeDecoded value = .ok wire := by
  obtain ⟨shape, exactBytes⟩ := decode_fields wire value accepted
  rw [encodeDecoded, ite_eq_left shape, exactBytes]

def ofQuote (value : IPv4Quote.Decoded) : Decoded :=
  ⟨value.packet, if value.packet.dontFragment then 16384 else 0, value.checksum, value.declaredLength⟩

theorem ofQuote_shape (value : IPv4Quote.Decoded) (valid : value.Valid) : (ofQuote value).Shape := by
  constructor
  · have fields := valid.2.2.2.1
    unfold IPv4Quote.udpLength? at fields
    split at fields
    · simp_all [ofQuote]
    · cases fields
  · change value.packet.dontFragment = flagsDF (if value.packet.dontFragment then 16384 else 0)
    cases flag : value.packet.dontFragment <;> decide

end Netlib.Protocol.IPv4QuotePrefix
