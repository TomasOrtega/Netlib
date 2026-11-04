import Std

/-!
# RFC 3748 packet framing

Method bytes remain opaque. A Success packet is a wire value, not authentication evidence.
Bytes beyond the declared length are retained as padding.
-/

namespace Netlib.Protocol.EAP

inductive Packet where
  | request (identifier : UInt8) (kind : UInt8) (data : List UInt8)
  | response (identifier : UInt8) (kind : UInt8) (data : List UInt8)
  | success (identifier : UInt8)
  | failure (identifier : UInt8)
  deriving Repr, BEq, DecidableEq

namespace Packet

def identifier : Packet → UInt8
  | .request identifier .. | .response identifier .. | .success identifier | .failure identifier => identifier

def code : Packet → UInt8
  | .request .. => 1
  | .response .. => 2
  | .success .. => 3
  | .failure .. => 4

def kind? : Packet → Option UInt8
  | .request _ kind _ | .response _ kind _ => some kind
  | .success .. | .failure .. => none

def payload : Packet → List UInt8
  | .request _ kind data | .response _ kind data => kind :: data
  | .success .. | .failure .. => []

def wireLength (packet : Packet) : Nat := packet.payload.length + 4

def Encodable (packet : Packet) : Prop := packet.wireLength < 65536

instance (packet : Packet) : Decidable packet.Encodable := inferInstanceAs (Decidable (packet.wireLength < 65536))

end Packet

def highByte (value : Nat) : UInt8 := UInt8.ofNat (value / 256)
def lowByte (value : Nat) : UInt8 := UInt8.ofNat value
def read16 (high low : UInt8) : Nat := high.toNat * 256 + low.toNat

theorem read16_bytes (value : Nat) (bounded : value < 65536) :
    read16 (highByte value) (lowByte value) = value := by
  have high : value / 256 < 256 := by omega
  simp only [read16, highByte, lowByte, UInt8.toNat_ofNat']
  change value / 256 % 256 * 256 + value % 256 = value
  rw [Nat.mod_eq_of_lt high]
  omega

theorem read16_bounded (high low : UInt8) : read16 high low < 65536 := by
  have first := UInt8.toNat_lt high
  have second := UInt8.toNat_lt low
  unfold read16
  omega

theorem highByte_read16 (high low : UInt8) : highByte (read16 high low) = high := by
  have lower := UInt8.toNat_lt low
  have quotient : read16 high low / 256 = high.toNat := by unfold read16; omega
  simp [highByte, quotient]

theorem lowByte_read16 (high low : UInt8) : lowByte (read16 high low) = low := by
  apply UInt8.toNat_inj.mp
  have lower := UInt8.toNat_lt low
  simp only [lowByte, UInt8.toNat_ofNat']
  change read16 high low % 256 = low.toNat
  unfold read16
  omega

structure Decoded where
  packet : Packet
  padding : List UInt8
  deriving Repr, BEq, DecidableEq

def decodePayload (code identifier : UInt8) (payload : List UInt8) : Except String Packet :=
  match code.toNat with
  | 1 => match payload with
    | kind :: data => .ok (.request identifier kind data)
    | [] => .error "An EAP Request requires its Type byte."
  | 2 => match payload with
    | kind :: data => .ok (.response identifier kind data)
    | [] => .error "An EAP Response requires its Type byte."
  | 3 => if payload.isEmpty then .ok (.success identifier)
    else .error "EAP Success cannot contain declared data."
  | 4 => if payload.isEmpty then .ok (.failure identifier)
    else .error "EAP Failure cannot contain declared data."
  | _ => .error "Only RFC 3748 EAP Codes 1 through 4 are supported."

def decode : List UInt8 → Except String Decoded
  | code :: identifier :: high :: low :: rest => do
    let declared := read16 high low
    if declared < 4 then throw "The EAP length is shorter than its header."
    if rest.length < declared - 4 then throw "The EAP declared length exceeds the received bytes."
    let packet ← decodePayload code identifier (rest.take (declared - 4))
    return ⟨packet, rest.drop (declared - 4)⟩
  | _ => .error "An EAP packet requires a four-byte header."

def encodeBytes (packet : Packet) : List UInt8 :=
  packet.code :: packet.identifier :: highByte packet.wireLength :: lowByte packet.wireLength :: packet.payload

def encode (packet : Packet) : Except String (List UInt8) :=
  if packet.Encodable then .ok (encodeBytes packet)
  else .error "The EAP packet exceeds its 16-bit length field."

def encodeDecoded (value : Decoded) : Except String (List UInt8) := do
  return (← encode value.packet) ++ value.padding

@[simp] theorem decodePayload_packet (packet : Packet) :
    decodePayload packet.code packet.identifier packet.payload = .ok packet := by
  cases packet <;> rfl

theorem encodeBytes_length (packet : Packet) : (encodeBytes packet).length = packet.wireLength := by
  simp [encodeBytes, Packet.wireLength]

theorem decode_encodeBytes (packet : Packet) (padding : List UInt8) (bounded : packet.Encodable) :
    decode (encodeBytes packet ++ padding) = .ok ⟨packet, padding⟩ := by
  have minimum : ¬packet.wireLength < 4 := by unfold Packet.wireLength; omega
  have available : ¬(packet.payload ++ padding).length < packet.wireLength - 4 := by
    simp only [List.length_append, Packet.wireLength]
    omega
  simp only [encodeBytes, List.cons_append, decode]
  simp only [read16_bytes packet.wireLength bounded, ite_eq_right minimum, ite_eq_right available]
  simp [Packet.wireLength]
  rfl

theorem decode_encode (packet : Packet) (bytes : List UInt8) (encoded : encode packet = .ok bytes) :
    decode bytes = .ok ⟨packet, []⟩ := by
  unfold encode at encoded
  split at encoded
  · cases encoded
    simpa using decode_encodeBytes packet [] (by assumption)
  · cases encoded

theorem decode_encodeDecoded (value : Decoded) (bytes : List UInt8)
    (encoded : encodeDecoded value = .ok bytes) : decode bytes = .ok value := by
  cases found : encode value.packet with
  | error error => simp [encodeDecoded, found, bind, Except.bind] at encoded
  | ok canonical =>
    simp [encodeDecoded, found, bind, Except.bind, pure] at encoded
    cases encoded
    unfold encode at found
    split at found
    · cases found
      simpa using decode_encodeBytes value.packet value.padding (by assumption)
    · cases found

private theorem decodePayload_fields (code identifier : UInt8) (payload : List UInt8) (packet : Packet)
    (accepted : decodePayload code identifier payload = .ok packet) :
    packet.code = code ∧ packet.identifier = identifier ∧ packet.payload = payload := by
  by_cases request : code.toNat = 1
  · have same : code = 1 := UInt8.toNat_inj.mp (by simpa using request)
    subst code
    cases payload with
    | nil => cases accepted
    | cons kind data => cases accepted; exact ⟨rfl, rfl, rfl⟩
  · by_cases response : code.toNat = 2
    · have same : code = 2 := UInt8.toNat_inj.mp (by simpa using response)
      subst code
      cases payload with
      | nil => cases accepted
      | cons kind data => cases accepted; exact ⟨rfl, rfl, rfl⟩
    · by_cases success : code.toNat = 3
      · have same : code = 3 := UInt8.toNat_inj.mp (by simpa using success)
        subst code
        cases payload with
        | nil => cases accepted; exact ⟨rfl, rfl, rfl⟩
        | cons kind data => cases accepted
      · by_cases failure : code.toNat = 4
        · have same : code = 4 := UInt8.toNat_inj.mp (by simpa using failure)
          subst code
          cases payload with
          | nil => cases accepted; exact ⟨rfl, rfl, rfl⟩
          | cons kind data => cases accepted
        · unfold decodePayload at accepted
          split at accepted <;> simp_all

private theorem encode_decode_header (code identifier high low : UInt8) (rest : List UInt8) (value : Decoded)
    (accepted : decode (code :: identifier :: high :: low :: rest) = .ok value) :
    encodeDecoded value = .ok (code :: identifier :: high :: low :: rest) := by
  by_cases short : read16 high low < 4
  · simp [decode, short, bind, Except.bind, throw] at accepted
  · by_cases truncated : rest.length < read16 high low - 4
    · simp [decode, short, truncated, bind, Except.bind, throw] at accepted
    · cases found : decodePayload code identifier (rest.take (read16 high low - 4)) with
      | error error => simp [decode, short, truncated, found, bind, Except.bind] at accepted
      | ok packet =>
        simp [decode, short, truncated, found, bind, Except.bind, pure] at accepted
        cases accepted
        obtain ⟨codeSame, identifierSame, payloadSame⟩ := decodePayload_fields _ _ _ _ found
        have length : packet.wireLength = read16 high low := by
          rw [Packet.wireLength, payloadSame, List.length_take]
          omega
        have bounded : packet.Encodable := by
          rw [Packet.Encodable, length]
          exact read16_bounded high low
        simp only [encodeDecoded, encode, ite_eq_left bounded, bind, Except.bind, pure]
        apply congrArg Except.ok
        simp [encodeBytes, codeSame, identifierSame, length, highByte_read16, lowByte_read16,
          payloadSame, List.take_append_drop]

theorem encode_decode (bytes : List UInt8) (value : Decoded) (accepted : decode bytes = .ok value) :
    encodeDecoded value = .ok bytes := by
  cases bytes with
  | nil => cases accepted
  | cons code bytes =>
    cases bytes with
    | nil => cases accepted
    | cons identifier bytes =>
      cases bytes with
      | nil => cases accepted
      | cons high bytes =>
        cases bytes with
        | nil => cases accepted
        | cons low rest => exact encode_decode_header code identifier high low rest value accepted

end Netlib.Protocol.EAP
