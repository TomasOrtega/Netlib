import Netlib.Protocol.EAP

/-!
# Untagged Ethernet EAPOL framing

The profile supports EAPOL versions 1 through 3 and EAP, Start, and Logoff bodies.
Inner EAP padding and outer Ethernet padding remain separate.
-/

namespace Netlib.Import.EAPOL

open Protocol

private def nibble (char : Char) : Except String Nat :=
  if '0' ≤ char && char ≤ '9' then .ok (char.toNat - '0'.toNat)
  else if 'a' ≤ char && char ≤ 'f' then .ok (char.toNat - 'a'.toNat + 10)
  else if 'A' ≤ char && char ≤ 'F' then .ok (char.toNat - 'A'.toNat + 10)
  else .error "Require hexadecimal digits without separators or whitespace."

private def decodeHex : List Char → Except String (List UInt8)
  | [] => .ok []
  | high :: low :: rest => do
    let high ← nibble high
    let low ← nibble low
    return UInt8.ofNat (high * 16 + low) :: (← decodeHex rest)
  | [_] => .error "Hexadecimal bytes require an even number of digits."

def bytesFromHex (text : String) : Except String (List UInt8) := decodeHex text.toList

private def hexDigit (value : Nat) : Char :=
  if value < 10 then Char.ofNat ('0'.toNat + value) else Char.ofNat ('a'.toNat + value - 10)

private def byteHex (value : UInt8) : String :=
  String.ofList [hexDigit (value.toNat / 16), hexDigit (value.toNat % 16)]

def bytesToHex (values : List UInt8) : String := String.join (values.map byteHex)

structure MAC where
  a : UInt8
  b : UInt8
  c : UInt8
  d : UInt8
  e : UInt8
  f : UInt8
  deriving Repr, BEq, DecidableEq

namespace MAC

def bytes (address : MAC) : List UInt8 := [address.a, address.b, address.c, address.d, address.e, address.f]

def render (address : MAC) : String := String.intercalate ":" (address.bytes.map byteHex)

def read : List UInt8 → Except String (MAC × List UInt8)
  | a :: b :: c :: d :: e :: f :: rest => .ok (⟨a, b, c, d, e, f⟩, rest)
  | _ => .error "An Ethernet address requires six bytes."

def parse (text : String) : Except String MAC := do
  let parts := text.splitOn ":"
  if parts.length != 6 || !(parts.all (fun part => part.length == 2)) then
    throw "Require an Ethernet address in aa:bb:cc:dd:ee:ff form."
  let (address, rest) ← read (← bytesFromHex (String.join parts))
  if !rest.isEmpty then throw "Unexpected bytes after the Ethernet address."
  return address

@[simp] theorem bytes_length (address : MAC) : address.bytes.length = 6 := rfl

theorem read_bytes (address : MAC) (rest : List UInt8) :
    read (address.bytes ++ rest) = .ok (address, rest) := by
  cases address
  rfl

theorem bytes_read (bytes : List UInt8) (address : MAC) (rest : List UInt8)
    (accepted : read bytes = .ok (address, rest)) : address.bytes ++ rest = bytes := by
  unfold read at accepted
  split at accepted
  · cases accepted
    rfl
  · cases accepted

end MAC

inductive Version where
  | v1
  | v2
  | v3
  deriving Repr, BEq, DecidableEq

namespace Version

def code : Version → UInt8
  | .v1 => 1
  | .v2 => 2
  | .v3 => 3

def decode (value : UInt8) : Except String Version :=
  match value.toNat with
  | 1 => .ok .v1
  | 2 => .ok .v2
  | 3 => .ok .v3
  | _ => .error "Only EAPOL versions 1, 2, and 3 are supported."

@[simp] theorem decode_code (version : Version) : decode version.code = .ok version := by
  cases version <;> rfl

theorem code_decode (value : UInt8) (version : Version) (accepted : decode value = .ok version) :
    version.code = value := by
  by_cases first : value.toNat = 1
  · have same : value = 1 := UInt8.toNat_inj.mp (by simpa using first)
    subst value
    cases accepted
    rfl
  · by_cases second : value.toNat = 2
    · have same : value = 2 := UInt8.toNat_inj.mp (by simpa using second)
      subst value
      cases accepted
      rfl
    · by_cases third : value.toNat = 3
      · have same : value = 3 := UInt8.toNat_inj.mp (by simpa using third)
        subst value
        cases accepted
        rfl
      · unfold decode at accepted
        split at accepted <;> simp_all

end Version

inductive Body where
  | eap (value : EAP.Decoded)
  | start
  | logoff
  deriving Repr, BEq, DecidableEq

def Body.code : Body → UInt8
  | .eap _ => 0
  | .start => 1
  | .logoff => 2

structure Frame where
  version : Version
  body : Body
  deriving Repr, BEq, DecidableEq

structure Decoded where
  frame : Frame
  padding : List UInt8
  deriving Repr, BEq, DecidableEq

def decodeBody (kind : UInt8) (payload : List UInt8) : Except String Body :=
  match kind.toNat with
  | 0 => Body.eap <$> EAP.decode payload
  | 1 => if payload.isEmpty then .ok .start else .error "Nonempty EAPOL-Start bodies are unsupported."
  | 2 => if payload.isEmpty then .ok .logoff else .error "Nonempty EAPOL-Logoff bodies are unsupported."
  | _ => .error "Only EAP-Packet, EAPOL-Start, and EAPOL-Logoff are supported."

def decode : List UInt8 → Except String Decoded
  | version :: kind :: high :: low :: rest => do
    let version ← Version.decode version
    let declared := EAP.read16 high low
    if rest.length < declared then throw "The EAPOL declared body exceeds the received bytes."
    let body ← decodeBody kind (rest.take declared)
    return ⟨⟨version, body⟩, rest.drop declared⟩
  | _ => .error "An EAPOL frame requires a four-byte header."

def encodeBody : Body → Except String (List UInt8)
  | .eap value => EAP.encodeDecoded value
  | .start | .logoff => .ok []

def frameBytes (frame : Frame) (payload : List UInt8) : List UInt8 :=
  frame.version.code :: frame.body.code :: EAP.highByte payload.length :: EAP.lowByte payload.length :: payload

def encode (frame : Frame) : Except String (List UInt8) := do
  let payload ← encodeBody frame.body
  if payload.length < 65536 then return frameBytes frame payload
  else throw "The EAPOL body exceeds its 16-bit length field."

def encodeDecoded (value : Decoded) : Except String (List UInt8) := do
  return (← encode value.frame) ++ value.padding

theorem decodeBody_encodeBody (body : Body) (payload : List UInt8) (encoded : encodeBody body = .ok payload) :
    decodeBody body.code payload = .ok body := by
  cases body with
  | eap value =>
    change EAP.encodeDecoded value = .ok payload at encoded
    simp only [Body.code, decodeBody, EAP.decode_encodeDecoded value payload encoded]
    rfl
  | start => cases encoded; rfl
  | logoff => cases encoded; rfl

theorem decode_frameBytes (frame : Frame) (payload padding : List UInt8)
    (bounded : payload.length < 65536) (body : decodeBody frame.body.code payload = .ok frame.body) :
    decode (frameBytes frame payload ++ padding) = .ok ⟨frame, padding⟩ := by
  have available : ¬(payload ++ padding).length < payload.length := by simp
  simp only [frameBytes, List.cons_append, decode, Version.decode_code, bind, Except.bind, pure,
    EAP.read16_bytes payload.length bounded, ite_eq_right available]
  simp only [List.take_left, List.drop_left, body]
  rfl

theorem decode_encode_padding (frame : Frame) (bytes padding : List UInt8) (encoded : encode frame = .ok bytes) :
    decode (bytes ++ padding) = .ok ⟨frame, padding⟩ := by
  cases found : encodeBody frame.body with
  | error error => simp [encode, found, bind, Except.bind] at encoded
  | ok payload =>
    simp only [encode, found, bind, Except.bind] at encoded
    split at encoded
    · cases encoded
      exact decode_frameBytes frame payload padding (by assumption) (decodeBody_encodeBody _ _ found)
    · cases encoded

theorem decode_encode (frame : Frame) (bytes : List UInt8) (encoded : encode frame = .ok bytes) :
    decode bytes = .ok ⟨frame, []⟩ := by simpa using decode_encode_padding frame bytes [] encoded

theorem decode_encodeDecoded (value : Decoded) (bytes : List UInt8) (encoded : encodeDecoded value = .ok bytes) :
    decode bytes = .ok value := by
  cases found : encode value.frame with
  | error error => simp [encodeDecoded, found, bind, Except.bind] at encoded
  | ok canonical =>
    simp [encodeDecoded, found, bind, Except.bind, pure] at encoded
    cases encoded
    simpa using decode_encode_padding value.frame canonical value.padding found

private theorem encodeBody_decodeBody (kind : UInt8) (payload : List UInt8) (body : Body)
    (accepted : decodeBody kind payload = .ok body) :
    body.code = kind ∧ encodeBody body = .ok payload := by
  by_cases eap : kind.toNat = 0
  · have same : kind = 0 := UInt8.toNat_inj.mp (by simpa using eap)
    subst kind
    cases found : EAP.decode payload with
    | error error =>
      simp only [decodeBody, found] at accepted
      change (Except.error error : Except String Body) = .ok body at accepted
      cases accepted
    | ok value =>
      simp [decodeBody, found] at accepted
      cases accepted
      exact ⟨rfl, EAP.encode_decode payload value found⟩
  · by_cases start : kind.toNat = 1
    · have same : kind = 1 := UInt8.toNat_inj.mp (by simpa using start)
      subst kind
      cases payload with
      | nil => cases accepted; exact ⟨rfl, rfl⟩
      | cons byte rest => cases accepted
    · by_cases logoff : kind.toNat = 2
      · have same : kind = 2 := UInt8.toNat_inj.mp (by simpa using logoff)
        subst kind
        cases payload with
        | nil => cases accepted; exact ⟨rfl, rfl⟩
        | cons byte rest => cases accepted
      · unfold decodeBody at accepted
        split at accepted <;> simp_all

private theorem encode_decode_header (version kind high low : UInt8) (rest : List UInt8) (value : Decoded)
    (accepted : decode (version :: kind :: high :: low :: rest) = .ok value) :
    encodeDecoded value = .ok (version :: kind :: high :: low :: rest) := by
  cases foundVersion : Version.decode version with
  | error error => simp [decode, foundVersion, bind, Except.bind] at accepted
  | ok decodedVersion =>
    by_cases truncated : rest.length < EAP.read16 high low
    · simp [decode, foundVersion, truncated, bind, Except.bind, throw] at accepted
    · cases foundBody : decodeBody kind (rest.take (EAP.read16 high low)) with
      | error error => simp [decode, foundVersion, truncated, foundBody, bind, Except.bind] at accepted
      | ok body =>
        simp [decode, foundVersion, truncated, foundBody, bind, Except.bind, pure] at accepted
        cases accepted
        have versionSame := Version.code_decode version decodedVersion foundVersion
        obtain ⟨kindSame, bodySame⟩ := encodeBody_decodeBody _ _ _ foundBody
        have length : (rest.take (EAP.read16 high low)).length = EAP.read16 high low := by
          rw [List.length_take]
          omega
        have bounded : (rest.take (EAP.read16 high low)).length < 65536 := by
          rw [length]
          exact EAP.read16_bounded high low
        simp only [encodeDecoded, encode, bodySame, bind, Except.bind, ite_eq_left bounded, pure]
        apply congrArg Except.ok
        simp [frameBytes, versionSame, kindSame, length, EAP.highByte_read16, EAP.lowByte_read16,
          List.take_append_drop]

theorem encode_decode (bytes : List UInt8) (value : Decoded) (accepted : decode bytes = .ok value) :
    encodeDecoded value = .ok bytes := by
  cases bytes with
  | nil => cases accepted
  | cons version bytes =>
    cases bytes with
    | nil => cases accepted
    | cons kind bytes =>
      cases bytes with
      | nil => cases accepted
      | cons high bytes =>
        cases bytes with
        | nil => cases accepted
        | cons low rest => exact encode_decode_header version kind high low rest value accepted

structure EthernetFrame where
  destination : MAC
  source : MAC
  frame : Frame
  padding : List UInt8
  deriving Repr, BEq, DecidableEq

def decodeEthernet (bytes : List UInt8) : Except String EthernetFrame := do
  let (destination, bytes) ← MAC.read bytes
  let (source, bytes) ← MAC.read bytes
  match bytes with
  | high :: low :: payload =>
    if EAP.read16 high low != 34958 then throw "Require untagged Ethernet EtherType 0x888e."
    let decoded ← decode payload
    return ⟨destination, source, decoded.frame, decoded.padding⟩
  | _ => throw "An Ethernet frame requires its two-byte EtherType."

def encodeEthernet (frame : EthernetFrame) : Except String (List UInt8) := do
  let payload ← encode frame.frame
  return frame.destination.bytes ++ frame.source.bytes ++ [136, 142] ++ payload ++ frame.padding

def parseHex (text : String) : Except String EthernetFrame := bytesFromHex text >>= decodeEthernet

theorem decodeEthernet_encodeEthernet (frame : EthernetFrame) (bytes : List UInt8)
    (encoded : encodeEthernet frame = .ok bytes) : decodeEthernet bytes = .ok frame := by
  cases found : encode frame.frame with
  | error error => simp [encodeEthernet, found, bind, Except.bind] at encoded
  | ok payload =>
    simp [encodeEthernet, found, bind, Except.bind, pure] at encoded
    cases encoded
    simp only [decodeEthernet, MAC.read_bytes, bind, Except.bind, pure]
    change (do
      let decoded ← decode (payload ++ frame.padding)
      pure (EthernetFrame.mk frame.destination frame.source decoded.frame decoded.padding)) = .ok frame
    rw [decode_encode_padding frame.frame payload frame.padding found]
    rfl

theorem encodeEthernet_decodeEthernet (bytes : List UInt8) (frame : EthernetFrame)
    (accepted : decodeEthernet bytes = .ok frame) : encodeEthernet frame = .ok bytes := by
  cases destinationRead : MAC.read bytes with
  | error error => simp [decodeEthernet, destinationRead, bind, Except.bind] at accepted
  | ok destinationRest =>
    obtain ⟨destination, rest⟩ := destinationRest
    cases sourceRead : MAC.read rest with
    | error error => simp [decodeEthernet, destinationRead, sourceRead, bind, Except.bind] at accepted
    | ok sourceRest =>
      obtain ⟨source, typeRest⟩ := sourceRest
      cases typeRest with
      | nil => simp [decodeEthernet, destinationRead, sourceRead, bind, Except.bind, throw] at accepted
      | cons high typeRest =>
        cases typeRest with
        | nil => simp [decodeEthernet, destinationRead, sourceRead, bind, Except.bind, throw] at accepted
        | cons low payload =>
          by_cases etherType : EAP.read16 high low = 34958
          · cases found : decode payload with
            | error error =>
              simp [decodeEthernet, destinationRead, sourceRead, etherType, found,
                bind, Except.bind] at accepted
            | ok decoded =>
              simp [decodeEthernet, destinationRead, sourceRead, etherType, found,
                bind, Except.bind, pure] at accepted
              cases accepted
              have highSame : high = 136 := by
                rw [← EAP.highByte_read16 high low, etherType]
                rfl
              have lowSame : low = 142 := by
                rw [← EAP.lowByte_read16 high low, etherType]
                rfl
              have reencoded := encode_decode payload decoded found
              cases encoded : encode decoded.frame with
              | error error => simp [encodeDecoded, encoded, bind, Except.bind] at reencoded
              | ok canonical =>
                simp [encodeDecoded, encoded, bind, Except.bind, pure] at reencoded
                change Except.ok (canonical ++ decoded.padding) = .ok payload at reencoded
                have payloadSame := Except.ok.inj reencoded
                have destinationBytes := MAC.bytes_read bytes destination rest destinationRead
                have sourceBytes := MAC.bytes_read rest source (high :: low :: payload) sourceRead
                rw [← destinationBytes, ← sourceBytes]
                simp [encodeEthernet, encoded, bind, Except.bind, pure, highSame, lowSame,
                  List.append_assoc, payloadSame]
                rfl
          · simp [decodeEthernet, destinationRead, sourceRead, etherType,
              bind, Except.bind, throw] at accepted

end Netlib.Import.EAPOL
