import Netlib.Protocol.InternetChecksum

namespace Netlib.Protocol.ICMP

open InternetChecksum

inductive Kind where
  | timeExceeded
  | fragmentationNeeded (nextHopMTU : Word)
  deriving Repr, BEq, DecidableEq

structure Message where
  kind : Kind
  quote : List UInt8
  deriving Repr, BEq, DecidableEq

structure Decoded where
  message : Message
  checksum : Word
  deriving Repr, BEq, DecidableEq

def kindPrefix : Kind → List UInt8
  | .timeExceeded => [11, 0]
  | .fragmentationNeeded _ => [3, 4]

def kindSuffix : Kind → List UInt8
  | .timeExceeded => [0, 0, 0, 0]
  | .fragmentationNeeded mtu => [0, 0] ++ wordBytes mtu

@[simp] theorem kindPrefix_length (kind : Kind) : (kindPrefix kind).length = 2 := by cases kind <;> rfl
@[simp] theorem kindSuffix_length (kind : Kind) : (kindSuffix kind).length = 4 := by cases kind <;> rfl

def bytes (message : Message) (checksum : Word) : List UInt8 :=
  kindPrefix message.kind ++ wordBytes checksum ++ kindSuffix message.kind ++ message.quote

@[simp] theorem bytes_length (message : Message) (checksum : Word) :
    (bytes message checksum).length = message.quote.length + 8 := by simp [bytes]; omega

def computedChecksum (message : Message) : Word := InternetChecksum.checksum (bytes message 0)

theorem computedChecksum_valid (message : Message) : valid (bytes message (computedChecksum message)) = true := by
  simpa only [bytes, computedChecksum, wordBytes_zero, List.append_assoc] using
    synthesize_valid (kindPrefix message.kind) (kindSuffix message.kind ++ message.quote) (by simp)

def encode (message : Message) : List UInt8 := bytes message (computedChecksum message)

def encodeDecoded (value : Decoded) : Except String (List UInt8) :=
  if valid (bytes value.message value.checksum) then .ok (bytes value.message value.checksum)
  else .error "The ICMP checksum is invalid."

def decode : List UInt8 → Except String Decoded
  | type :: code :: ch :: cl :: u0 :: u1 :: u2 :: u3 :: quote => do
    let kind ← if type = 11 ∧ code = 0 ∧ u0 = 0 ∧ u1 = 0 ∧ u2 = 0 ∧ u3 = 0 then
        .ok Kind.timeExceeded
      else if type = 3 ∧ code = 4 ∧ u0 = 0 ∧ u1 = 0 then
        .ok (Kind.fragmentationNeeded (read16 u2 u3))
      else .error "Require ICMP time exceeded or fragmentation needed with zero unused fields."
    let message : Message := ⟨kind, quote⟩
    if valid (bytes message (read16 ch cl)) then return ⟨message, read16 ch cl⟩
    else throw "The ICMP checksum is invalid."
  | _ => .error "An ICMP error header requires eight bytes."

theorem decode_bytes (message : Message) (checksum : Word)
    (checked : valid (bytes message checksum) = true) :
    decode (bytes message checksum) = .ok ⟨message, checksum⟩ := by
  cases message with
  | mk kind quote =>
    cases kind <;>
      simp [bytes, kindPrefix, kindSuffix, wordBytes, decode, read16_bytes,
        bind, Except.bind, pure] at checked ⊢ <;> simp [checked, Except.pure]

theorem decode_encode (message : Message) : decode (encode message) = .ok ⟨message, computedChecksum message⟩ :=
  decode_bytes message (computedChecksum message) (computedChecksum_valid message)

theorem decode_encodeDecoded (value : Decoded) (wire : List UInt8)
    (encoded : encodeDecoded value = .ok wire) : decode wire = .ok value := by
  unfold encodeDecoded at encoded
  split at encoded
  · cases encoded
    exact decode_bytes value.message value.checksum (by assumption)
  · cases encoded

theorem decode_fields (wire : List UInt8) (value : Decoded) (accepted : decode wire = .ok value) :
    valid (bytes value.message value.checksum) = true ∧ bytes value.message value.checksum = wire := by
  unfold decode at accepted
  split at accepted
  · rename_i type code ch cl u0 u1 u2 u3 quote
    by_cases time : type = 11 ∧ code = 0 ∧ u0 = 0 ∧ u1 = 0 ∧ u2 = 0 ∧ u3 = 0
    · obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := time
      by_cases checked : valid (bytes ⟨.timeExceeded, quote⟩ (read16 ch cl)) = true
      · simp [checked, bind, Except.bind, pure] at accepted
        cases accepted
        exact ⟨checked, by simp [bytes, kindPrefix, kindSuffix, wordBytes]⟩
      · simp [checked, bind, Except.bind, throw] at accepted
    · by_cases frag : type = 3 ∧ code = 4 ∧ u0 = 0 ∧ u1 = 0
      · obtain ⟨rfl, rfl, rfl, rfl⟩ := frag
        by_cases checked : valid (bytes ⟨.fragmentationNeeded (read16 u2 u3), quote⟩ (read16 ch cl)) = true
        · simp [checked, bind, Except.bind, pure] at accepted
          cases accepted
          exact ⟨checked, by simp [bytes, kindPrefix, kindSuffix, wordBytes]⟩
        · simp [checked, bind, Except.bind, throw] at accepted
      · simp [time, frag, bind, Except.bind] at accepted
  · cases accepted

theorem encode_decode (wire : List UInt8) (value : Decoded) (accepted : decode wire = .ok value) :
    encodeDecoded value = .ok wire := by
  obtain ⟨checked, exactBytes⟩ := decode_fields wire value accepted
  rw [encodeDecoded, ite_eq_left checked, exactBytes]

end Netlib.Protocol.ICMP
