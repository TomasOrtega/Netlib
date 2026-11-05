import Netlib.Protocol.TCP.Options

/-!
# Directional TCP maximum segment size

The option states its sender's receive capability.
Extraction is separate from output placement and other option semantics.
Absent IPv4 MSS selects 536; zero and duplicate values remain distinct unsupported cases.
The send limit includes the full IPv4 datagram and uses actual packet option overhead.
Receive advertisement uses separate finite IPv4 receive and reassembly evidence.
-/

namespace Netlib.Protocol.TCP.MSS

open InternetChecksum

inductive Error where
  | framing
  | zero
  | duplicate
  | valueRange
  | otherOptions
  | receiveLimit
  | advertisementBound
  deriving Repr, BEq, ReflBEq, LawfulBEq, DecidableEq

def Error.message : Error → String
  | .framing => "The TCP option framing is invalid."
  | .zero => "A present zero MSS requires semantics outside this selected model."
  | .duplicate => "Duplicate MSS options require semantics outside this selected model."
  | .valueRange => "The MSS value must fit its positive 16-bit field."
  | .otherOptions => "The startup options require semantics outside MSS, NOP, and EOL."
  | .receiveLimit => "The declared IPv4 receive and reassembly limit must be between 576 and 65535."
  | .advertisementBound => "The advertised MSS exceeds the declared IPv4 receive and reassembly limit."

structure Value where
  word : Word
  positive : 0 < word.val
  deriving Repr, BEq, ReflBEq, LawfulBEq, DecidableEq

def Value.ofNat (number : Nat) : Except Error Value :=
  if positive : 0 < number then
    if bounded : number < 65536 then .ok ⟨⟨number, bounded⟩, positive⟩
    else .error .valueRange
  else .error .zero

inductive Offer where
  | absent
  | present (value : Value)
  deriving Repr, BEq, DecidableEq

def Offer.limit : Offer → Nat
  | .absent => 536
  | .present value => value.word.val

theorem Offer.limit_positive (offer : Offer) : 0 < offer.limit := by
  cases offer with
  | absent => decide
  | present value => exact value.positive

theorem Offer.limit_bound (offer : Offer) : offer.limit < 65536 := by
  cases offer with
  | absent => decide
  | present value => exact value.word.isLt

def Offer.Observed (offer : Offer) (bytes : List UInt8) : Prop :=
  Options.valid bytes = true ∧
    match offer with
    | .absent => Options.maximumSegmentSizes bytes = []
    | .present value => Options.maximumSegmentSizes bytes = [value.word]

def read (bytes : List UInt8) : Except Error Offer :=
  if Options.valid bytes = true then
    match Options.maximumSegmentSizes bytes with
    | [] => .ok .absent
    | [word] =>
      if positive : 0 < word.val then .ok (.present ⟨word, positive⟩)
      else .error .zero
    | _ :: _ :: _ => .error .duplicate
  else .error .framing

theorem read_observed (bytes : List UInt8) (offer : Offer) (accepted : read bytes = .ok offer) :
    offer.Observed bytes := by
  unfold read at accepted
  split at accepted
  · rename_i framed
    split at accepted
    · cases accepted
      exact ⟨framed, by assumption⟩
    · split at accepted
      · cases accepted
        exact ⟨framed, by assumption⟩
      · cases accepted
    · cases accepted
  · cases accepted

def startupOptions : List UInt8 → Bool
  | [] => true
  | kind :: rest =>
    if kind == 0 then rest.all (· == 0)
    else if kind == 1 then startupOptions rest
    else match rest with
      | [] => false
      | length :: tail =>
        if kind == 2 ∧ length == 4 ∧ 2 ≤ tail.length then startupOptions (tail.drop 2)
        else false
termination_by bytes => bytes.length
decreasing_by all_goals (simp_wf <;> omega)

def readStartup (bytes : List UInt8) : Except Error Offer := do
  let offer ← read bytes
  if startupOptions bytes then return offer else throw .otherOptions

theorem readStartup_observed (bytes : List UInt8) (offer : Offer)
    (accepted : readStartup bytes = .ok offer) : offer.Observed bytes ∧ startupOptions bytes = true := by
  unfold readStartup at accepted
  cases selected : read bytes with
  | error reason => simp [selected, bind, Except.bind] at accepted
  | ok actual =>
    simp only [selected, bind, Except.bind] at accepted
    split at accepted
    · cases accepted
      exact ⟨read_observed _ _ selected, by assumption⟩
    · cases accepted

def selectStartup (bytes : List UInt8) (accepted : (readStartup bytes).isOk = true) :
    { offer : Offer // readStartup bytes = .ok offer } := by
  cases computed : readStartup bytes with
  | ok offer => exact ⟨offer, rfl⟩
  | error reason =>
    rw [computed] at accepted
    change false = true at accepted
    cases accepted

def encode (value : Value) : List UInt8 := [2, 4] ++ wordBytes value.word

@[simp] theorem encode_length (value : Value) : (encode value).length = 4 := rfl

@[simp] theorem encode_aligned (value : Value) : (encode value).length % 4 = 0 := by simp

theorem encode_valid (value : Value) : Options.valid (encode value) = true := by
  simp [encode, wordBytes, Options.valid]

theorem encode_values (value : Value) : Options.maximumSegmentSizes (encode value) = [value.word] := by
  simp [encode, wordBytes, Options.maximumSegmentSizes, read16_bytes]

theorem encode_startup (value : Value) : startupOptions (encode value) = true := by
  simp [encode, wordBytes, startupOptions]

theorem read_encode (value : Value) : read (encode value) = .ok (.present value) := by
  simp only [read, encode_valid, ↓reduceIte, encode_values]
  split
  · congr
  · exact False.elim ((by assumption : ¬0 < value.word.val) value.positive)

theorem readStartup_encode (value : Value) : readStartup (encode value) = .ok (.present value) := by
  simp [readStartup, read_encode, encode_startup]

structure Advertisement where
  receiveLimit : Nat
  value : Value
  receiveBounds : 576 ≤ receiveLimit ∧ receiveLimit ≤ 65535
  fits : 40 + value.word.val ≤ receiveLimit
  deriving Repr, BEq, ReflBEq, LawfulBEq, DecidableEq

def Advertisement.make (receiveLimit : Nat) (value : Value) : Except Error Advertisement :=
  if bounds : 576 ≤ receiveLimit ∧ receiveLimit ≤ 65535 then
    if fits : 40 + value.word.val ≤ receiveLimit then .ok ⟨receiveLimit, value, bounds, fits⟩
    else .error .advertisementBound
  else .error .receiveLimit

def Advertisement.offer (advertisement : Advertisement) : Offer := .present advertisement.value
def Advertisement.options (advertisement : Advertisement) : List UInt8 := encode advertisement.value

theorem Advertisement.make_fields (receiveLimit : Nat) (value : Value) (advertisement : Advertisement)
    (accepted : Advertisement.make receiveLimit value = .ok advertisement) :
    advertisement.receiveLimit = receiveLimit ∧ advertisement.value = value := by
  unfold Advertisement.make at accepted
  split at accepted
  · split at accepted
    · cases accepted
      exact ⟨rfl, rfl⟩
    · cases accepted
  · cases accepted

theorem Advertisement.read (advertisement : Advertisement) :
    readStartup advertisement.options = .ok advertisement.offer := readStartup_encode _

def effective (peer : Offer) (ipSendLimit ipOptionBytes tcpOptionBytes : Nat) : Nat :=
  min peer.limit (ipSendLimit - 40) - (ipOptionBytes + tcpOptionBytes)

@[simp] theorem effective_no_options (peer : Offer) (ipSendLimit : Nat) :
    effective peer ipSendLimit 0 0 = min peer.limit (ipSendLimit - 40) := by
  simp [effective]

@[simp] theorem effective_default (ipSendLimit : Nat) :
    effective .absent ipSendLimit 0 0 = min 536 (ipSendLimit - 40) := by
  simp [effective, Offer.limit]

theorem effective_rfc (peer : Offer) (ipSendLimit ipOptionBytes tcpOptionBytes : Nat)
    (headers : 40 ≤ ipSendLimit) :
    effective peer ipSendLimit ipOptionBytes tcpOptionBytes =
      min (peer.limit + 20) (ipSendLimit - 20) - (20 + tcpOptionBytes) - ipOptionBytes := by
  unfold effective
  omega

theorem effective_peer (peer : Offer) (ipSendLimit ipOptionBytes tcpOptionBytes : Nat) :
    effective peer ipSendLimit ipOptionBytes tcpOptionBytes ≤ peer.limit := by
  unfold effective
  omega

theorem effective_positive (peer : Offer) (ipSendLimit ipOptionBytes tcpOptionBytes : Nat) :
    0 < effective peer ipSendLimit ipOptionBytes tcpOptionBytes ↔
      ipOptionBytes + tcpOptionBytes < min peer.limit (ipSendLimit - 40) := by
  unfold effective
  omega

theorem effective_bounds (peer : Offer) (ipSendLimit ipOptionBytes tcpOptionBytes : Nat)
    (room : ipOptionBytes + tcpOptionBytes < min peer.limit (ipSendLimit - 40)) :
    0 < effective peer ipSendLimit ipOptionBytes tcpOptionBytes ∧
      ipOptionBytes + tcpOptionBytes + effective peer ipSendLimit ipOptionBytes tcpOptionBytes ≤ peer.limit ∧
      40 + ipOptionBytes + tcpOptionBytes + effective peer ipSendLimit ipOptionBytes tcpOptionBytes ≤ ipSendLimit := by
  unfold effective
  omega

theorem effective_exhausted (peer : Offer) (ipSendLimit ipOptionBytes tcpOptionBytes : Nat)
    (exhausted : min peer.limit (ipSendLimit - 40) ≤ ipOptionBytes + tcpOptionBytes) :
    effective peer ipSendLimit ipOptionBytes tcpOptionBytes = 0 := by
  unfold effective
  omega

theorem effective_no_options_positive (peer : Offer) (ipSendLimit : Nat) (headers : 40 < ipSendLimit) :
    0 < effective peer ipSendLimit 0 0 ∧ effective peer ipSendLimit 0 0 ≤ peer.limit ∧
      40 + effective peer ipSendLimit 0 0 ≤ ipSendLimit := by
  have positive := peer.limit_positive
  have room : 0 + 0 < min peer.limit (ipSendLimit - 40) := by omega
  simpa using effective_bounds peer ipSendLimit 0 0 room

end Netlib.Protocol.TCP.MSS
