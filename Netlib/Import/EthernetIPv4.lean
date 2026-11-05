import Netlib.Import.EAPOL

/-!
# Untagged Ethernet IPv4 capture envelope

The payload retains the complete captured IPv4 bytes and trailing padding.
Capture metadata must exclude the Ethernet FCS and checksum-offload intermediates.
-/

namespace Netlib.Import.EthernetIPv4

abbrev MAC := EAPOL.MAC

structure Envelope where
  destination : MAC
  source : MAC
  payload : List UInt8
  deriving Repr, BEq, DecidableEq

def encode (frame : Envelope) : List UInt8 :=
  frame.destination.bytes ++ frame.source.bytes ++ [8, 0] ++ frame.payload

def decode (bytes : List UInt8) : Except String Envelope := do
  let (destination, rest) ← EAPOL.MAC.read bytes
  let (source, rest) ← EAPOL.MAC.read rest
  match rest with
  | 8 :: 0 :: payload => return ⟨destination, source, payload⟩
  | _ => throw "Require an untagged Ethernet IPv4 envelope with EtherType 0x0800."

theorem decode_encode (frame : Envelope) : decode (encode frame) = .ok frame := by
  simp [encode, List.append_assoc, decode, EAPOL.MAC.read_bytes, bind, Except.bind, pure]
  rfl

theorem encode_decode (bytes : List UInt8) (frame : Envelope) (accepted : decode bytes = .ok frame) :
    encode frame = bytes := by
  unfold decode at accepted
  cases first : EAPOL.MAC.read bytes with
  | error error => simp [first, bind, Except.bind] at accepted
  | ok pair =>
    rcases pair with ⟨destination, rest⟩
    cases second : EAPOL.MAC.read rest with
    | error error => simp [first, second, bind, Except.bind] at accepted
    | ok pair =>
      rcases pair with ⟨source, payload⟩
      simp only [first, second, bind, Except.bind] at accepted
      split at accepted
      · cases accepted
        rename_i tail
        simp only [encode, List.append_assoc]
        change destination.bytes ++ (source.bytes ++ (8 :: 0 :: tail)) = bytes
        rw [EAPOL.MAC.bytes_read _ _ _ second, EAPOL.MAC.bytes_read _ _ _ first]
      · cases accepted

def parseHex (text : String) : Except String Envelope := do
  decode (← EAPOL.bytesFromHex text)

end Netlib.Import.EthernetIPv4
