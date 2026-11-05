import Std

/-!
# Checked immutable packet bytes

The packet and its bytes share one decoder equation.
The source does not assert a transmission or delivery history.
-/

namespace Netlib.Protocol

universe u

structure WireSource (α : Type u) (decode : List UInt8 → Except String α) where
  bytes : List UInt8
  packet : α
  decoded : decode bytes = .ok packet

namespace WireSource

def read (decode : List UInt8 → Except String α) (bytes : List UInt8) : Except String (WireSource α decode) :=
  match decoded : decode bytes with
  | .error reason => .error reason
  | .ok packet => .ok ⟨bytes, packet, decoded⟩

theorem read_bytes (decode : List UInt8 → Except String α) (bytes : List UInt8) (source : WireSource α decode)
    (accepted : read decode bytes = .ok source) : source.bytes = bytes := by
  unfold read at accepted
  split at accepted
  · cases accepted
  · cases accepted
    rfl

end WireSource

end Netlib.Protocol
