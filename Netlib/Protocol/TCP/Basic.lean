import Netlib.Protocol.IPv4

/-! Wire fields keep sequence-number representation separate from serial comparison. -/

namespace Netlib.Protocol.TCP

abbrev Word32 := Fin 4294967296
abbrev Nibble := Fin 16

structure Seq where
  bits : Word32
  deriving Repr, BEq, DecidableEq

def Seq.val (value : Seq) : Nat := value.bits.val

def Seq.ofNat (value : Nat) : Seq := ⟨⟨value % 4294967296, Nat.mod_lt _ (by decide)⟩⟩

theorem Seq.val_lt (value : Seq) : value.val < 4294967296 := value.bits.isLt

theorem Seq.ext {first second : Seq} (same : first.val = second.val) : first = second := by
  cases first
  cases second
  congr
  exact Fin.ext same

def word32Bytes (value : Word32) : List UInt8 := IPv4.addressBytes value
def read32 (a b c d : UInt8) : Word32 := IPv4.readAddress a b c d
def seqBytes (value : Seq) : List UInt8 := word32Bytes value.bits
def readSeq (a b c d : UInt8) : Seq := ⟨read32 a b c d⟩

@[simp] theorem word32Bytes_length (value : Word32) : (word32Bytes value).length = 4 := IPv4.addressBytes_length value
@[simp] theorem seqBytes_length (value : Seq) : (seqBytes value).length = 4 := word32Bytes_length value.bits

theorem read32_bytes (value : Word32) :
    read32 (InternetChecksum.highByte (IPv4.highWord value)) (InternetChecksum.lowByte (IPv4.highWord value))
      (InternetChecksum.highByte (IPv4.lowWord value)) (InternetChecksum.lowByte (IPv4.lowWord value)) = value :=
  IPv4.readAddress_bytes value

theorem word32Bytes_read32 (a b c d : UInt8) : word32Bytes (read32 a b c d) = [a, b, c, d] :=
  IPv4.addressBytes_readAddress a b c d

@[simp] theorem seqBytes_readSeq (a b c d : UInt8) : seqBytes (readSeq a b c d) = [a, b, c, d] :=
  word32Bytes_read32 a b c d

namespace Flags

def contains (flags : UInt8) (bit : Nat) : Bool := flags.toNat / (2 ^ bit) % 2 == 1
def fin (flags : UInt8) : Bool := contains flags 0
def syn (flags : UInt8) : Bool := contains flags 1
def rst (flags : UInt8) : Bool := contains flags 2
def psh (flags : UInt8) : Bool := contains flags 3
def ack (flags : UInt8) : Bool := contains flags 4
def urg (flags : UInt8) : Bool := contains flags 5
def ece (flags : UInt8) : Bool := contains flags 6
def cwr (flags : UInt8) : Bool := contains flags 7

end Flags
end Netlib.Protocol.TCP
