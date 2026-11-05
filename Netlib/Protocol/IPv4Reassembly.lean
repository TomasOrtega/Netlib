import Netlib.Protocol.IPv4InputFragment

/-!
# Stateful IPv4 input reassembly

The selected Linux profile has IHL five, successful allocation, and ipfrag_max_dist
zero. Domain.user already includes the defragmentation user and conntrack zone;
Domain.vif is the L3 master identity. Queue expiry uses the supplied monotonic clock.
Runs retain Linux's tail-append grouping, which affects duplicate classification.
-/

namespace Netlib.Protocol.IPv4Reassembly

open Packet InternetChecksum

structure Domain where
  user : Nat
  vif : Nat := 0
  deriving Repr, BEq, DecidableEq

structure Key where
  domain : Domain
  source : Address
  destination : Address
  protocol : Packet.Protocol
  identification : Word
  deriving Repr, BEq, DecidableEq

def key (domain : Domain) (fragment : IPv4Fragment.Decoded) : Key :=
  ⟨domain, fragment.packet.source, fragment.packet.destination, fragment.packet.protocol,
    fragment.packet.identification⟩

structure Policy where
  timeout : Nat
  deriving Repr, BEq, DecidableEq

structure Piece where
  fragment : IPv4Fragment.Decoded
  data : List UInt8
  deriving Repr, BEq, DecidableEq

def Piece.start (piece : Piece) : Nat := piece.fragment.packet.offset.val * 8
def Piece.stop (piece : Piece) : Nat := piece.start + piece.data.length

def normalize (fragment : IPv4Fragment.Decoded) : Piece :=
  ⟨fragment, if fragment.packet.moreFragments then
    fragment.packet.payload.take (fragment.packet.payload.length / 8 * 8) else fragment.packet.payload⟩

structure Run where
  first : Piece
  rest : List Piece := []
  deriving Repr, BEq, DecidableEq

def Run.pieces (run : Run) : List Piece := run.first :: run.rest
def Run.start (run : Run) : Nat := run.first.start
def Run.stop (run : Run) : Nat := run.start + (run.pieces.flatMap (·.data)).length

def Run.append (run : Run) (piece : Piece) : Run := { run with rest := run.rest ++ [piece] }

def Run.contains (run : Run) (piece : Piece) : Bool :=
  decide (run.start ≤ piece.start ∧ piece.stop ≤ run.stop)

def Run.overlaps (run : Run) (piece : Piece) : Bool :=
  decide (piece.start < run.stop ∧ run.start < piece.stop)

/-- Internal gap fills remain separate runs even when they touch both neighbors. -/
def insert (piece : Piece) : List Run → List Run
  | [] => [⟨piece, []⟩]
  | run :: rest =>
    if piece.start < run.start then ⟨piece, []⟩ :: run :: rest
    else match rest with
      | [] => if piece.start = run.stop then [run.append piece] else [run, ⟨piece, []⟩]
      | next :: tail => run :: insert piece (next :: tail)

def joinAt (expected : Nat) : List Piece → Option (List UInt8)
  | [] => some []
  | piece :: rest =>
    if piece.start = expected then (joinAt piece.stop rest).map (piece.data ++ ·) else none

structure Queue where
  key : Key
  expires : Nat
  runs : List Run := []
  length : Nat := 0
  last : Bool := false
  first : Option IPv4.Packet := none
  ecn : Nat := 0
  maxSize : Nat := 0
  maxDFSize : Nat := 0
  deriving Repr, BEq, DecidableEq

def Queue.pieces (queue : Queue) : List Piece := queue.runs.flatMap Run.pieces

def Queue.meat (queue : Queue) : Nat := (queue.pieces.flatMap (·.data)).length

structure State where
  queues : List Queue := []
  lastTime : Nat := 0
  deriving Repr, BEq, DecidableEq

def State.initial : State := ⟨[], 0⟩

def State.age (state : State) (now : Nat) : State :=
  { state with queues := state.queues.filter (fun queue => decide (now < queue.expires)) }

def State.lookup (state : State) (wanted : Key) : Option Queue :=
  state.queues.find? (fun queue => decide (queue.key = wanted))

def State.erase (state : State) (wanted : Key) : State :=
  { state with queues := state.queues.filter (fun queue => decide (queue.key ≠ wanted)) }

def State.put (state : State) (queue : Queue) : State :=
  { state with queues := queue :: (state.erase queue.key).queues }

inductive Disposition where
  | whole | buffered | duplicate | overlap | inconsistentLength | empty | invalidECN | tooLarge | complete | invalidLayout
  deriving Repr, BEq, DecidableEq

structure Output where
  packet : IPv4.Packet
  pieces : List Piece
  maxSize : Nat
  maxDFSize : Nat
  reassembled : Bool
  deriving Repr, BEq, DecidableEq

inductive Completion where
  | waiting
  | rejected (reason : Disposition)
  | accepted (output : Output)
  deriving Repr, BEq, DecidableEq

def Queue.complete (queue : Queue) : Completion :=
  match queue.first with
  | none => .waiting
  | some first =>
    if queue.last && decide (queue.meat = queue.length) then
      if queue.ecn % 2 = 1 ∧ 1 < queue.ecn then .rejected .invalidECN
      else if 65535 < queue.length + 20 then .rejected .tooLarge
      else match joinAt 0 queue.pieces with
        | none => .rejected .invalidLayout
        | some payload =>
          let tos := if 8 ≤ queue.ecn then UInt8.ofNat (first.tos.toNat / 4 * 4 + 3) else first.tos
          .accepted ⟨{ first with payload, tos, dontFragment := decide (queue.maxDFSize = queue.maxSize) },
            queue.pieces, queue.maxSize, queue.maxDFSize, true⟩
    else .waiting

structure Result where
  state : State
  disposition : Disposition
  output : Option Output := none
  deriving Repr, BEq, DecidableEq

inductive Error where
  | invalidTimeout | backwardsClock | invalidFragment
  deriving Repr, BEq, DecidableEq

def Error.describe : Error → String
  | .invalidTimeout => "The fragment queue timeout must be positive."
  | .backwardsClock => "Fragment arrival times must be monotonic."
  | .invalidFragment => "The input fragment length or IPv4 header checksum is invalid."

def queuedLength (queue : Queue) (piece : Piece) : Option Queue :=
  if piece.fragment.packet.moreFragments then
    if queue.last && decide (queue.length < piece.stop) then none
    else some { queue with length := max queue.length piece.stop }
  else if piece.stop < queue.length ∨ (queue.last = true ∧ piece.stop ≠ queue.length) then none
  else some { queue with length := piece.stop, last := true }

def store (queue : Queue) (piece : Piece) : Queue :=
  let size := piece.data.length + 20
  { queue with
    runs := insert piece queue.runs
    first := if piece.start = 0 then some piece.fragment.packet.toPacket else queue.first
    ecn := queue.ecn ||| (2 ^ (piece.fragment.packet.tos.toNat % 4))
    maxSize := max queue.maxSize size
    maxDFSize := if piece.fragment.packet.dontFragment then max queue.maxDFSize size else queue.maxDFSize }

def accept (state : State) (queue : Queue) (piece : Piece) : Result :=
  if piece.data.isEmpty then ⟨state.erase queue.key, .empty, none⟩
  else if queue.runs.any (·.contains piece) then ⟨state.put queue, .duplicate, none⟩
  else if queue.runs.any (·.overlaps piece) then ⟨state.erase queue.key, .overlap, none⟩
  else
    let next := store queue piece
    match next.complete with
    | .waiting => ⟨state.put next, .buffered, none⟩
    | .rejected reason => ⟨state.erase queue.key, reason, none⟩
    | .accepted output => ⟨state.erase queue.key, .complete, some output⟩

def process (policy : Policy) (before : State) (now : Nat) (domain : Domain)
    (fragment : IPv4Fragment.Decoded) : Result :=
  let state := { before.age now with lastTime := now }
  if !fragment.packet.moreFragments && decide (fragment.packet.offset.val = 0) then
    ⟨state, .whole, some ⟨fragment.packet.toPacket, [⟨fragment, fragment.packet.payload⟩], 0, 0, false⟩⟩
  else
  let wanted := key domain fragment
  let queue := (state.lookup wanted).getD { key := wanted, expires := now + policy.timeout }
  let piece := normalize fragment
  match queuedLength queue piece with
  | none => ⟨state.erase wanted, .inconsistentLength, none⟩
  | some queue => accept state queue piece

def arrive (policy : Policy) (before : State) (now : Nat) (domain : Domain)
    (fragment : IPv4Fragment.Decoded) : Except Error Result :=
  if policy.timeout = 0 then .error .invalidTimeout
  else if now < before.lastTime then .error .backwardsClock
  else if ¬fragment.packet.wireLength < 65536 ∨
      InternetChecksum.valid (IPv4Fragment.headerBytes fragment.packet fragment.checksum) ≠ true then
    .error .invalidFragment
  else .ok (process policy before now domain fragment)

end Netlib.Protocol.IPv4Reassembly
