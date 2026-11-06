import Netlib.Protocol.TCP.MSS
import Netlib.Protocol.TCP.ReceiveAdvertisement
import Netlib.Protocol.TCP.EstablishedReceive
import Netlib.Theory.TimedReaction

/-!
# ACK work from actual endpoint operations

The endpoint supplies its existing local clock and checked receive result.
A response consumes the whole pending group. Reads use the selected SWS rule.
The trace layer links these records to their actual issuer and packet output.
-/

namespace Netlib.Protocol.TCP.AckReaction

namespace T
export Netlib.Theory.TimedReaction (Cause Discharge State initial pendingDue credit issue checkTime completedState complete)
end T

inductive Kind where
  | data | sequence | window
  deriving Repr, BEq, DecidableEq

structure Demand where
  kind : Kind
  cursor : Seq
  position : Nat
  bytes : Nat
  minimumEdge : Nat := 0
  deriving Repr, BEq, DecidableEq

structure Acknowledgment where
  cursor : Seq
  position : Nat
  window : Nat
  deriving Repr, BEq, DecidableEq

abbrev Work := Netlib.Theory.TimedReaction.State Unit Demand Acknowledgment

structure State where
  origin : Seq
  rmss : Nat
  advertisement : ReceiveAdvertisement.State
  work : Work
  fullSegments : Nat := 0
  dataBytes : Nat := 0
  deriving Repr, BEq, DecidableEq

inductive Stop where
  | disabled | alreadyEnabled | noCredit | early | ledger | deadline | challenge
  deriving Repr, BEq, DecidableEq

def Stop.unsupported : Stop → Bool
  | .deadline | .challenge => true
  | _ => false

def fromTimeError : Netlib.Theory.TimedReaction.Error → Stop
  | .noCredit => .noCredit
  | .deadline => .deadline
  | .clock | .coverage => .ledger

def initial (cursor : Seq) (capacity rmss : Nat) : State :=
  ⟨cursor, rmss, ReceiveAdvertisement.initial capacity, T.initial (), 0, 0⟩

def State.window (state : State) : Nat := state.advertisement.window

def State.due (state : State) : Option Nat := T.pendingDue state.work

def State.credit (state : State) : Nat := T.credit state.work

def candidate (state : State) (capacity free outgoingMSS : Nat) : Nat :=
  ReceiveAdvertisement.candidate state.advertisement capacity free outgoingMSS

def State.Coherent (state : State) (cursor : Seq) (free rmss : Nat) : Prop :=
  state.advertisement.Valid free ∧ state.origin.add state.advertisement.frontier = cursor ∧
    state.rmss = rmss ∧ 0 < state.rmss ∧
    ∀ cause ∈ state.work.pending,
      cause.demand.position ≤ state.advertisement.frontier ∧
        cause.demand.cursor = state.origin.add cause.demand.position

instance (state : State) (cursor : Seq) (free rmss : Nat) : Decidable (state.Coherent cursor free rmss) := by
  unfold State.Coherent
  infer_instance

def checkTime (state : State) (now : Nat) : Except Stop Unit :=
  (T.checkTime state.work now).mapError fromTimeError

def demand (state : State) (kind : Kind) (cursor : Seq) (bytes minimumEdge : Nat) : Demand :=
  ⟨kind, cursor, state.advertisement.frontier, bytes, minimumEdge⟩

def receiveData (state : State) (now : Nat) (cursor : Seq) (count : Nat) : State :=
  let next := { state with
    advertisement := ReceiveAdvertisement.consume state.advertisement count
    fullSegments := state.fullSegments + if state.rmss ≤ count then 1 else 0
    dataBytes := state.dataBytes + count }
  let delay := if 2 ≤ next.fullSegments ∨ 2 * state.rmss ≤ next.dataBytes then 0 else 499
  { next with work := T.issue state.work now (demand next .data cursor count 0) delay }

def receiveSequence (state : State) (now : Nat) (cursor : Seq) : State :=
  { state with work := T.issue state.work now (demand state .sequence cursor 0 0) 0 }

def read (state : State) (now : Nat) (cursor : Seq) (capacity beforeFree afterFree outgoingMSS : Nat) : State :=
  let before := candidate state capacity beforeFree outgoingMSS
  let after := candidate state capacity afterFree outgoingMSS
  if before < after then
    { state with work := T.issue state.work now (demand state .window cursor 0 (state.advertisement.frontier + after)) 0 }
  else state

def acknowledgment (state : State) (cursor : Seq) (capacity free outgoingMSS : Nat) : Acknowledgment :=
  ⟨cursor, state.advertisement.frontier, candidate state capacity free outgoingMSS⟩

def covers (owed : Demand) (output : Acknowledgment) : Bool :=
  decide (owed.position ≤ output.position ∧ owed.minimumEdge ≤ output.position + output.window)

def outputReady (state : State) (now : Nat) (cursor : Seq) (capacity free outgoingMSS : Nat) : Except Stop Unit := do
  checkTime state now
  let output := acknowledgment state cursor capacity free outgoingMSS
  if state.work.pending.all (fun cause => covers cause.demand output) then return ()
  else throw .ledger

def outputState (state : State) (now : Nat) (cursor : Seq) (capacity free outgoingMSS : Nat) : State :=
  { state with
    advertisement := ReceiveAdvertisement.commit state.advertisement capacity free outgoingMSS
    work := if state.work.pending.isEmpty then state.work
      else T.completedState state.work now (acknowledgment state cursor capacity free outgoingMSS)
    fullSegments := 0
    dataBytes := 0 }

def responseReady (state : State) (now : Nat) (dueOnly : Bool) : Except Stop Unit := do
  checkTime state now
  if state.work.pending.isEmpty then throw .noCredit
  if dueOnly then
    match state.due with
    | none => throw .noCredit
    | some due => if now < due then throw .early else return ()
  else return ()

theorem initial_coherent (cursor : Seq) (capacity rmss : Nat) (positive : 0 < rmss) :
    (initial cursor capacity rmss).Coherent cursor capacity rmss := by
  simp [initial, State.Coherent, ReceiveAdvertisement.State.Valid, ReceiveAdvertisement.State.window,
    ReceiveAdvertisement.initial, T.initial, Netlib.Theory.TimedReaction.initial, positive]

theorem outputState_frontier (state : State) (now : Nat) (cursor : Seq) (capacity free outgoingMSS : Nat) :
    (outputState state now cursor capacity free outgoingMSS).advertisement.frontier = state.advertisement.frontier := rfl

theorem receiveData_frontier (state : State) (now : Nat) (cursor : Seq) (count : Nat) :
    (receiveData state now cursor count).advertisement.frontier = state.advertisement.frontier + count := rfl

end Netlib.Protocol.TCP.AckReaction
