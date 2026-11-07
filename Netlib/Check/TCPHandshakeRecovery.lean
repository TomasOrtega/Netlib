import Netlib.Check.TCPHandshake
import Netlib.Protocol.TCP.HandshakeTimer
import Netlib.Protocol.TCP.HandshakeDuplicate
import Netlib.Protocol.TCP.ApplicationTraceFacts

/-!
# Actual startup controls with recovery

Control occurrences and receipts keep their event indices.
Early endpoint receives retain their actual application history.
-/

namespace Netlib.Check.TCPHandshakeRecovery

open Protocol.TCP

namespace H
export Handshake (Local Socket Input SynSent SynReceived ActiveEstablished PassiveEstablished)
end H
namespace O
export TCPHandshake (Opened Answered Acknowledged Completed Path)
end O
namespace X
export HandshakeExchange (DeliverySpec Delivery)
end X
namespace T
export HandshakeTimer (State Kind Flight Data)
end T
namespace A
export ApplicationTrace (Step Chain Chronological)
end A

inductive Side where
  | active | passive
  deriving Repr, BEq, DecidableEq

def Side.other : Side → Side
  | .active => .passive
  | .passive => .active

inductive Kind where
  | syn | synAck | finalAck | synReplyAck
  deriving Repr, BEq, DecidableEq

inductive Cause where
  | open
  | response (source : Nat)
  | timeout (source generation : Nat)
  | duplicateSyn (source : Nat)
  | duplicateSynAck (source : Nat)
  deriving Repr, BEq, DecidableEq

structure Emission where
  index : Nat
  actor : Side
  kind : Kind
  packet : H.Input
  cause : Cause

structure Receipt where
  index : Nat
  source : Emission
  spec : X.DeliverySpec
  delivery : X.Delivery source.packet spec
  earlier : source.index < index

def Receipt.actor (receipt : Receipt) : Side := receipt.source.actor.other

structure PreData (seed : Endpoint.State) where
  current : Endpoint.State
  valid : current.Valid
  steps : List A.Step
  chain : A.Chain seed steps current
  ordered : A.Chronological steps

def PreData.initial (seed : Endpoint.State) (valid : seed.Valid) : PreData seed :=
  ⟨seed, valid, [], .nil seed, .nil⟩

structure ReceivedAck (before : PreData seed) (packet : H.Input) (index : Nat) where
  profile : Handshake.Profile packet 16
  tuple : packet.packet.header = before.current.core.inbound
  coordinates : packet.packet.segment.sequence = before.current.core.receiveNext ∧
    packet.packet.segment.acknowledgment = before.current.core.sendUna
  operation : A.Step
  beforeEq : operation.before = before.current
  event : operation.event = .receive packet
  stamp : operation.stamp = index
  accepted : operation.result.decision = .accepted (.receive 0 0)
  quiet : operation.result.output = none
  read : operation.result.read = []
  after : PreData seed
  state : after.current = operation.result.state
  history : after.steps = before.steps ++ [operation]

def PreData.receiveAck (before : PreData seed) (packet : H.Input) (index : Nat) :
    Except String (ReceivedAck before packet index) := do
  if profile : Handshake.Profile packet 16 then
    if tuple : packet.packet.header = before.current.core.inbound then
      if coordinates : packet.packet.segment.sequence = before.current.core.receiveNext ∧
          packet.packet.segment.acknowledgment = before.current.core.sendUna then
        if earlier : ∀ old ∈ before.steps, old.stamp < index then
          let operation := ApplicationTrace.Step.make before.current before.valid (.receive packet) index
          if accepted : operation.result.decision = .accepted (.receive 0 0) then
            if quiet : operation.result.output = none then
              if read : operation.result.read = [] then
                let after : PreData seed := ⟨operation.result.state, operation.valid,
                  before.steps ++ [operation], before.chain.snoc,
                  ApplicationTrace.chronological_snoc before.ordered earlier⟩
                return ⟨profile, tuple, coordinates, operation, rfl, rfl, rfl, accepted, quiet, read, after, rfl, rfl⟩
              else throw "A startup ACK cannot read application bytes."
            else throw "The selected startup ACK requires another endpoint output."
          else throw "The selected startup ACK is outside the empty pre-data receive profile."
        else throw "A startup endpoint receive must follow its earlier local operations."
      else throw "The startup ACK does not match the current empty stream cursors."
    else throw "The startup ACK does not match the current endpoint tuple."
  else throw "The startup ACK requires a bare data-free ACK profile."

inductive Phase (active passive : H.Local) where
  | idle
  | opened (value : O.Opened active)
  | answered (value : O.Answered active passive)
  | acknowledged (value : O.Acknowledged active passive) (client : PreData value.ready.seed)
  | complete (value : O.Completed active passive)
      (client : PreData value.certificate.activeSeed) (server : PreData value.certificate.passiveSeed)

structure State (active passive : H.Local) where
  phase : Phase active passive := .idle
  activeTimer : T.State := HandshakeTimer.initial
  passiveTimer : T.State := HandshakeTimer.initial
  activeValid : activeTimer.Valid
  passiveValid : passiveTimer.Valid
  emissions : List Emission := []
  receipts : List Receipt := []
  last : Option Nat := none

def State.initial : State active passive := {
  activeValid := HandshakeTimer.initial_valid (rto := 1000) (now := 0) (by decide)
  passiveValid := HandshakeTimer.initial_valid (rto := 1000) (now := 0) (by decide) }

def State.timer (state : State active passive) : Side → T.State
  | .active => state.activeTimer
  | .passive => state.passiveTimer

theorem State.timer_valid (state : State active passive) (actor : Side) : (state.timer actor).Valid := by
  cases actor
  · exact state.activeValid
  · exact state.passiveValid

def State.withTimer (state : State active passive) (actor : Side) (timer : T.State) (valid : timer.Valid) :
    State active passive :=
  match actor with
  | .active => { state with activeTimer := timer, activeValid := valid }
  | .passive => { state with passiveTimer := timer, passiveValid := valid }

def State.source (state : State active passive) (index : Nat) : Option Emission :=
  state.emissions.find? (fun output => output.index == index)

inductive Event where
  | activeOpen (remote : H.Socket) (policy : Bool)
  | receive (source : Nat) (bytes : List UInt8) (path : O.Path) (policy : Bool)
  | advanceClock (actor : Side) (millis : Nat)
  | timeout (actor : Side) (generation : Nat) (policy : Bool)

inductive Decision where
  | accepted | discarded | obsolete
  deriving Repr, BEq, DecidableEq

structure Effect (active passive : H.Local) where
  state : State active passive
  decision : Decision := .accepted
  output : Option Emission := none
  receipt : Option Receipt := none
  application : Option (Side × A.Step) := none

def publish (state : State active passive) (output : Emission) : Effect active passive :=
  ⟨{ state with emissions := state.emissions ++ [output] }, .accepted, some output, none, none⟩

def retainReceipt (effect : Effect active passive) (receipt : Receipt) : Effect active passive :=
  { effect with state := { effect.state with receipts := effect.state.receipts ++ [receipt] }, receipt := some receipt }

def finish (before : O.Acknowledged active passive) (index : Nat) (spec : X.DeliverySpec)
    (ack : X.Delivery before.ready.output spec)
    (passiveReady : H.PassiveEstablished before.answered.pending ack.input)
    (computed : Handshake.synReceivedAck before.answered.pending ack.input = .ok passiveReady)
    (ordered : before.answered.opened.index < before.answered.index ∧ before.answered.index < before.index ∧ before.index < index) :
    O.Completed active passive := {
  input := {
    active, passive, remote := before.answered.opened.remote
    openPolicy := before.answered.opened.policy, synPolicy := before.answered.policy, synAckPolicy := before.policy
    syn := before.answered.spec, synAck := before.spec, ack := spec
    times := ⟨before.answered.opened.index, before.answered.index, before.index, index⟩ }
  certificate := {
    ordered
    activePending := before.answered.opened.pending, opened := before.answered.opened.computed
    syn := before.answered.delivery, passivePending := before.answered.pending, listened := before.answered.computed
    synAck := before.delivery, active := before.ready, activeComputed := before.computed
    ack, passive := passiveReady, passiveComputed := computed }
  activeConfig := rfl
  passiveConfig := rfl }

def State.applicationSteps (state : State active passive) (actor : Side) : List A.Step :=
  match state.phase, actor with
  | .acknowledged _ client, .active => client.steps
  | .complete _ client _, .active => client.steps
  | .complete _ _ server, .passive => server.steps
  | _, _ => []

def applicationFor (actor : Side) (selected : Option (Side × A.Step)) : Option A.Step :=
  selected.bind fun pair => if pair.1 = actor then some pair.2 else none

def AckOperation (packet : H.Input) (index : Nat) (operation : A.Step) : Prop :=
  Handshake.Profile packet 16 ∧ operation.event = .receive packet ∧
    packet.packet.header = operation.before.core.inbound ∧
    packet.packet.segment.sequence = operation.before.core.receiveNext ∧
    packet.packet.segment.acknowledgment = operation.before.core.sendUna ∧
    operation.result.decision = .accepted (.receive 0 0) ∧ operation.result.output = none ∧
    operation.result.read = [] ∧ operation.stamp = index

def ApplicationReceipt (effect : Effect active passive) (index : Nat) (actor : Side) (operation : A.Step) : Prop :=
  ∃ receipt, effect.receipt = some receipt ∧ receipt.actor = actor ∧
    AckOperation receipt.delivery.input index operation

end Netlib.Check.TCPHandshakeRecovery
