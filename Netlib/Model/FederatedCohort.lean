import Netlib.Model.FederatedPacketExecution
import Netlib.Check.FederatedPacketControl

/-!
# Finite packets with shared receiver buffers

Each flight reserves one receiver slot. Queues contain packet indices, while
immutable packet contexts retain external identities and selected queries.
-/

namespace Netlib.Federation.Cohort

namespace I
export InFlight (Node Cursors KeyPhase Phase Stamp Observation)
end I

structure Capacity where
  node : I.Node
  slots : Nat
  deriving Repr, DecidableEq

abbrev Queues (input : Input) (size : Nat) :=
  Vector (List (Fin size)) (InFlight.Control.nodes input).length

structure Context (input : Input) (size : Nat) where
  packets : Vector (InFlight.Context input) size
  capacities : Vector Nat (InFlight.Control.nodes input).length

def Context.Unique (context : Context input size) : Prop :=
  (context.packets.toList.map (fun packet => packet.profile.packetID)).Nodup

def nodeAt (input : Input) (index : Fin (InFlight.Control.nodes input).length) : I.Node :=
  (InFlight.Control.nodes input).get index

def nodeIndex (input : Input) (node : I.Node) : Option (Fin (InFlight.Control.nodes input).length) :=
  (List.finRange (InFlight.Control.nodes input).length).find? fun index => decide (nodeAt input index = node)

def queueAt (queues : Queues input size) (node : I.Node) : List (Fin size) :=
  ((nodeIndex input node).map queues.get).getD []

def putQueue (queues : Queues input size) (node : I.Node) (values : List (Fin size)) : Queues input size :=
  match nodeIndex input node with
  | none => queues
  | some index => queues.set index.val values index.isLt

inductive PacketMove where
  | send (target : I.Node)
  | arrive
  | receive
  deriving Repr, DecidableEq

def PacketMove.local : PacketMove → InFlight.Move
  | .send target => .send target
  | .arrive => .arrive
  | .receive => .receive

inductive Move (size : Nat) where
  | packet (index : Fin size) (move : PacketMove)
  | updateLeft (index : Nat)
  | updateRight (index : Nat)
  | updateBoth (leftIndex rightIndex : Nat)
  deriving Repr, DecidableEq

def Move.local (move : Move size) (index : Fin size) : Option InFlight.Move :=
  match move with
  | .packet selected action => if selected = index then some action.local else none
  | .updateLeft cursor => some (.updateLeft cursor)
  | .updateRight cursor => some (.updateRight cursor)
  | .updateBoth first second => some (.updateBoth first second)

structure Key (input : Input) (size : Nat) where
  current : I.Cursors input
  phases : Vector I.KeyPhase size
  queues : Queues input size
  deriving Repr, DecidableEq

def Key.packet (key : Key input size) (index : Fin size) : InFlight.Key input :=
  ⟨key.current, key.phases.get index⟩

structure State (input : Input) (size : Nat) where
  current : I.Cursors input
  phases : Vector (I.Phase input) size
  queues : Queues input size
  nextIndex : Nat
  deriving Repr, DecidableEq

def State.packet (state : State input size) (index : Fin size) : InFlight.State input :=
  ⟨state.current, state.phases.get index, state.nextIndex⟩

def State.key (state : State input size) : Key input size :=
  ⟨state.current, state.phases.map InFlight.Phase.key, state.queues⟩

@[simp] theorem State.packet_key (state : State input size) (index : Fin size) :
    (state.packet index).key = state.key.packet index := by
  simp [State.packet, State.key, Key.packet, InFlight.State.key, Vector.get, Fin.cast]

def initialQueues (context : Context input size) : Queues input size :=
  Vector.ofFn fun node => (List.finRange size).filter fun packet =>
    decide ((context.packets.get packet).sourceNode = nodeAt input node)

def initialKey (context : Context input size) : Key input size :=
  ⟨Plan.jointInitial input.left input.right,
    context.packets.map (fun packet => .held packet.sourceNode), initialQueues context⟩

def initialState (context : Context input size) : State input size :=
  ⟨Plan.jointInitial input.left input.right,
    context.packets.map (fun packet => .held packet.sourceNode), initialQueues context, 0⟩

@[simp] theorem initialState_packet (context : Context input size) (index : Fin size) :
    (initialState context).packet index = InFlight.initialState (context.packets.get index) := by
  simp [initialState, State.packet, InFlight.initialState, Vector.get, Fin.cast]

def finished (key : Key input size) : Bool :=
  (List.finRange size).all (fun index => decide (key.phases.get index = .delivered)) &&
    decide (key.current.1.val = input.left.updates.length ∧ key.current.2.val = input.right.updates.length)

def packetIndex (context : Context input size) (packetID : String) : Option (Fin size) :=
  (List.finRange size).find? fun index => decide ((context.packets.get index).profile.packetID = packetID)

def actionMove (context : Context input size) : InFlight.Action → Except String (Option (Move size))
  | .idle => .ok none
  | .updateLeft index => .ok (some (.updateLeft index))
  | .updateRight index => .ok (some (.updateRight index))
  | .updateBoth first second => .ok (some (.updateBoth first second))
  | .send observation target =>
    match packetIndex context observation.packetID with
    | none => .error "The send packet ID is outside the cohort."
    | some index => .ok (some (.packet index (.send target)))
  | .arrive observation _ =>
    match packetIndex context observation.packetID with
    | none => .error "The arrival packet ID is outside the cohort."
    | some index => .ok (some (.packet index .arrive))
  | .receive observation =>
    match packetIndex context observation.packetID with
    | none => .error "The receipt packet ID is outside the cohort."
    | some index => .ok (some (.packet index .receive))

def projectAction (context : Context input size) (action : InFlight.Action) (index : Fin size) : InFlight.Action :=
  match actionMove context action with
  | .ok (some (.packet selected _)) => if selected = index then action else .idle
  | .ok (some _) => action
  | _ => .idle

def canonicalAction (context : Context input size) (headers : Vector Packet.Header size)
    (state : State input size) : Move size → InFlight.Action
  | .packet index move =>
    InFlight.canonicalAction (context.packets.get index) (headers.get index) (state.packet index) move.local
  | .updateLeft index => .updateLeft index
  | .updateRight index => .updateRight index
  | .updateBoth first second => .updateBoth first second

structure Outcome (input : Input) (size : Nat) where
  after : State input size
  effects : Vector (InFlight.Effect input) size
  deriving Repr, DecidableEq

structure Event (input : Input) (size : Nat) where
  action : InFlight.Action
  effects : Vector (InFlight.Effect input) size
  deriving Repr, DecidableEq

def Event.packet (context : Context input size) (event : Event input size) (index : Fin size) : InFlight.Event input :=
  ⟨projectAction context event.action index, event.effects.get index⟩

end Netlib.Federation.Cohort
