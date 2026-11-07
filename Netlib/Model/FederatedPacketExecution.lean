import Netlib.Model.FederatedPacket

/-!
# Packet observations and retained send stamps

Only a send creates a flight stamp. Arrival consumes that exact stamp.
The control key omits clocks, receipt indices, and historical sender data.
-/

namespace Netlib.Federation.InFlight

structure Observation where
  packetID : String
  header : Packet.Header
  node : Node
  deriving Repr, DecidableEq

structure Stamp (input : Input) where
  current : Cursors input
  source : Node
  target : Node
  packetID : String
  header : Packet.Header
  sendIndex : Nat
  deriving Repr, DecidableEq

inductive Phase (input : Input) where
  | held (node : Node)
  | flight (stamp : Stamp input)
  | delivered (receiveIndex : Nat)
  deriving Repr, DecidableEq

def Phase.key : Phase input → KeyPhase
  | .held node => .held node
  | .flight stamp => .flight stamp.target
  | .delivered _ => .delivered

structure State (input : Input) where
  current : Cursors input
  phase : Phase input
  nextIndex : Nat
  deriving Repr, DecidableEq

def State.key (state : State input) : Key input := ⟨state.current, state.phase.key⟩

def initialState (context : Context input) : State input :=
  ⟨Plan.jointInitial input.left input.right, .held context.sourceNode, 0⟩

@[simp] theorem initialState_key (context : Context input) :
    (initialState context).key = initialKey context := rfl

inductive Action where
  | idle
  | send (observation : Observation) (target : Node)
  | arrive (observation : Observation) (sendIndex : Nat)
  | receive (observation : Observation)
  | updateLeft (index : Nat)
  | updateRight (index : Nat)
  | updateBoth (leftIndex rightIndex : Nat)
  deriving Repr, DecidableEq

def Action.move? : Action → Option Move
  | .idle => none
  | .send _ target => some (.send target)
  | .arrive _ _ => some .arrive
  | .receive _ => some .receive
  | .updateLeft index => some (.updateLeft index)
  | .updateRight index => some (.updateRight index)
  | .updateBoth first second => some (.updateBoth first second)

def Context.observation (context : Context input) (header : Packet.Header) (node : Node) : Observation :=
  ⟨context.profile.packetID, header, node⟩

def canonicalAction (context : Context input) (header : Packet.Header) (state : State input) : Move → Action
  | .send target =>
    match state.phase with
    | .held source => .send (context.observation header source) target
    | _ => .send (context.observation header context.sourceNode) target
  | .arrive =>
    match state.phase with
    | .flight stamp => .arrive (context.observation header stamp.target) stamp.sendIndex
    | _ => .arrive (context.observation header context.targetNode) state.nextIndex
  | .receive =>
    match state.phase with
    | .held node => .receive (context.observation header node)
    | _ => .receive (context.observation header context.targetNode)
  | .updateLeft index => .updateLeft index
  | .updateRight index => .updateRight index
  | .updateBoth first second => .updateBoth first second

@[simp] theorem canonicalAction_move (context : Context input) (header : Packet.Header)
    (state : State input) (move : Move) : (canonicalAction context header state move).move? = some move := by
  rcases state with ⟨current, phase, index⟩
  cases move <;> cases phase <;> rfl

inductive Effect (input : Input) where
  | idle
  | sent (stamp : Stamp input)
  | arrived (stamp : Stamp input)
  | received (observation : Observation) (current : Cursors input) (receiveIndex : Nat)
  | updated (move : Move) (before after : Cursors input)
  deriving Repr, DecidableEq

structure Event (input : Input) where
  action : Action
  effect : Effect input
  deriving Repr, DecidableEq

structure Outcome (input : Input) where
  after : State input
  effect : Effect input
  deriving Repr, DecidableEq

end Netlib.Federation.InFlight
