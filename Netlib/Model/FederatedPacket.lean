import Netlib.Check.FederatedGuarantees

/-!
# One packet across independent native updates

The control key omits clocks and old send evidence. Concrete histories retain
that evidence separately. Public endpoint and border bindings stay fixed.
-/

namespace Netlib.Federation.InFlight

abbrev Node := Sum String String

structure Profile where
  queryID : String
  packetID : String
  leftFences : List (List String)
  rightFences : List (List String)
  cells : Nat
  work : Nat
  deriving Repr

structure Context (input : Input) where
  profile : Profile
  query : Query
  first : Case
  second : Case

def Context.sourceNode (context : Context input) : Node :=
  Composition.anchor input.left.initial input.right.initial context.query.source

def Context.targetNode (context : Context input) : Node :=
  Composition.anchor input.left.initial input.right.initial context.query.target

abbrev Cursors (input : Input) := input.left.Cursor × input.right.Cursor

inductive KeyPhase where
  | held (node : Node)
  | flight (receiver : Node)
  | delivered
  deriving Repr, DecidableEq

structure Key (input : Input) where
  current : Cursors input
  phase : KeyPhase
  deriving Repr, DecidableEq

inductive Move where
  | send (target : Node)
  | arrive
  | receive
  | updateLeft (index : Nat)
  | updateRight (index : Nat)
  | updateBoth (leftIndex rightIndex : Nat)
  deriving Repr, DecidableEq

def initialKey (context : Context input) : Key input :=
  ⟨Plan.jointInitial input.left input.right, .held context.sourceNode⟩

def finished (key : Key input) : Bool :=
  decide (key.phase = .delivered ∧ key.current.1.val = input.left.updates.length ∧
    key.current.2.val = input.right.updates.length)

def fixedRole : Role → Bool
  | .endpoint | .ingress | .egress => true
  | .enforcement | .internal => false

end Netlib.Federation.InFlight
