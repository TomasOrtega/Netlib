import Netlib.Import.LinuxDeployment
import Netlib.Network.Contract
import Netlib.Check.Traffic

/-!
# Public contracts and private native revisions

Public node names belong to one operator. Each native revision supplies its
own projection and exact anchors for paths through the public graph.
-/

namespace Netlib.Federation

inductive Role where
  | endpoint | enforcement | ingress | egress | internal
  deriving Repr, DecidableEq

structure PublicNode where
  id : String
  role : Role
  deriving Repr, DecidableEq

structure Arc where
  source : String
  target : String
  deriving Repr, DecidableEq

structure Case where
  id : String
  selector : Packet.Match
  request : ZeroTrust.Request String String String
  upper : List Arc
  must : List Arc

structure Contract where
  id : String
  version : Nat
  nodes : List PublicNode
  cases : List Case

def Contract.ids (contract : Contract) : List String := contract.nodes.map (·.id)

def Contract.node? (contract : Contract) (id : String) : Option PublicNode :=
  contract.nodes.find? (·.id == id)

def Contract.case? (contract : Contract) (id : String) : Option Case := contract.cases.find? (·.id == id)

def arcs (edges : List Arc) (source target : String) : Bool := edges.contains ⟨source, target⟩

def Contract.upperModel (contract : Contract) (selected : Case) : Network String :=
  Certificate.finiteNetwork contract.ids (arcs selected.upper)

def Contract.mustModel (contract : Contract) (selected : Case) : Network String :=
  Certificate.finiteNetwork contract.ids (arcs selected.must)

structure NodeMap where
  localNode : String
  publicNode : String
  deriving Repr, DecidableEq

structure Anchor where
  publicNode : String
  localNode : String
  deriving Repr, DecidableEq

structure Revision where
  id : String
  snapshot : Import.LinuxDeployment.Snapshot
  projection : List NodeMap
  anchors : List Anchor

def Revision.project (revision : Revision) (node : String) : String :=
  ((revision.projection.find? (·.localNode == node)).map (·.publicNode)).getD ""

def Revision.anchor (revision : Revision) (node : String) : String :=
  ((revision.anchors.find? (·.publicNode == node)).map (·.localNode)).getD ""

def Revision.native (revision : Revision) (selected : Case) (header : Packet.Header) : Network String :=
  revision.snapshot.nativeModel header selected.request

structure Plan where
  contract : Contract
  initial : Revision
  updates : List Revision

def Plan.versions (plan : Plan) : List Revision := plan.initial :: plan.updates

inductive Side where
  | left | right
  deriving Repr, DecidableEq

structure PublicRef where
  side : Side
  node : String
  deriving Repr, DecidableEq

structure Border where
  source : PublicRef
  target : PublicRef
  sourceDomain : String
  targetDomain : String
  sourceVersion : Nat
  targetVersion : Nat
  cases : List String
  deriving Repr, DecidableEq

structure Query where
  id : String
  kind : DataPlane.Kind
  caseID : String
  source : PublicRef
  target : PublicRef
  gateways : List PublicRef := []
  deriving Repr, DecidableEq

structure Intent where
  borders : List Border
  queries : List Query
  deriving Repr

def contracts (left right : Contract) : Side → Contract
  | .left => left
  | .right => right

def references (left right : Contract) : List PublicRef :=
  left.ids.map (⟨.left, ·⟩) ++ right.ids.map (⟨.right, ·⟩)

def borderEdge (borders : List Border) (caseID : String) (source target : PublicRef) : Bool :=
  borders.any fun border => decide (border.source = source ∧ border.target = target) && border.cases.contains caseID

def publicEdge (first second : Case) (borders : List Border)
    (source target : PublicRef) (must : Bool) : Bool :=
  match source.side, target.side with
  | .left, .left => arcs (if must then first.must else first.upper) source.node target.node
  | .right, .right => arcs (if must then second.must else second.upper) source.node target.node
  | _, _ => borderEdge borders first.id source target

def publicModel (left right : Contract) (first second : Case) (borders : List Border) (must : Bool) :
    Network PublicRef :=
  Certificate.finiteNetwork (references left right) (publicEdge first second borders · · must)

end Netlib.Federation
