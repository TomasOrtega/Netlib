import Netlib.Examples.CampusDirect

namespace NetlibTest.CampusDirect
open Netlib Packet Protocol Network Examples
open Examples.CampusDirect

private def context : Context := ⟨"wired-client", "campus-application", "campus-authority"⟩
private def scope : Scope := ⟨"campus-application", "use"⟩
private def credential : Credential := ⟨context.issuer, context.consumer, context.producer, [scope], 100, true⟩
private def session : EAPSession.State :=
  ⟨EAPAuth.State.initial, { authenticated := true, credential := some credential, now := 10 }⟩
private def nodes : List Node := [.client, .primary, .standby, .server, .management]
private def campusNodes : List Campus.Node := [.client, .apA, .gatewayA, .apB, .gatewayB, .server, .management]

example (state : EAPSession.State) (selectedScope : Scope) (withdrawn : Bool) :
    Duplex (network context state selectedScope withdrawn) ↔ state.session.permits context selectedScope = true :=
  duplex_reachable_iff context state selectedScope withdrawn

example (state : EAPSession.State) (selectedScope : Scope) (withdrawn : Bool)
    (gateway : StatefulFailover.Gateway) (direction : FlowNAT.Direction)
    (permitted : state.session.permits context selectedScope = true) (live : withdrawn = false ∨ gateway = .standby) :
    Walk (network context state selectedScope withdrawn) (source direction) (target direction) (routeTrace gateway direction) :=
  selected_route context state selectedScope withdrawn gateway direction permitted live

private instance (a b : Node) : Decidable (physical.link a b) := by
  simp only [physical, endpoints, clients, servers, gateways]
  infer_instance

private instance (node : Node) : Decidable (gateways node) := by
  unfold gateways
  infer_instance

private instance (a b : Campus.Node) : Decidable (CampusDuplex.physical.link a b) := by
  simp only [CampusDuplex.physical, CampusNAT.physical, Network.union, Campus.base, Campus.access, Campus.distribution]
  infer_instance

private def edge (withdrawn allowed : Bool) (a b : Node) : Bool :=
  decide (physical.link a b) && (!withdrawn || (a != .primary && b != .primary)) &&
    (!(decide (gateways a) || decide (gateways b)) || allowed)

private def closure [BEq α] (vertices : List α) (edge : α → α → Bool) (source target : α) : Bool :=
  ((List.range vertices.length).foldl (fun seen _ =>
    (seen ++ vertices.filter (fun next => seen.any (fun previous => edge previous next))).eraseDups) [source]).contains target

private def path (edge : Node → Node → Bool) : List Node → Bool
  | [] => false
  | [_] => true
  | a :: b :: rest => edge a b && path edge (b :: rest)

private def ensure (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

def run : IO Unit := do
  ensure (collapse .apA == .client && collapse .apB == .client)
    "Both abstract access points must collapse to the wired client role."
  for node in nodes do
    ensure (collapse (expand node) == node) "Expansion must retain every actual direct-topology role."
  for a in campusNodes do
    for b in campusNodes do
      if decide (CampusDuplex.physical.link a b) then
        ensure (collapse a == collapse b || decide (physical.link (collapse a) (collapse b)))
          "Every abstract campus edge must stutter or map to an actual direct-model edge."
  for a in nodes do
    for b in nodes do
      if decide (physical.link a b) then
        ensure (closure campusNodes (fun x y => decide (CampusDuplex.physical.link x y)) (expand a) (expand b))
          "Every direct-model edge must expand to a declared abstract campus path."
  for withdrawn in [false, true] do
    for allowed in [false, true] do
      ensure (closure nodes (edge withdrawn allowed) .client .server == allowed &&
        closure nodes (edge withdrawn allowed) .server .client == allowed)
        "Direct request and reply reachability must equal current permission before and after primary withdrawal."
      for endpoint in [Node.client, .server] do
        ensure (!(closure nodes (edge withdrawn allowed) endpoint .management) &&
          !(closure nodes (edge withdrawn allowed) .management endpoint))
          "Both direct endpoint roles must remain separated from management in both directions."
      for gateway in [StatefulFailover.Gateway.primary, .standby] do
        for direction in [FlowNAT.Direction.original, .reply] do
          ensure (path (edge withdrawn allowed) (routeTrace gateway direction) ==
            (allowed && (!withdrawn || gateway == .standby)))
            "A selected route requires current permission and a physically present assigned gateway."
  ensure (session.session.permits context scope)
    "The direct graph must retain the explicitly supplied custom application scope."
  for node in nodes do
    ensure (!(edge true true node .primary) && !(edge true true .primary node))
      "Primary withdrawal must remove every incident direct-model link."

end NetlibTest.CampusDirect
