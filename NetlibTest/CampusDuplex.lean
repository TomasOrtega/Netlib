import Netlib.Examples.CampusDuplex

namespace NetlibTest.CampusDuplex

open Netlib Packet Protocol Network Examples
open Examples.CampusDuplex

private def context : Context := ⟨"student", "campus-application", "campus-authority"⟩
private def scope : Scope := ⟨"campus-application", "use"⟩
private def token : Credential := ⟨context.issuer, context.consumer, context.producer, [scope], 100, true⟩
private def permitted : EAPSession.State :=
  ⟨EAPAuth.State.initial, { authenticated := true, credential := some token, now := 10 }⟩
private def nodes : List Campus.Node := [.client, .apA, .gatewayA, .apB, .gatewayB, .server, .management]

example (state : EAPSession.State) (selectedScope : Scope) (fault : Fault Campus.Node)
    (admissible : singleInternalNode Campus.clients Campus.servers fault) :
    Duplex (network context state selectedScope fault) ↔ state.session.permits context selectedScope = true :=
  duplex_reachable_iff context state selectedScope fault admissible

example (state : EAPSession.State) (withdrawal : CampusWithdrawal.State) :
    Duplex (interpretation context state scope withdrawal) ↔ state.session.permits context scope = true :=
  interpretation_duplex_iff context state scope withdrawal

example (state : EAPSession.State) (selectedScope : Scope) (direction : FlowNAT.Direction)
    (allowed : state.session.permits context selectedScope = true) :
    Walk (network context state selectedScope primaryWithdrawal) (source direction) (target direction)
      (routeTrace .standby direction) := standby_after_withdrawal context state selectedScope direction allowed

private def ensure (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private instance (a b : Campus.Node) : Decidable (physical.link a b) := by
  simp only [physical, CampusNAT.physical, Network.union, Campus.base, Campus.access, Campus.distribution]
  infer_instance

private instance (node : Campus.Node) : Decidable (Campus.gateways node) := by
  unfold Campus.gateways
  infer_instance

private def edge (failed : List Campus.Node) (allowed : Bool) (a b : Campus.Node) : Bool :=
  decide (physical.link a b) && !failed.contains a && !failed.contains b &&
    (!(decide (Campus.gateways a) || decide (Campus.gateways b)) || allowed)

private def reachable (failed : List Campus.Node) (allowed : Bool) (source target : Campus.Node) : Bool :=
  let closure := (List.range nodes.length).foldl (fun seen _ =>
    (seen ++ nodes.filter (fun next => seen.any (fun previous => edge failed allowed previous next))).eraseDups) [source]
  closure.contains target

private def path (failed : List Campus.Node) (allowed : Bool) : List Campus.Node → Bool
  | [] => false
  | [_] => true
  | a :: b :: rest => edge failed allowed a b && path failed allowed (b :: rest)

def run : IO Unit := do
  ensure (permitted.session.permits context scope) "The custom campus application scope must permit the declared current session."
  ensure (!(permitted.session.permits context ⟨"application", "read"⟩))
    "The duplex interpretation must retain the supplied scope instead of substituting the earlier campus example's scope."
  for failed in [] :: nodes.map (fun node => [node]) do
    for allowed in [false, true] do
      let endpointsAlive := !failed.contains .client && !failed.contains .server
      let expected := allowed && endpointsAlive
      ensure (reachable failed allowed .client .server == expected && reachable failed allowed .server .client == expected)
        "Request and reply continuity must agree for every endpoint-safe single internal failure and both permission values."
      for endpoint in [Campus.Node.client, .server] do
        ensure (!(reachable failed allowed endpoint .management) && !(reachable failed allowed .management endpoint))
          "Management must remain separated from both endpoint roles in both directions."
  for gateway in [StatefulFailover.Gateway.primary, .standby] do
    for direction in [FlowNAT.Direction.original, .reply] do
      ensure (path [] true (routeTrace gateway direction))
        "Both concrete gateway interpretations must provide their complete request and reply walk."
      ensure (!(path [] false (routeTrace gateway direction)))
        "Each selected route must cross the denied gateway enforcement boundary."
      ensure (path [.gatewayA] true (routeTrace gateway direction) == (gateway == .standby))
        "Withdrawing primary must retain exactly the standby's declared route in either direction."
  for failed in [[Campus.Node.gatewayA, .gatewayB], [.apA, .apB]] do
    ensure (!(reachable failed true .client .server) && !(reachable failed true .server .client))
      "Two independent path failures lie outside single-node continuity and can disconnect both directions."
  let revoked := Session.step context permitted.session .revoke
  ensure (!revoked.permits context scope && !(reachable [.gatewayA] (revoked.permits context scope) .client .server) &&
    !(reachable [.gatewayA] (revoked.permits context scope) .server .client))
    "Current revocation must remove both application directions even when the standby physical route survives."

end NetlibTest.CampusDuplex
