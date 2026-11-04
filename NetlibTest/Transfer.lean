import Netlib.Check.Transfer
import Netlib.Check.Compliance

namespace NetlibTest.Transfer

open Netlib Packet Netlib.Check.Transfer

private def incoming : Header := ⟨167772161, 3405803786, .tcp, 50000, 80⟩
private def translated : Header := { incoming with destination := 167772162, destinationPort := 443 }

private def service : Match := {
  destination := some ⟨167772162, 32⟩
  protocol := some .tcp
  destinationPorts := some (PortRange.single 443)
}

private def dnat : Netlib.Check.Transfer.Config := {
  nodes := ["client", "nat", "firewall", "server"]
  links := [
    ⟨"client", "nat", {}, {}⟩,
    ⟨"nat", "firewall", {}, { destination := some 167772162, destinationPort := some 443 }⟩,
    ⟨"firewall", "server", service, {}⟩]
}

private def query (kind : Kind := .reach) : Query :=
  ⟨kind, "client", "server", incoming, if kind = .mediated then ["nat"] else []⟩

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def unwrap (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error message => throw (IO.userError message)

private def reject (result : Except String α) (message : String) : IO Unit :=
  match result with
  | .ok _ => throw (IO.userError message)
  | .error _ => pure ()

private def dnatTests : IO Unit := do
  let result ← unwrap (check dnat (query .reach))
  ensure result.value "DNAT did not reach the service."
  ensure (result.path? == some [
    ("client", incoming), ("nat", incoming), ("firewall", translated), ("server", translated)])
    "The DNAT witness lost a rewritten packet or forwarding node."
  let isolated ← unwrap (check dnat (query .isolate))
  ensure (!isolated.value && isolated.path?.isSome) "Isolation lost the rewritten counterexample path."
  let mediated ← unwrap (check dnat (query .mediated))
  ensure (mediated.value && mediated.cut?.isSome) "The NAT node did not mediate the path."
  let withoutTranslation : Netlib.Check.Transfer.Config := { dnat with links := [
    ⟨"client", "nat", {}, {}⟩, ⟨"nat", "firewall", {}, {}⟩,
    ⟨"firewall", "server", service, {}⟩] }
  let blocked ← unwrap (check withoutTranslation (query .reach))
  ensure (!blocked.value && blocked.cut?.isSome) "An untranslated packet passed the private-service guard."
  let denied ← unwrap (check withoutTranslation (query .isolate))
  ensure denied.value "The untranslated packet was not isolated."
  let bypass : Netlib.Check.Transfer.Config := { dnat with
    nodes := dnat.nodes ++ ["side"]
    links := dnat.links ++ [
      ⟨"client", "side", {}, { destination := some 167772162, destinationPort := some 443 }⟩,
      ⟨"side", "server", service, {}⟩] }
  let unmediated ← unwrap (check bypass (query .mediated))
  ensure (!unmediated.value && unmediated.path?.isSome) "A rewritten gateway bypass went undetected."
  ensure (unmediated.path? == some [("client", incoming), ("side", translated), ("server", translated)])
    "The bypass certificate lost the rewritten header."

private def cycleTests : IO Unit := do
  let cyclic : Netlib.Check.Transfer.Config := {
    nodes := ["a", "b", "c"]
    links := [⟨"a", "b", {}, { destination := some 167772162 }⟩,
      ⟨"b", "a", {}, { destination := some incoming.destination }⟩]
  }
  let q : Query := ⟨.isolate, "a", "c", incoming, []⟩
  let blocked ← unwrap (check cyclic q)
  ensure (blocked.value && blocked.cut?.isSome) "A rewrite cycle prevented a closed-cut result."
  let reached ← unwrap (check cyclic { q with kind := .reach, target := "b" })
  ensure reached.value "A state in the rewrite cycle was not reachable."
  let same ← unwrap (check cyclic { q with kind := .reach, target := "a" })
  ensure (same.value && same.path? == some [("a", incoming)]) "Zero-step reachability lost its packet."
  let selfIsolation ← unwrap (check cyclic { q with target := "a" })
  ensure (!selfIsolation.value) "A zero-step path was called isolated."
  let selfMediation ← unwrap (check cyclic { q with kind := .mediated, target := "a", gateways := ["b"] })
  ensure (!selfMediation.value) "A zero-step path outside all gateways was mediated."
  let endpoint ← unwrap (check cyclic { q with kind := .mediated, target := "a", gateways := ["a"] })
  ensure (endpoint.value && endpoint.path?.isNone && endpoint.cut?.isNone)
    "A gateway endpoint did not satisfy mediation."

private def legacyTests : IO Unit := do
  let unchanged : Netlib.Check.Transfer.Config := {
    nodes := ["a", "b", "c", "d"]
    links := [⟨"a", "b", {}, {}⟩, ⟨"b", "c", {}, {}⟩, ⟨"b", "a", {}, {}⟩]
  }
  for target in unchanged.nodes do
    let q : Query := ⟨.reach, "a", target, incoming, []⟩
    let current ← unwrap (check unchanged q)
    let previous ← unwrap (Compliance.decideReach unchanged.nodes
      (fun a b => unchanged.links.any (fun link => link.source == a && link.target == b)) "a" target)
    ensure (current.value == previous.value) "Identity rewriting changed legacy graph reachability."
    match current.path? with
    | none => pure ()
    | some trace =>
      ensure (trace.all (fun state => state.2 == incoming))
        "An identity transfer changed the packet header."

private def certificateTests : IO Unit := do
  let q := query .reach
  let states := dnat.states incoming
  let edge := dnat.filteredEdge q.allowed
  ensure (!(Certificate.validPath states edge ("client", incoming) ("server", incoming)
    [("client", incoming), ("nat", incoming), ("firewall", incoming), ("server", incoming)]))
    "The validator accepted a path that omitted the rewrite."
  ensure (!(Certificate.validCut states edge ("client", incoming) ("server", translated)
    [("client", incoming)])) "The validator accepted a nonclosed cut."
  ensure (!(Certificate.validPath states edge ("client", incoming) ("server", translated) []))
    "The validator accepted a missing path certificate."
  reject (Search.decide ([] : List State) (fun _ _ => false) ("outside", incoming) [("outside", incoming)])
    "A missing declared state produced a zero-step certificate."

private def validationTests : IO Unit := do
  reject (check dnat (query .reach) 0) "An exhausted state budget returned an answer."
  reject (check dnat (query .reach) (dnat.stateCount incoming - 1))
    "The state product exceeded its budget."
  let exact ← unwrap (check dnat (query .reach) (dnat.stateCount incoming))
  ensure exact.value "The exact state budget rejected a complete search."
  reject (check { dnat with nodes := dnat.nodes ++ ["client"] } (query .reach))
    "Duplicate device declarations were accepted."
  reject (check { dnat with links := dnat.links ++ dnat.links } (query .reach))
    "Duplicate transfer links were accepted."
  reject (check { dnat with nodes := ["client", "server"] } (query .reach))
    "An unknown link endpoint was accepted."
  reject (check dnat { query .reach with source := "unknown" }) "An unknown source was accepted."
  reject (check dnat { query .reach with target := "unknown" }) "An unknown target was accepted."
  reject (check dnat { query .mediated with gateways := ["unknown"] }) "An unknown gateway was accepted."
  reject (check dnat { query .mediated with gateways := ["nat", "nat"] }) "Duplicate gateways were accepted."
  reject (check dnat { query .mediated with gateways := [] }) "An empty gateway requirement was accepted."
  reject (check dnat { query .reach with gateways := ["nat"] }) "A reach query silently ignored gateways."
  let large : Netlib.Check.Transfer.Config := {
    nodes := ["a", "b"]
    links := (List.range 100).map fun value => ⟨"a", "b", {}, {
      source := some ⟨value % 4294967296, Nat.mod_lt _ (by decide)⟩
      destination := some 0
      protocol := some 6
    }⟩
  }
  reject (check large ⟨.reach, "a", "b", incoming, []⟩ 1)
    "A large Cartesian universe was enumerated before its budget check."

def run : IO Unit := do
  dnatTests
  cycleTests
  legacyTests
  certificateTests
  validationTests
  IO.println "Header-changing transfer tests passed."

end NetlibTest.Transfer
