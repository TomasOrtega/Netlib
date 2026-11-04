import Netlib.Routing.Basic

namespace NetlibTest.Routing

open Netlib Netlib.Packet Netlib.Routing

private def host : Address := 167838211
private def other : Address := 3232235777
private def broad : Entry Nat := ⟨⟨167772160, 8⟩, some 1⟩
private def middle : Entry Nat := ⟨⟨167837696, 16⟩, some 2⟩
private def narrow : Entry Nat := ⟨⟨167838208, 24⟩, some 3⟩
private def equalLength : Entry Nat := ⟨⟨167838250, 24⟩, some 4⟩
private def exactHost : Entry Nat := ⟨⟨host, 32⟩, some 5⟩
private def dropHost : Entry Nat := ⟨⟨host, 32⟩, none⟩
private def unrelated : Entry Nat := ⟨⟨other, 32⟩, some 6⟩

example : lookup ([] : List (Entry Nat)) host = none := rfl
example : lookup [unrelated] host = none := by decide
example : lookup [broad, middle, narrow] host = some narrow := by decide
example : lookup [narrow, broad, middle] host = some narrow := by decide
example : lookup [broad, narrow, exactHost] host = some exactHost := by decide
example : lookup [exactHost, narrow, broad] host = some exactHost := by decide
example : lookup [narrow, equalLength] host = some narrow := by decide
example : lookup [equalLength, narrow] host = some equalLength := by decide
example : lookup [unrelated, narrow] host = some narrow := by decide
example : lookup [narrow, unrelated] host = some narrow := by decide
example : lookup [defaultRoute (some 9), broad, narrow] host = some narrow := by decide
example : lookup [broad, defaultRoute (some 9)] other = some (defaultRoute (some 9)) := by decide
example : lookup [defaultRoute (some 9), defaultRoute (some 8)] host =
    some (defaultRoute (some 9)) := by decide
example : lookup [broad, narrow, dropHost] host = some dropHost := by decide
example : lookup [dropHost, exactHost] host = some dropHost := by decide
example : lookup [exactHost, dropHost] host = some exactHost := by decide
example : nextHop [broad, narrow, dropHost] host = none := by decide
example : nextHop [narrow] host = some 3 := by decide
example : nextHop [unrelated] host = none := by decide

example : narrow ∈ [broad, narrow, middle] ∧ narrow.destination.contains host = true ∧
    ∀ entry ∈ [broad, narrow, middle], entry.destination.contains host = true →
      entry.rank ≤ narrow.rank := lookup_best _ _ _ (by decide)

example (entries : List (Entry Nat)) (selected : Entry Nat)
    (found : lookup entries host = some selected) :
    lookup (entries ++ [defaultRoute (some 9)]) host = some selected :=
  append_default_preserves entries host selected found (some 9)

example : lookup ([unrelated] ++ [defaultRoute (some 9)]) host =
    some (defaultRoute (some 9)) :=
  append_default_of_none [unrelated] host (by decide) (some 9)

private def tables (source : Nat) : List (Entry Nat) :=
  if source = 0 then [defaultRoute (some 1)]
  else if source = 1 then [defaultRoute (some 2)]
  else []

example : (network tables host).Reachable 0 2 := by
  apply Network.Reachable.step (next := 1)
  · decide
  · exact .single (by decide)

example : ¬(network tables host).link 0 2 := by decide

example {source left right : Nat}
    (leftLink : (network tables host).link source left)
    (rightLink : (network tables host).link source right) : left = right :=
  network_deterministic tables host leftLink rightLink

example : ∃ entry ∈ tables 0, entry.nextHop = some 1 ∧
    entry.destination.contains host = true ∧
    ∀ candidate ∈ tables 0, candidate.destination.contains host = true →
      candidate.rank ≤ entry.rank := link_has_best_route tables host (by decide)

private def dropped (_source : Nat) : List (Entry Nat) := [broad, dropHost]

example : ¬(network dropped host).Reachable 0 2 :=
  drop_has_no_path dropped host 0 dropHost (by decide) rfl 2 (by decide)

example : (network dropped host).Reachable 0 0 := .refl 0

private def https : Header := ⟨1, host, Protocol.tcp, 49152, 443⟩
private def ssh : Header := { https with destinationPort := 22 }

private def acl (_source _target : Nat) : ACL :=
  [⟨{ protocol := some Protocol.tcp, destinationPorts := some (.single 443) }, .permit⟩]

example : (packetNetwork tables acl https).Reachable 0 2 := by
  apply Network.Reachable.step (next := 1)
  · constructor <;> decide
  · apply Network.Reachable.single
    constructor <;> decide

example : ¬(packetNetwork tables acl ssh).Reachable 0 2 := by
  intro path
  cases path with
  | step edge _ =>
    have accepted := edge.2
    change ACL.allows (acl 0 _) ssh = true at accepted
    have denied : ACL.allows (acl 0 0) ssh = false := by decide
    change ACL.allows (acl 0 0) ssh = true at accepted
    simp_all

example : ¬(packetNetwork tables acl https).link 0 2 := by decide

end NetlibTest.Routing
