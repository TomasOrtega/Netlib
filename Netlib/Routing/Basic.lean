import Netlib.Packet.ACL

/-!
# Destination routing

A route selects destination addresses by an address prefix.
The longest matching prefix supplies the next hop.
The first entry wins when prefix lengths are equal.
A route with no next hop drops the packet.
-/

namespace Netlib.Routing

open Packet

/-- A route has an address prefix and an optional next hop. -/
structure Entry (Node : Type u) where
  destination : Prefix
  nextHop : Option Node
  deriving Repr, BEq, DecidableEq

namespace Entry

def rank (entry : Entry Node) : Nat := entry.destination.length.val

end Entry

/-- Keep the longer prefix. Keep the left entry when lengths are equal. -/
def prefer (left right : Option (Entry Node)) : Option (Entry Node) :=
  match left, right with
  | none, route => route
  | route, none => route
  | some a, some b => if a.rank < b.rank then some b else some a

/-- Select the first entry with the longest matching prefix. -/
def lookup : List (Entry Node) → Address → Option (Entry Node)
  | [], _ => none
  | entry :: entries, address =>
    prefer (if entry.destination.contains address then some entry else none) (lookup entries address)

theorem prefer_assoc (a b c : Option (Entry Node)) :
    prefer (prefer a b) c = prefer a (prefer b c) := by
  cases a with
  | none => rfl
  | some a =>
    cases b with
    | none => rfl
    | some b =>
      cases c with
      | none =>
        by_cases hab : a.rank < b.rank <;> simp [prefer, hab]
      | some c =>
        by_cases hab : a.rank < b.rank <;>
          by_cases hbc : b.rank < c.rank <;>
          by_cases hac : a.rank < c.rank <;>
          simp only [prefer, hab, hbc, hac, ite_true, ite_false] <;> omega

theorem lookup_append (left right : List (Entry Node)) (address : Address) :
    lookup (left ++ right) address = prefer (lookup left address) (lookup right address) := by
  induction left with
  | nil => rfl
  | cons entry entries ih =>
    simp only [List.cons_append, lookup, ih]
    exact (prefer_assoc _ _ _).symm

theorem lookup_cons_unmatched (entry : Entry Node) (entries : List (Entry Node))
    (address : Address) (unmatched : entry.destination.contains address = false) :
    lookup (entry :: entries) address = lookup entries address := by
  simp [lookup, unmatched, prefer]

theorem lookup_cons_tie (entry selected : Entry Node) (entries : List (Entry Node))
    (address : Address) (accepted : entry.destination.contains address = true)
    (tail : lookup entries address = some selected) (equal : entry.rank = selected.rank) :
    lookup (entry :: entries) address = some entry := by
  simp [lookup, accepted, tail, prefer, equal]

theorem lookup_none_iff (entries : List (Entry Node)) (address : Address) :
    lookup entries address = none ↔
      ∀ entry ∈ entries, entry.destination.contains address = false := by
  induction entries with
  | nil => simp [lookup]
  | cons entry entries ih =>
    cases accepted : entry.destination.contains address with
    | false => simpa [lookup_cons_unmatched _ _ _ accepted, accepted] using ih
    | true =>
      cases selected : lookup entries address with
      | none => simp [lookup, accepted, selected, prefer]
      | some route =>
        simp only [lookup, accepted, ite_true, selected, prefer]
        split <;> simp [accepted]

/-- A selected route is in the table, accepts the address, and has maximal length. -/
theorem lookup_best (entries : List (Entry Node)) (address : Address) (selected : Entry Node)
    (found : lookup entries address = some selected) :
    selected ∈ entries ∧ selected.destination.contains address = true ∧
      ∀ entry ∈ entries, entry.destination.contains address = true → entry.rank ≤ selected.rank := by
  induction entries generalizing selected with
  | nil => simp [lookup] at found
  | cons entry entries ih =>
    cases accepted : entry.destination.contains address with
    | false =>
      have tail : lookup entries address = some selected := by
        simpa [lookup_cons_unmatched _ _ _ accepted] using found
      obtain ⟨member, accepted, maximal⟩ := ih _ tail
      refine ⟨List.mem_cons_of_mem _ member, accepted, ?_⟩
      intro candidate candidateMember accepted
      rcases List.mem_cons.mp candidateMember with rfl | candidateMember
      · simp_all
      · exact maximal candidate candidateMember accepted
    | true =>
      cases tail : lookup entries address with
      | none =>
        have same : entry = selected := by simpa [lookup, accepted, tail, prefer] using found
        subst selected
        refine ⟨by simp, accepted, ?_⟩
        intro candidate candidateMember accepted
        rcases List.mem_cons.mp candidateMember with rfl | candidateMember
        · exact Nat.le_refl _
        · have rejected := (lookup_none_iff _ _).mp tail candidate candidateMember
          simp_all
      | some best =>
        obtain ⟨bestMember, bestMatches, bestMaximal⟩ := ih _ tail
        by_cases longer : entry.rank < best.rank
        · have same : best = selected := by
            simpa [lookup, accepted, tail, prefer, longer] using found
          subst selected
          refine ⟨List.mem_cons_of_mem _ bestMember, bestMatches, ?_⟩
          intro candidate candidateMember accepted
          rcases List.mem_cons.mp candidateMember with rfl | candidateMember
          · exact Nat.le_of_lt longer
          · exact bestMaximal candidate candidateMember accepted
        · have same : entry = selected := by
            simpa [lookup, accepted, tail, prefer, longer] using found
          subst selected
          refine ⟨by simp, accepted, ?_⟩
          intro candidate candidateMember accepted
          rcases List.mem_cons.mp candidateMember with rfl | candidateMember
          · exact Nat.le_refl _
          · have := bestMaximal candidate candidateMember accepted
            omega

theorem lookup_matches (entries : List (Entry Node)) (address : Address) (selected : Entry Node)
    (found : lookup entries address = some selected) :
    selected.destination.contains address = true := (lookup_best _ _ _ found).2.1

theorem lookup_member (entries : List (Entry Node)) (address : Address) (selected : Entry Node)
    (found : lookup entries address = some selected) : selected ∈ entries :=
  (lookup_best _ _ _ found).1

/-- A default route has a zero-length prefix. -/
def defaultRoute (nextHop : Option Node) : Entry Node := ⟨⟨0, 0⟩, nextHop⟩

@[simp] theorem default_matches (nextHop : Option Node) (address : Address) :
    (defaultRoute nextHop).destination.contains address = true := Prefix.contains_zero _ _

@[simp] theorem lookup_default (nextHop : Option Node) (address : Address) :
    lookup [defaultRoute nextHop] address = some (defaultRoute nextHop) := by
  simp [lookup, prefer]

/-- A default route at the end does not replace an existing matching route. -/
theorem append_default_preserves (entries : List (Entry Node)) (address : Address)
    (selected : Entry Node) (found : lookup entries address = some selected) (nextHop : Option Node) :
    lookup (entries ++ [defaultRoute nextHop]) address = some selected := by
  rw [lookup_append, found, lookup_default]
  simp [prefer, defaultRoute, Entry.rank]

/-- A final default route supplies an answer when other routes do not match. -/
theorem append_default_of_none (entries : List (Entry Node)) (address : Address)
    (missing : lookup entries address = none) (nextHop : Option Node) :
    lookup (entries ++ [defaultRoute nextHop]) address = some (defaultRoute nextHop) := by
  rw [lookup_append, missing, lookup_default]
  rfl

/-- No route and a selected drop route both produce no next hop. -/
def nextHop (entries : List (Entry Node)) (address : Address) : Option Node :=
  (lookup entries address).bind (·.nextHop)

theorem nextHop_some_iff (entries : List (Entry Node)) (address : Address) (hop : Node) :
    nextHop entries address = some hop ↔
      ∃ entry, lookup entries address = some entry ∧ entry.nextHop = some hop := by
  cases selected : lookup entries address <;> simp [nextHop, selected]

/-- Each node forwards to the next hop selected by its table. -/
def network (tables : Node → List (Entry Node)) (destination : Address) : Network Node :=
  ⟨fun source target => nextHop (tables source) destination = some target⟩

instance networkLinkDecidable [DecidableEq Node] (tables : Node → List (Entry Node))
    (destination : Address) (source target : Node) :
    Decidable ((network tables destination).link source target) :=
  inferInstanceAs (Decidable (nextHop (tables source) destination = some target))

/-- One lookup cannot select two different next hops. -/
theorem network_deterministic (tables : Node → List (Entry Node)) (destination : Address)
    {source left right : Node} (leftLink : (network tables destination).link source left)
    (rightLink : (network tables destination).link source right) : left = right :=
  Option.some.inj (leftLink.symm.trans rightLink)

/-- A forwarding step has a matching route of maximal length. -/
theorem link_has_best_route (tables : Node → List (Entry Node)) (destination : Address)
    {source target : Node} (link : (network tables destination).link source target) :
    ∃ entry ∈ tables source, entry.nextHop = some target ∧
      entry.destination.contains destination = true ∧
      ∀ candidate ∈ tables source,
        candidate.destination.contains destination = true → candidate.rank ≤ entry.rank := by
  obtain ⟨entry, selected, next⟩ := (nextHop_some_iff _ _ _).mp link
  obtain ⟨member, accepted, maximal⟩ := lookup_best _ _ _ selected
  exact ⟨entry, member, next, accepted, maximal⟩

/-- Apply packet rules after the routing decision. -/
def packetNetwork (tables : Node → List (Entry Node)) (policies : Node → Node → ACL)
    (header : Header) : Network Node :=
  Forwarding.filter (network tables header.destination) policies header

instance packetLinkDecidable [DecidableEq Node] (tables : Node → List (Entry Node))
    (policies : Node → Node → ACL) (header : Header) (source target : Node) :
    Decidable ((packetNetwork tables policies header).link source target) :=
  inferInstanceAs (Decidable ((network tables header.destination).link source target ∧
    (policies source target).allows header = true))

/-- Packet rules do not create a route. -/
theorem packet_path_has_route {tables : Node → List (Entry Node)}
    {policies : Node → Node → ACL} {header : Header} {source target : Node}
    (path : (packetNetwork tables policies header).Reachable source target) :
    (network tables header.destination).Reachable source target :=
  Forwarding.reachable_original path

/-- A selected drop route prevents all forwarding steps from its node. -/
theorem drop_has_no_link (tables : Node → List (Entry Node)) (destination : Address)
    (source : Node) (entry : Entry Node) (selected : lookup (tables source) destination = some entry)
    (drop : entry.nextHop = none) (target : Node) :
    ¬(network tables destination).link source target := by
  simp [network, nextHop, selected, drop]

/-- A drop route blocks every path to a different node. -/
theorem drop_has_no_path (tables : Node → List (Entry Node)) (destination : Address)
    (source : Node) (entry : Entry Node) (selected : lookup (tables source) destination = some entry)
    (drop : entry.nextHop = none) (target : Node) (different : source ≠ target) :
    ¬(network tables destination).Reachable source target := by
  intro path
  cases path with
  | refl => exact different rfl
  | step edge _ => exact drop_has_no_link tables destination source entry selected drop _ edge

end Netlib.Routing
