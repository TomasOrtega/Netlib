import Netlib.Network.Contract
import Netlib.Network.Failure

namespace NetlibTest.Contracts

open Netlib Netlib.Network

private def firstDomain : Network Nat := ⟨fun a b => a = 0 ∧ b = 1⟩
private def secondDomain : Network Nat := ⟨fun a b => a = 1 ∧ b = 2⟩

example : firstDomain.Isolated (· = 0) (· = 2) := by
  apply isolated_of_closed (· ≤ 1)
  · intro a b edge _
    obtain ⟨_, rfl⟩ := edge
    decide
  · intro a member
    subst a
    decide
  · intro b member
    subst b
    decide

example : secondDomain.Isolated (· = 0) (· = 2) := by
  apply isolated_of_closed (· = 0)
  · intro a b edge inside
    obtain ⟨rfl, _⟩ := edge
    contradiction
  · exact fun _ => id
  · intro b member
    subst b
    decide

/-- Independent isolation claims do not protect an alternating path. -/
example : ¬(union firstDomain secondDomain).Isolated (· = 0) (· = 2) := by
  intro isolated
  exact isolated 0 2 rfl rfl
    (.step (.inl ⟨rfl, rfl⟩) (.single (.inr ⟨rfl, rfl⟩)))

example : (union firstDomain secondDomain).Available (· = 0) (· = 2) := by
  apply available_union_via (· = 1)
  · intro a source
    subst a
    exact ⟨1, rfl, .single ⟨rfl, rfl⟩⟩
  · intro a b interface target
    subst a
    subst b
    exact .single ⟨rfl, rfl⟩

example : (union firstDomain secondDomain).Isolated (· = 0) (· = 3) := by
  apply isolated_union_of_closed (region := (· ≤ 2))
  · intro a b _ edge
    obtain ⟨_, rfl⟩ := edge
    decide
  · intro a b _ edge
    obtain ⟨_, rfl⟩ := edge
    decide
  · intro a source
    subst a
    decide
  · intro b target
    subst b
    decide

example : (union firstDomain secondDomain).Mediated (· = 0) (· = 2) (· = 1) := by
  apply mediated_union_of_closed (region := (· = 0))
  · intro a b _ edge
    exact False.elim (edge.2.2 edge.1.2)
  · intro a b _ edge
    exact False.elim (edge.2.1 edge.1.1)
  · exact fun _ => id
  · intro b target
    subst b
    decide

private def domainNet : Network (Fin 2) := ⟨fun a b => a = 0 ∧ b = 1⟩
private def abstract : Network Nat := ⟨fun a b => b = a + 1⟩

private def leftContract : StutteringRefinement domainNet abstract where
  project node := node.val
  simulate a b edge := by
    obtain ⟨rfl, rfl⟩ := edge
    exact .inr rfl

private def rightContract : StutteringRefinement domainNet abstract where
  project node := node.val + 2
  simulate a b edge := by
    obtain ⟨rfl, rfl⟩ := edge
    exact .inr rfl

private def border (a b : Fin 2) : Prop := a = 1 ∧ b = 0
private def noBorder (_ _ : Fin 2) : Prop := False

private def federation : StutteringRefinement
    (interconnect domainNet domainNet border noBorder) abstract :=
  leftContract.interconnect rightContract border noBorder
    (by intro a b edge; obtain ⟨rfl, rfl⟩ := edge; exact .inr rfl)
    (by intro _ _ edge; exact False.elim edge)

private theorem abstractMediated : abstract.Mediated (· = 0) (· = 3) (· = 1) := by
  apply mediated_of_cut (· = 0)
  · intro a b edge _ outside inside
    subst a
    have : b = 1 := edge
    exact False.elim (outside this)
  · exact fun _ => id
  · intro b target
    subst b
    decide

example : (interconnect domainNet domainNet border noBorder).Mediated
    (fun node => federation.project node = 0)
    (fun node => federation.project node = 3)
    (fun node => federation.project node = 1) :=
  federation.mediated abstractMediated

example : (interconnect domainNet domainNet border noBorder).Reachable
    (.inl 0) (.inr 1) := by
  apply Reachable.step (next := Sum.inl (1 : Fin 2))
  · exact ⟨rfl, rfl⟩
  apply Reachable.step (next := Sum.inr (0 : Fin 2))
  · exact ⟨rfl, rfl⟩
  exact .single ⟨rfl, rfl⟩

private def redundant : Network Nat where
  link a b := (a = 0 ∧ (b = 1 ∨ b = 2)) ∨ ((a = 1 ∨ a = 2) ∧ b = 3)

theorem redundantAvailable : redundant.RobustAvailable
    (singleInternalNode (· = 0) (· = 3)) (· = 0) (· = 3) := by
  apply robustAvailable_two_gateways
  intro source target sourceMember targetMember
  subst source
  subst target
  exact ⟨1, 2, by decide, .inl ⟨rfl, .inl rfl⟩, .inr ⟨.inl rfl, rfl⟩,
    .inl ⟨rfl, .inr rfl⟩, .inr ⟨.inr rfl, rfl⟩⟩

example : (redundant.afterFault (Fault.node 1)).Reachable 0 3 := by
  have admissible : singleInternalNode (fun n : Nat => n = 0) (· = 3) (Fault.node 1) :=
    singleInternalNode_node 1 (by decide) (by decide)
  exact redundantAvailable _ admissible 0 3 rfl rfl

example : redundant.Mediated (· = 0) (· = 3) (fun n => n = 1 ∨ n = 2) := by
  apply mediated_of_cut (· = 0)
  · intro a b edge _ outside inside
    subst a
    rcases edge with ⟨_, target⟩ | ⟨impossible, _⟩
    · exact False.elim (outside target)
    · rcases impossible with impossible | impossible <;> contradiction
  · exact fun _ => id
  · intro b target
    subst b
    decide

private def twoFailures : Fault Nat := ⟨fun n => n = 1 ∨ n = 2, fun _ _ => False⟩

/-- Two gateway failures exceed the availability contract. -/
example : ¬(redundant.afterFault twoFailures).Reachable 0 3 := by
  intro path
  cases path with
  | step edge _ =>
    rcases edge.1 with ⟨_, gateway⟩ | ⟨impossible, _⟩
    · exact edge.2.2.1 gateway
    · rcases impossible with impossible | impossible <;> contradiction

private def longerPaths : Network Nat where
  link a b := (a, b) ∈ [(0, 1), (1, 2), (2, 7), (0, 3), (3, 4), (4, 7)]

example : longerPaths.RobustAvailable
    (singleInternalNode (· = 0) (· = 7)) (· = 0) (· = 7) := by
  apply robustAvailable_disjoint_walks
  intro source target sourceMember targetMember
  subst source
  subst target
  refine ⟨[0, 1, 2, 7], [0, 3, 4, 7], ?_, ?_, ?_⟩
  · exact .cons (by simp [longerPaths])
      (.cons (by simp [longerPaths]) (.cons (by simp [longerPaths]) (.nil 7)))
  · exact .cons (by simp [longerPaths])
      (.cons (by simp [longerPaths]) (.cons (by simp [longerPaths]) (.nil 7)))
  · intro node firstMember secondMember
    simp only [List.mem_cons, List.not_mem_nil, or_false] at firstMember secondMember
    omega

end NetlibTest.Contracts
