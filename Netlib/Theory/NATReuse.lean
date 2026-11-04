import Netlib.Protocol.NAT

/-!
# Indistinguishability after NAPT alias reuse

Source translation erases the inside endpoint from the wire five-tuple.
Reusing the alias can make a delayed reply identical to a current reply.
The results concern the header abstraction, not full TCP packet processing.
-/

namespace Netlib.Theory.NATReuse

open Packet Protocol

def translated (alias : Endpoint) (flow : Header) : Header :=
  (Rewrite.sourceEndpoint alias).apply flow

theorem translated_eq_iff (alias : Endpoint) (left right : Header) :
    translated alias left = translated alias right ↔
      left.destinationEndpoint = right.destinationEndpoint ∧ left.protocol = right.protocol := by
  cases left
  cases right
  simp [translated, Rewrite.sourceEndpoint, Rewrite.apply, Header.destinationEndpoint,
    and_assoc, and_comm]

theorem reply_eq (alias : Endpoint) (left right : Header)
    (remote : left.destinationEndpoint = right.destinationEndpoint)
    (protocol : left.protocol = right.protocol) :
    (translated alias left).reverse = (translated alias right).reverse :=
  congrArg Header.reverse ((translated_eq_iff alias left right).mpr ⟨remote, protocol⟩)

theorem distinct_inside_same_reply (alias : Endpoint) (left right : Header)
    (distinct : left.sourceEndpoint ≠ right.sourceEndpoint)
    (remote : left.destinationEndpoint = right.destinationEndpoint)
    (protocol : left.protocol = right.protocol) :
    left ≠ right ∧ (translated alias left).reverse = (translated alias right).reverse :=
  ⟨fun same => distinct (congrArg Header.sourceEndpoint same), reply_eq alias left right remote protocol⟩

/-- The state is the same at the decision point for either indistinguishable packet. -/
theorem header_only_indistinguishable {State : Type u} {Answer : Type v}
    (decision : State → Header → Answer) (state : State) (alias : Endpoint) (left right : Header)
    (remote : left.destinationEndpoint = right.destinationEndpoint)
    (protocol : left.protocol = right.protocol) :
    decision state (translated alias left).reverse = decision state (translated alias right).reverse :=
  congrArg (decision state) (reply_eq alias left right remote protocol)

theorem cannot_reject_old_accept_new {State : Type u}
    (decision : State → Header → Bool) (state : State) (alias : Endpoint) (oldFlow newFlow : Header)
    (remote : oldFlow.destinationEndpoint = newFlow.destinationEndpoint)
    (protocol : oldFlow.protocol = newFlow.protocol) :
    ¬(decision state (translated alias oldFlow).reverse = false ∧
      decision state (translated alias newFlow).reverse = true) := by
  rintro ⟨oldRejected, newAccepted⟩
  have same := header_only_indistinguishable decision state alias oldFlow newFlow remote protocol
  rw [oldRejected, newAccepted] at same
  cases same

theorem cannot_recover_inside {State : Type u}
    (decode : State → Header → Endpoint) (state : State) (alias : Endpoint) (oldFlow newFlow : Header)
    (distinct : oldFlow.sourceEndpoint ≠ newFlow.sourceEndpoint)
    (remote : oldFlow.destinationEndpoint = newFlow.destinationEndpoint)
    (protocol : oldFlow.protocol = newFlow.protocol) :
    ¬(decode state (translated alias oldFlow).reverse = oldFlow.sourceEndpoint ∧
      decode state (translated alias newFlow).reverse = newFlow.sourceEndpoint) := by
  rintro ⟨oldDecoded, newDecoded⟩
  have same := header_only_indistinguishable decode state alias oldFlow newFlow remote protocol
  rw [oldDecoded, newDecoded] at same
  exact distinct same

def retirementEvents (oldFlow : Header) (alias : Endpoint) (expiresAt : Nat) : List NAT.Event :=
  [.outbound oldFlow alias true expiresAt, .advance expiresAt]

def reuseEvents (oldFlow newFlow : Header) (alias : Endpoint)
    (oldDeadline newDeadline : Nat) : List NAT.Event :=
  retirementEvents oldFlow alias oldDeadline ++ [.outbound newFlow alias true newDeadline]

theorem retired_state (oldFlow : Header) (alias : Endpoint) (expiresAt : Nat)
    (transport : Conntrack.transport oldFlow = true) (future : 0 < expiresAt) :
    NAT.run NAT.State.initial (retirementEvents oldFlow alias expiresAt) =
      ⟨⟨expiresAt, []⟩, []⟩ := by
  simp [retirementEvents, NAT.run, NAT.step, NAT.State.initial, Conntrack.canOpen,
    transport, future, NAT.allocationAllowed, NAT.mapping?, NAT.collisionFree,
    NAT.outboundState, NAT.newBinding, NAT.advance, Conntrack.install, Conntrack.advance]

theorem reused_outbound (oldFlow newFlow : Header) (alias : Endpoint)
    (oldDeadline newDeadline : Nat)
    (oldTransport : Conntrack.transport oldFlow = true) (oldFuture : 0 < oldDeadline)
    (newTransport : Conntrack.transport newFlow = true) (newFuture : oldDeadline < newDeadline) :
    (NAT.step (NAT.run NAT.State.initial (retirementEvents oldFlow alias oldDeadline))
      (.outbound newFlow alias true newDeadline)).output = some (translated alias newFlow) := by
  rw [retired_state oldFlow alias oldDeadline oldTransport oldFuture]
  simp [NAT.step, Conntrack.canOpen, newTransport, newFuture, NAT.allocationAllowed,
    NAT.mapping?, NAT.collisionFree, translated]

theorem reused_state_safe (oldFlow newFlow : Header) (alias : Endpoint) (oldDeadline newDeadline : Nat) :
    (NAT.run NAT.State.initial (reuseEvents oldFlow newFlow alias oldDeadline newDeadline)).Safe :=
  NAT.run_safe _ _ NAT.initial_safe

/-- The old packet's wire reply is restored using the new live binding and grant. -/
theorem delayed_reply_restored_to_new (oldFlow newFlow : Header) (alias : Endpoint)
    (oldDeadline newDeadline : Nat)
    (oldTransport : Conntrack.transport oldFlow = true) (oldFuture : 0 < oldDeadline)
    (newTransport : Conntrack.transport newFlow = true) (newFuture : oldDeadline < newDeadline)
    (remote : oldFlow.destinationEndpoint = newFlow.destinationEndpoint)
    (protocol : oldFlow.protocol = newFlow.protocol) :
    (NAT.step (NAT.run NAT.State.initial (reuseEvents oldFlow newFlow alias oldDeadline newDeadline))
      (.inbound (translated alias oldFlow).reverse)).output = some newFlow.reverse := by
  have accepted := reused_outbound oldFlow newFlow alias oldDeadline newDeadline
    oldTransport oldFuture newTransport newFuture
  have roundtrip := NAT.accepted_roundtrip _ newFlow (translated alias newFlow) alias true newDeadline accepted
  rw [← reply_eq alias oldFlow newFlow remote protocol] at roundtrip
  simpa only [reuseEvents, NAT.run, List.foldl_append, List.foldl_cons, List.foldl_nil] using roundtrip

theorem delayed_reply_not_original (oldFlow newFlow : Header) (alias : Endpoint)
    (oldDeadline newDeadline : Nat)
    (oldTransport : Conntrack.transport oldFlow = true) (oldFuture : 0 < oldDeadline)
    (newTransport : Conntrack.transport newFlow = true) (newFuture : oldDeadline < newDeadline)
    (distinct : oldFlow.sourceEndpoint ≠ newFlow.sourceEndpoint)
    (remote : oldFlow.destinationEndpoint = newFlow.destinationEndpoint)
    (protocol : oldFlow.protocol = newFlow.protocol) :
    (NAT.step (NAT.run NAT.State.initial (reuseEvents oldFlow newFlow alias oldDeadline newDeadline))
      (.inbound (translated alias oldFlow).reverse)).output ≠ some oldFlow.reverse := by
  rw [delayed_reply_restored_to_new oldFlow newFlow alias oldDeadline newDeadline
    oldTransport oldFuture newTransport newFuture remote protocol]
  intro same
  have reverseSame := Option.some.inj same
  have flowSame := congrArg Header.reverse reverseSame
  simp only [Header.reverse_reverse] at flowSame
  exact distinct (congrArg Header.sourceEndpoint flowSame.symm)

def RejectsRetiredReply (state : NAT.State) (oldFlow : Header) (alias : Endpoint) : Prop :=
  (NAT.step state (.inbound (translated alias oldFlow).reverse)).output = none

theorem safe_but_not_retired_reply_rejection (oldFlow newFlow : Header) (alias : Endpoint)
    (oldDeadline newDeadline : Nat)
    (oldTransport : Conntrack.transport oldFlow = true) (oldFuture : 0 < oldDeadline)
    (newTransport : Conntrack.transport newFlow = true) (newFuture : oldDeadline < newDeadline)
    (remote : oldFlow.destinationEndpoint = newFlow.destinationEndpoint)
    (protocol : oldFlow.protocol = newFlow.protocol) :
    let state := NAT.run NAT.State.initial (reuseEvents oldFlow newFlow alias oldDeadline newDeadline)
    state.Safe ∧ ¬RejectsRetiredReply state oldFlow alias := by
  refine ⟨reused_state_safe _ _ _ _ _, ?_⟩
  intro rejected
  have accepted := delayed_reply_restored_to_new oldFlow newFlow alias oldDeadline newDeadline
    oldTransport oldFuture newTransport newFuture remote protocol
  rw [show (NAT.step _ _).output = none from rejected] at accepted
  cases accepted

end Netlib.Theory.NATReuse
