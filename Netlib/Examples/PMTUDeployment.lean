import Netlib.Protocol.RelatedICMP
import Netlib.Protocol.PMTUFacts

/-!
# Received RELATED errors and a connected UDP sender

A gateway emission is reassembled and decoded before its translated quote reaches
one selected socket's PMTU state. RELATED permission is supplied by the gateway
policy; association does not authenticate the reporter. Host sends assume pending
socket errors have been drained, a stable route, and a monotonic model clock.
-/

namespace Netlib.Examples.PMTUDeployment

open Packet Protocol InternetChecksum

/-- Extract host feedback only from a successfully decoded received error. -/
def sourceFeedback (source : RelatedICMP.Source) : PMTU.Feedback :=
  ⟨source.icmp.message.kind, IPv4QuotePrefix.header source.quote, source.ip.packet.source⟩

def receive (policy : PMTU.Policy) (route : PMTU.Route) (socket : Header) (before : PMTU.State)
    (now : Nat) (source : RelatedICMP.Source) : Option PMTU.Result :=
  PMTU.feedback policy route socket before now (sourceFeedback source)

def deliveredSource (emission : RelatedICMP.Emission tracker input) : RelatedICMP.Source where
  bytes := emission.association.bytes
  ip := ⟨emission.association.packet, IPv4.computedChecksum emission.association.packet, []⟩
  icmp := ⟨emission.association.message, ICMP.computedChecksum emission.association.message⟩
  quote := emission.association.quote
  network := emission.association.decoded
  protocol := input.source.protocol
  transport := emission.association.icmp_decoded
  quotation := emission.association.quoted_decoded

theorem source_decoded (source : RelatedICMP.Source) : RelatedICMP.decode source.bytes = .ok source := by
  unfold RelatedICMP.decode
  split
  · rename_i error network
    rw [source.network] at network
    cases network
  · rename_i ip network
    cases Except.ok.inj (network.symm.trans source.network)
    split
    · split
      · rename_i error transport
        rw [source.transport] at transport
        cases transport
      · rename_i icmp transport
        cases Except.ok.inj (transport.symm.trans source.transport)
        split
        · rename_i error quotation
          rw [source.quotation] at quotation
          cases quotation
        · rename_i quote quotation
          cases Except.ok.inj (quotation.symm.trans source.quotation)
          rfl
    · rename_i unsupported
      exact False.elim (unsupported source.protocol)

theorem delivered_decode (emission : RelatedICMP.Emission tracker input) :
    RelatedICMP.decode emission.association.bytes = .ok (deliveredSource emission) :=
  source_decoded (deliveredSource emission)

theorem delivered_reassembled (emission : RelatedICMP.Emission tracker input) :
    IPv4Fragmentation.reassemble emission.family.fragments = .ok (deliveredSource emission).ip.packet :=
  emission.reassembled

theorem delivered_feedback (emission : RelatedICMP.Emission tracker input) :
    sourceFeedback (deliveredSource emission) =
      ⟨input.source.icmp.message.kind,
        emission.association.entry.flow.input (RelatedICMP.opposite emission.association.direction),
        emission.association.packet.source⟩ := by
  simp only [sourceFeedback, deliveredSource, RelatedICMP.Association.kind,
    emission.association.quote_header]

theorem delivered_quote_ttl (emission : RelatedICMP.Emission tracker input) :
    (deliveredSource emission).quote.packet.ttl = input.source.quote.packet.ttl :=
  emission.association.quoted_metadata.1

theorem delivered_udp (emission : RelatedICMP.Emission tracker input) :
    (deliveredSource emission).quote.packet.protocol = Packet.Protocol.udp := by
  have preserved : emission.association.quote.packet.protocol = input.source.quote.packet.protocol := by
    cases destination : emission.association.entry.changesDestination emission.association.direction <;>
      cases source : emission.association.entry.changesSource emission.association.direction <;>
      simp [RelatedICMP.Association.quote, RelatedICMP.Association.destinationQuote, destination, source]
  exact preserved.trans emission.association.protocol

theorem delivered_update (policy : PMTU.Policy) (route : PMTU.Route) (socket : Header)
    (before : PMTU.State) (now : Nat) (emission : RelatedICMP.Emission tracker input) (advertised : Word)
    (selected : socket = emission.association.entry.flow.input (RelatedICMP.opposite emission.association.direction))
    (kind : input.source.icmp.message.kind = .fragmentationNeeded advertised) :
    receive policy route socket before now (deliveredSource emission) =
      some (PMTU.update policy route before now advertised) := by
  unfold receive
  rw [delivered_feedback, kind, selected]
  simp [PMTU.feedback]

theorem delivered_time_exceeded (policy : PMTU.Policy) (route : PMTU.Route) (socket : Header)
    (before : PMTU.State) (now : Nat) (emission : RelatedICMP.Emission tracker input)
    (kind : input.source.icmp.message.kind = .timeExceeded) :
    receive policy route socket before now (deliveredSource emission) = none := by
  unfold receive
  rw [delivered_feedback, kind]
  exact PMTU.feedback_time_exceeded _ _ _ _ _ _ _

structure OutputFacts (emission : RelatedICMP.Emission tracker input) : Prop where
  decoded : RelatedICMP.decode emission.association.bytes = .ok (deliveredSource emission)
  reassembled : IPv4Fragmentation.reassemble emission.family.fragments = .ok (deliveredSource emission).ip.packet
  socket : (sourceFeedback (deliveredSource emission)).quoted =
    emission.association.entry.flow.input (RelatedICMP.opposite emission.association.direction)
  quotedTTL : (deliveredSource emission).quote.packet.ttl = input.source.quote.packet.ttl
  udp : (deliveredSource emission).quote.packet.protocol = Packet.Protocol.udp
  quotedPrefix : (deliveredSource emission).quote.packet.payload.drop 8 = input.source.quote.packet.payload.drop 8
  outerChecksum : InternetChecksum.valid (deliveredSource emission).ip.packet.payload = true

theorem output_facts (emission : RelatedICMP.Emission tracker input) : OutputFacts emission :=
  ⟨delivered_decode emission, delivered_reassembled emission, emission.association.quote_header,
    delivered_quote_ttl emission, delivered_udp emission, emission.association.quoted_app_prefix,
    emission.association.checksums.2⟩

/-- Actual gateway output freezes conntrack and supplies the socket's PMTU update. -/
theorem step_delivers_update (pipeline : RelatedICMP.Pipeline) (tracker : ConntrackLifecycle.State)
    (input : RelatedICMP.Input) (outcome : RelatedICMP.Outcome tracker input)
    (accepted : RelatedICMP.step pipeline tracker input = .ok outcome)
    (emission : RelatedICMP.Emission tracker input) (emitted : outcome.output = some emission)
    (policy : PMTU.Policy) (route : PMTU.Route) (socket : Header) (before : PMTU.State) (now : Nat)
    (advertised : Word)
    (selected : socket = emission.association.entry.flow.input (RelatedICMP.opposite emission.association.direction))
    (kind : input.source.icmp.message.kind = .fragmentationNeeded advertised) :
    outcome.state = tracker ∧ outcome.disposition = .forwarded ∧
      StatefulACL.Policy.evaluate pipeline.forwarding.forwardDefault pipeline.forwarding.forward
        .related emission.association.beforeSource = .permit ∧
      StatefulACL.Policy.evaluate pipeline.forwarding.lateDefault pipeline.forwarding.late
        .related emission.association.afterSource = .permit ∧
      OutputFacts emission ∧
      receive policy route socket before now (deliveredSource emission) =
        some (PMTU.update policy route before now advertised) := by
  have filters := RelatedICMP.step_filters pipeline tracker input outcome accepted emission emitted
  exact ⟨RelatedICMP.step_state _ _ _ _ accepted, filters.1, filters.2.2.2.2.2.1,
    filters.2.2.2.2.2.2.1, output_facts emission,
    delivered_update _ _ _ _ _ _ _ selected kind⟩

theorem step_delivers_reduction (pipeline : RelatedICMP.Pipeline) (tracker : ConntrackLifecycle.State)
    (input : RelatedICMP.Input) (outcome : RelatedICMP.Outcome tracker input)
    (accepted : RelatedICMP.step pipeline tracker input = .ok outcome)
    (emission : RelatedICMP.Emission tracker input) (emitted : outcome.output = some emission)
    (policy : PMTU.Policy) (route : PMTU.Route) (socket : Header) (before : PMTU.State) (now : Nat)
    (advertised : Word)
    (selected : socket = emission.association.entry.flow.input (RelatedICMP.opposite emission.association.direction))
    (kind : input.source.icmp.message.kind = .fragmentationNeeded advertised)
    (valid : before.Valid route) (positive : 0 < policy.lifetime)
    (unlocked : (route.locked || ((before.age now).exception.map (·.locked)).getD false) = false)
    (above : policy.minimum.val ≤ advertised.val)
    (reducing : advertised.val < (before.current route now).val) :
    outcome.state = tracker ∧ ∃ result,
      receive policy route socket before now (deliveredSource emission) = some result ∧
      result.state.Valid route ∧ (result.state.current route now).val = advertised.val ∧
      (result.state.current route now).val < (before.current route now).val := by
  have delivery := step_delivers_update pipeline tracker input outcome accepted emission emitted
    policy route socket before now advertised selected kind
  have current : ((PMTU.update policy route before now advertised).state.current route now).val = advertised.val := by
    rw [PMTU.update_strict_reduction _ _ _ _ _ unlocked above reducing]
    have live : now < now + policy.lifetime := by omega
    simpa only [PMTU.State.current, PMTU.State.age, Option.filter_some, live, decide_true,
      ↓reduceIte, Option.map_some, Option.getD_some] using
      PMTU.reduced_at_least_floor (before.current route now) policy.minimum advertised above
  exact ⟨delivery.1, PMTU.update policy route before now advertised, delivery.2.2.2.2.2,
    PMTU.update_valid _ _ _ _ _ valid, current, by rw [current]; exact reducing⟩

theorem received_update_valid (policy : PMTU.Policy) (route : PMTU.Route) (socket : Header)
    (before : PMTU.State) (now : Nat) (source : RelatedICMP.Source) (result : PMTU.Result)
    (received : receive policy route socket before now source = some result) (valid : before.Valid route) :
    result.state.Valid route := by
  obtain ⟨_, advertised, _, updated⟩ := PMTU.feedback_accepted _ _ _ _ _ _ _ received
  rw [updated]
  exact PMTU.update_valid _ _ _ _ _ valid

theorem received_update_bounds (policy : PMTU.Policy) (route : PMTU.Route) (socket : Header)
    (before : PMTU.State) (now : Nat) (source : RelatedICMP.Source) (result : PMTU.Result)
    (received : receive policy route socket before now source = some result) (valid : before.Valid route)
    (observed : Nat) :
    68 ≤ (result.state.current route observed).val ∧ (result.state.current route observed).val ≤ route.mtu.val :=
  ⟨PMTU.State.current_lower _ _ _, PMTU.State.current_le_route _ _
    (received_update_valid _ _ _ _ _ _ _ received valid) _⟩

theorem received_reporter_independent (policy : PMTU.Policy) (route : PMTU.Route) (socket : Header)
    (before : PMTU.State) (now : Nat) (source : RelatedICMP.Source) (reporter : Address) :
    PMTU.feedback policy route socket before now { sourceFeedback source with reporter } =
      receive policy route socket before now source := rfl

/-- Matching decoded fields identify a socket; they do not authenticate a sender. -/
theorem matching_forgery_reduces (policy : PMTU.Policy) (route : PMTU.Route) (socket : Header)
    (before : PMTU.State) (now : Nat) (source : RelatedICMP.Source) (advertised : Word)
    (matching : IPv4QuotePrefix.header source.quote = socket)
    (kind : source.icmp.message.kind = .fragmentationNeeded advertised)
    (unlocked : (route.locked || ((before.age now).exception.map (·.locked)).getD false) = false)
    (above : policy.minimum.val ≤ advertised.val)
    (reducing : advertised.val < (before.current route now).val) :
    ∃ result entry, receive policy route socket before now source = some result ∧
      result.disposition = .updated ∧ result.state.exception = some entry ∧
      entry.mtu.val = advertised.val ∧ entry.mtu.val < (before.current route now).val := by
  have forged := PMTU.feedback_forgery_cached policy route socket before now advertised source.ip.packet.source
    unlocked above reducing
  simpa only [receive, sourceFeedback, matching, kind] using forged

end Netlib.Examples.PMTUDeployment
