import Netlib.Protocol.IPv4InputFragment
import Netlib.Packet.IngressPolicy

/-!
# IPv4 fields before transport reassembly

The envelope contains no transport ports or payload.
Zero ports provide a representative for existing header selectors.
-/

namespace Netlib.Packet

structure IPv4Envelope where
  source : Address
  destination : Address
  protocol : Protocol
  deriving Repr, BEq, DecidableEq

namespace IPv4Envelope

def ofHeader (header : Header) : IPv4Envelope := ⟨header.source, header.destination, header.protocol⟩

def ofPacket (packet : Netlib.Protocol.IPv4.Packet) : IPv4Envelope :=
  ⟨packet.source, packet.destination, packet.protocol⟩

def ofFragment (fragment : Netlib.Protocol.IPv4Fragment.Decoded) : IPv4Envelope := ofPacket fragment.packet.toPacket

def toHeader (envelope : IPv4Envelope) : Header :=
  ⟨envelope.source, envelope.destination, envelope.protocol, 0, 0⟩

def decode (bytes : List UInt8) : Except String IPv4Envelope :=
  ofFragment <$> Netlib.Protocol.IPv4InputFragment.decode bytes

@[simp] theorem ofHeader_toHeader (envelope : IPv4Envelope) : ofHeader envelope.toHeader = envelope := rfl

theorem decode_source (bytes : List UInt8) (envelope : IPv4Envelope) (accepted : decode bytes = .ok envelope) :
    ∃ fragment, Netlib.Protocol.IPv4InputFragment.decode bytes = .ok fragment ∧ ofFragment fragment = envelope := by
  unfold decode at accepted
  cases computed : Netlib.Protocol.IPv4InputFragment.decode bytes with
  | error error =>
    rw [computed] at accepted
    cases accepted
  | ok fragment =>
    rw [computed] at accepted
    exact ⟨fragment, rfl, Except.ok.inj accepted⟩

theorem decode_valid (bytes : List UInt8) (envelope : IPv4Envelope) (accepted : decode bytes = .ok envelope) :
    ∃ fragment, Netlib.Protocol.IPv4InputFragment.decode bytes = .ok fragment ∧ ofFragment fragment = envelope ∧
      fragment.packet.wireLength < 65536 ∧
      Netlib.Protocol.InternetChecksum.valid
        (Netlib.Protocol.IPv4Fragment.headerBytes fragment.packet fragment.checksum) = true := by
  obtain ⟨fragment, computed, selected⟩ := decode_source bytes envelope accepted
  exact ⟨fragment, computed, selected, Netlib.Protocol.IPv4InputFragment.decode_valid bytes fragment computed⟩

end IPv4Envelope

namespace Match

def erasePorts (traffic : Match) : Match := { traffic with sourcePorts := none, destinationPorts := none }

@[simp] theorem erasePorts_idempotent (traffic : Match) : traffic.erasePorts.erasePorts = traffic.erasePorts := rfl

theorem erasePorts_holds (traffic : Match) (header : Header) : traffic.erasePorts.Holds header ↔
    (∀ block, traffic.source = some block → block.contains header.source = true) ∧
    (∀ block, traffic.destination = some block → block.contains header.destination = true) ∧
    (∀ protocol, traffic.protocol = some protocol → protocol = header.protocol) := by
  simp [erasePorts, Holds]

theorem full_selection_implies_coarse (traffic : Match) (header : Header) (selected : traffic.Holds header) :
    traffic.erasePorts.Holds header := (erasePorts_holds traffic header).mpr ⟨selected.1, selected.2.1, selected.2.2.1⟩

theorem full_acceptance_implies_coarse (traffic : Match) (header : Header) (selected : traffic.accepts header = true) :
    traffic.erasePorts.accepts header = true :=
  (accepts_iff _ _).mpr (full_selection_implies_coarse traffic header ((accepts_iff _ _).mp selected))

theorem erasePorts_representative (traffic : Match) (header : Header) :
    traffic.erasePorts.accepts header = traffic.erasePorts.accepts (IPv4Envelope.ofHeader header).toHeader := rfl

theorem erasePorts_sameEnvelope (traffic : Match) (first second : Header)
    (same : IPv4Envelope.ofHeader first = IPv4Envelope.ofHeader second) :
    traffic.erasePorts.accepts first = traffic.erasePorts.accepts second := by
  rw [erasePorts_representative traffic first, erasePorts_representative traffic second, same]

theorem no_ports_sameEnvelope (traffic : Match) (fields : traffic.sourcePorts = none ∧ traffic.destinationPorts = none)
    (first second : Header) (same : IPv4Envelope.ofHeader first = IPv4Envelope.ofHeader second) :
    traffic.accepts first = traffic.accepts second := by
  have erased : traffic.erasePorts = traffic := by cases traffic; simp_all [erasePorts]
  rw [← erased]
  exact erasePorts_sameEnvelope traffic first second same

end Match

namespace IngressPolicy

def NoPorts (policy : Policy) : Prop :=
  ∀ rule ∈ policy.rules, rule.traffic.sourcePorts = none ∧ rule.traffic.destinationPorts = none

def noPorts (policy : Policy) : Bool :=
  policy.rules.all (fun rule => rule.traffic.sourcePorts.isNone && rule.traffic.destinationPorts.isNone)

theorem noPorts_correct (policy : Policy) : noPorts policy = true ↔ NoPorts policy := by
  simp [noPorts, NoPorts]

private theorem noPorts_evaluate (rules : List IngressPolicy.Rule) (fallback : Action)
    (fields : ∀ rule ∈ rules, rule.traffic.sourcePorts = none ∧ rule.traffic.destinationPorts = none)
    (index : Nat) (first second : Header) (same : IPv4Envelope.ofHeader first = IPv4Envelope.ofHeader second) :
    (Policy.mk rules fallback).evaluate index first = (Policy.mk rules fallback).evaluate index second := by
  induction rules with
  | nil => rw [Policy.evaluate_nil, Policy.evaluate_nil]
  | cons rule rules ih =>
    have selected : rule.accepts index first = rule.accepts index second := by
      unfold Rule.accepts
      rw [Match.no_ports_sameEnvelope rule.traffic (fields rule (by simp)) first second same]
    rw [Policy.evaluate_cons, Policy.evaluate_cons, selected,
      ih (fun next member => fields next (List.mem_cons_of_mem _ member))]

theorem noPorts_port_independent (policy : Policy) (fields : NoPorts policy) (index : Nat) (first second : Header)
    (same : IPv4Envelope.ofHeader first = IPv4Envelope.ofHeader second) :
    policy.allows index first = policy.allows index second := by
  change decide (policy.evaluate index first = .permit) = decide (policy.evaluate index second = .permit)
  rw [noPorts_evaluate policy.rules policy.fallback fields index first second same]

theorem noPorts_representative (policy : Policy) (fields : NoPorts policy) (index : Nat) (header : Header) :
    policy.allows index header = policy.allows index (IPv4Envelope.ofHeader header).toHeader :=
  noPorts_port_independent policy fields index header (IPv4Envelope.ofHeader header).toHeader rfl

end IngressPolicy
end Netlib.Packet
