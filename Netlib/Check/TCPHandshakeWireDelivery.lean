import Netlib.Check.TCPHandshake
import Netlib.Protocol.TCP.WireForwardingEmissionDeterminism

/-!
# Startup delivery from an actual gateway emission

The stored rewrite supplies the exact received bytes and delivery path.
No endpoint processing result is an input.
-/

namespace Netlib.Check.TCPHandshakeWireDelivery

open Protocol.TCP

namespace X
export HandshakeExchange (Delivery DeliverySpec)
end X
namespace W
export WireForwarding (Source Emission decrementTTL)
end W

theorem input_parsed (packet : Handshake.Input) : EstablishedReceive.input packet.bytes = .ok packet := by
  cases packet with
  | mk bytes packet checked =>
    unfold EstablishedReceive.input
    split
    · rename_i reason failed
      rw [checked] at failed
      cases failed
    · rename_i selected decoded
      have same := Except.ok.inj (decoded.symm.trans checked)
      subst selected
      rfl

theorem emission_delivery (source : W.Source) (emission : W.Emission source.packet) :
    ∃ delivery : X.Delivery source.asInput (TCPHandshake.spec emission.asInput .rewrite),
      delivery.input = emission.asInput := by
  let routed := HandshakeExchange.Delivery.rewritten source.asInput emission.target
    (W.decrementTTL source.packet) emission.transport
  refine ⟨⟨emission.asInput, rfl, routed.routed, ?_, ?_⟩, rfl⟩
  · change HandshakeExchange.route source.asInput
      [⟨emission.decoded.header, emission.decoded.ip.packet.ttl⟩] = .ok routed.routed
    rw [emission.header, show emission.decoded.ip.packet.ttl = W.decrementTTL source.packet from emission.rewritten.ttl]
    exact routed.generated
  · change emission.bytes = (source.asInput.rewrite emission.target (W.decrementTTL source.packet) emission.transport).bytes
    exact source.emission_bytes emission

theorem emission_checked (source : W.Source) (emission : W.Emission source.packet) :
    ∃ delivery : X.Delivery source.asInput (TCPHandshake.spec emission.asInput .rewrite),
      (TCPHandshake.spec emission.asInput .rewrite).check source.asInput = .ok delivery ∧
        delivery.input = emission.asInput := by
  obtain ⟨delivery, same⟩ := emission_delivery source emission
  exact ⟨delivery, delivery.checked, same⟩

end Netlib.Check.TCPHandshakeWireDelivery
