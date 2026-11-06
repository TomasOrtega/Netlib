import Netlib.Check.CampusTCPRoundStart
import Netlib.Check.CampusTCPRoundEndpointGeometry

/-!
# Receive guards from actual gateway emissions

The stored rewrite preserves the source TCP fields.
Startup alignment identifies the destination endpoint tuple.
-/

namespace Netlib.Check.CampusTCPRoundEmission

open Protocol.TCP CampusTCPModel CampusTCPEnabled CampusTCPRoundStart

variable {input : Input} {events : List Event} {report : Report input events}
variable {complete : H.Completed input.active input.passive} {request : Request input}
variable {source : DecodedIPv4}

theorem emission_profile (emission : WireForwarding.Emission source) (profile : Admission.DataProfile source.segment) :
    Admission.DataProfile emission.asInput.packet.segment := by
  change Admission.DataProfile emission.decoded.segment
  unfold Admission.DataProfile
  rw [emission.control.2.2.2.1, emission.control.2.2.2.2.2.2]
  exact profile

theorem profile_controls (profile : Admission.DataProfile segment) :
    EstablishedReceive.control segment = none ∧ Flags.ack segment.flags = true := by
  rcases profile with ⟨flags | flags, options⟩
  all_goals
    simp only [EstablishedReceive.control, flags, options]
    exact ⟨rfl, rfl⟩

theorem data_ready (initial : Initial report complete request) (emission : WireForwarding.Emission source)
    (target : emission.target = initial.entry.flow.output .original)
    (sequence : source.segment.sequence = input.active.iss.add 1)
    (acknowledgment : source.segment.acknowledgment = input.passive.iss.add 1)
    (payload : source.segment.payload = request.bytes) (profile : Admission.DataProfile source.segment) :
    ∃ recovery reaction, CampusTCPDeliveryEnabled.InOrderReady
      (endpoint initial.start.next.endpoints .server) emission.asInput recovery reaction := by
  have controls := profile_controls (emission_profile emission profile)
  apply CampusTCPRoundEndpointGeometry.server_ready initial.start emission.asInput
  · change emission.decoded.header = complete.certificate.passiveSeed.core.inbound
    rw [emission.header, target, initial.aligned.serverOutput]
  · exact controls.1
  · exact controls.2
  · exact emission.control.1.trans sequence
  · exact emission.control.2.1.trans acknowledgment
  · change emission.decoded.segment.payload ≠ []
    rw [emission.payload, payload]
    exact request.nonempty
  · change emission.decoded.segment.payload.length ≤ input.passive.capacity
    rw [emission.payload, payload]
    exact request.receiveFits

theorem ack_ready (initial : Initial report complete request) (emission : WireForwarding.Emission source)
    (target : emission.target = initial.entry.flow.output .reply)
    (sequence : source.segment.sequence = input.passive.iss.add 1)
    (acknowledgment : source.segment.acknowledgment = (input.active.iss.add 1).add request.bytes.length)
    (payload : source.segment.payload = []) (profile : Admission.DataProfile source.segment) :
    ∃ recovery reaction, CampusTCPDeliveryEnabled.FullAckReady
      (Endpoint.sendState (endpoint initial.start.next.endpoints .client) request.bytes.length)
      emission.asInput recovery reaction := by
  have controls := profile_controls (emission_profile emission profile)
  apply CampusTCPRoundEndpointGeometry.client_ready initial.start emission.asInput
    request.nonempty request.mssFits request.receiveFits
  · change emission.decoded.header = complete.certificate.activeSeed.core.inbound
    rw [emission.header, target, initial.aligned.clientOutput]
  · exact controls.1
  · exact controls.2
  · exact emission.control.1.trans sequence
  · exact emission.control.2.1.trans acknowledgment
  · exact emission.payload.trans payload

end Netlib.Check.CampusTCPRoundEmission
