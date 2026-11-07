import Netlib.Check.CampusTCPRecoveryStartupCurrentSources
import Netlib.Check.TCPHandshakeRecoveryReceiveConditions

/-!
# A startup receive input from a current actual link

The source occurrence stamp, service index, and custody ID remain separate.
-/

namespace Netlib.Check.CampusTCPRecoveryStartupLinkInput

open Protocol.TCP CampusTCPModel

namespace J
export CampusTCPStartupJobs (Source Job PacketItem)
end J
namespace C
export TCPHandshakeRecovery (ReceiveInput)
end C

variable {input : Input} {events : List Event} {report : Report input events}
variable {current : TCPHandshakeRecovery.State input.active input.passive} {source : J.Source input}

theorem source_earlier (origin : CampusTCPRecoveryStartupCurrentSources.ProducedAt report source) :
    source.occurrence.index < report.final.time := by
  obtain ⟨prior, later, history, preceding, _, _⟩ :=
    CampusTCPFacts.step_origin report origin.producer origin.member
  have first := CampusTCPOrigins.Trace.time preceding
  have last := CampusTCPOrigins.Trace.time report.trace
  have length := congrArg List.length history
  simp only [List.length_append, List.length_cons] at length
  have stamp := CampusTCPRecoveryStartupOrigins.Step.recovery_stamp origin.producer source.actual origin.recorded
  have outputStamp := source.actual.records.outputIndex source.occurrence source.emitted
  omega

theorem link_input (report : Report input events) (connected : report.final.connection = .recovering current)
    (item : J.PacketItem input) (serviceIndex : Nat) (served : Served input)
    (emission : W.Emission served.ticket.value.source.packet) (emitted : served.evidence.output = some emission)
    (source : J.Source input) (production : served.ticket.value.produced = source.produced)
    (payload : item.value.payload = .link serviceIndex served emission emitted)
    (pending : item ∈ report.final.custody.pending) :
    ∃ value : C.ReceiveInput current report.final.time .rewrite,
      value.source = source.occurrence ∧ value.packet = emission.asInput ∧
      value.event = .receive source.occurrence.index emission.bytes .rewrite true := by
  let job : J.Job input := .link item serviceIndex served emission emitted source production payload
  have jobPending : job.Pending report.final := pending
  obtain ⟨origin⟩ := CampusTCPRecoveryStartupCurrentSources.Job.source_at report job jobPending
  have member := origin.recovering_member connected
  change source.occurrence ∈ current.emissions at member
  have reachable := CampusTCPRecoveryStartupOrigins.Report.recoveryReachable report connected
  have selected := reachable.history.source_of_member member
  have earlier := source_earlier origin
  have original : served.ticket.value.source.asInput = source.occurrence.packet := by
    simp only [Ticket.source, production, CampusTCPStartupJobs.Source.produced, Produced.source, Produced.output,
      WireForwarding.Source.asInput_ofInput]
  have delivered : ∃ delivery : HandshakeExchange.Delivery source.occurrence.packet
      (TCPHandshake.spec emission.asInput .rewrite), delivery.input = emission.asInput := by
    rw [← original]
    exact TCPHandshakeWireDelivery.emission_delivery served.ticket.value.source emission
  obtain ⟨delivery, same⟩ := delivered
  exact ⟨⟨source.occurrence, selected, earlier, emission.asInput, delivery, same⟩, rfl, rfl, rfl⟩


theorem input_shape (report : Report input events) (connected : report.final.connection = .recovering current)
    (value : C.ReceiveInput current report.final.time .rewrite) :
    TCPHandshakeRecovery.OutputShape input.active input.passive value.source :=
  (CampusTCPRecoveryStartupOrigins.Report.recoveryReachable report connected).output_shape
    (List.mem_of_find?_eq_some value.selected)

theorem input_actor (report : Report input events) (connected : report.final.connection = .recovering current)
    (value : C.ReceiveInput current report.final.time .rewrite) : value.source.actor = value.source.kind.actor :=
  (input_shape report connected value).actorEq

end Netlib.Check.CampusTCPRecoveryStartupLinkInput
