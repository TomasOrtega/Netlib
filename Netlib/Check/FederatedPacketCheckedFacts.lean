import Netlib.Check.FederatedPacketCompletion
import Netlib.Check.FederatedPacketReplayEvidence
import Netlib.Check.FederatedPacketSafety

/-!
# Public facts for a checked packet report

The stored report supplies every trace and source index. Safety facts apply
to its actual prefixes and the matching queries in the supplied intent.
-/

namespace Netlib.Federation.InFlight

variable {input : Input} {profile : Profile} {certificate : Certified input profile}
variable {header : Packet.Header} {actions : List Action} {bound : Nat}

theorem Certified.common_history (certificate : Certified input profile) (header : Packet.Header)
    (accepted : certificate.context.first.selector.accepts header = true)
    {events : List (Event input)} {after : State input}
    (trace : (Execution.system certificate.context header).Trace (initialState certificate.context) events after) :
    Safety.CommonHistory certificate.context header events after :=
  Safety.common_history certificate.valid header accepted trace

theorem CheckedExecution.common_history (value : CheckedExecution certificate header actions bound) :
    Safety.CommonHistory certificate.context header (value.report.steps.map Replay.Step.event) value.report.final :=
  certificate.common_history header value.accepted value.report.trace

theorem CheckedExecution.history_at (value : CheckedExecution certificate header actions bound)
    (cut : Nat) (within : cut ≤ value.report.prefix.length) :
    Safety.CommonHistory certificate.context header ((value.report.steps.take cut).map Replay.Step.event)
      (value.report.prefix.state cut) :=
  certificate.common_history header value.accepted (value.report.prefix_trace cut within)

theorem CheckedExecution.isolate_at (value : CheckedExecution certificate header actions bound)
    (cut : Nat) (within : cut ≤ value.report.prefix.length) (query : Query) (member : query ∈ input.intent.queries)
    (kind : query.kind = .isolate) (sameCase : query.caseID = certificate.context.query.caseID)
    (sameSource : query.source = certificate.context.query.source) :
    Safety.publicPosition certificate.context (value.report.prefix.state cut) ≠ query.target :=
  Safety.isolate certificate.valid header value.accepted (value.report.prefix_trace cut within)
    query member kind sameCase sameSource

theorem CheckedExecution.mediated_on (value : CheckedExecution certificate header actions bound)
    (cut : Nat) (within : cut ≤ value.report.prefix.length) (query : Query) (member : query ∈ input.intent.queries)
    (kind : query.kind = .mediated) (sameCase : query.caseID = certificate.context.query.caseID)
    (sameSource : query.source = certificate.context.query.source)
    (reached : Safety.publicPosition certificate.context (value.report.prefix.state cut) = query.target)
    (side : Side) (checkedSide : query.gateways.all (fun gateway => decide (gateway.side = side)) = true) :
    Nonempty (Safety.PEPVisit certificate.context header ((value.report.steps.take cut).map Replay.Step.event)
      (value.report.prefix.state cut) query side) :=
  Safety.mediated_on certificate.valid header value.accepted (value.report.prefix_trace cut within)
    query member kind sameCase sameSource reached side checkedSide

theorem CheckedExecution.receipt_origin (value : CheckedExecution certificate header actions bound) :
    ∃ index, (value.report.prefix.state value.completion).phase = .delivered index ∧
      Nonempty (Replay.ReceiptOrigin value.report index) ∧ index < value.completion := by
  obtain ⟨index, delivered⟩ := value.complete.1
  have origin := value.report.delivered_source value.completion value.within index delivered
  exact ⟨index, delivered, origin.1, origin.2⟩

theorem CheckedExecution.arrival_source (value : CheckedExecution certificate header actions bound)
    (index : Nat) (step : Replay.Step certificate.context header) (found : value.report.steps[index]? = some step)
    (observation : Observation) (sendIndex : Nat) (action : step.action = .arrive observation sendIndex) :
    ∃ stamp, step.before.phase = .flight stamp ∧ step.event.effect = .arrived stamp ∧ sendIndex = stamp.sendIndex ∧
      Nonempty (Replay.SendOrigin value.report stamp) ∧ stamp.sendIndex < index :=
  value.report.arrival_source index step found action

end Netlib.Federation.InFlight
