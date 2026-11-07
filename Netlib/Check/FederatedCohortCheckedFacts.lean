import Netlib.Check.FederatedCohortCompletion
import Netlib.Check.FederatedCohortReplayEvidence
import Netlib.Check.FederatedCohortFacts

/-!
# Closed safety and source facts for checked cohort reports

Every packet uses the same actual prefix and clock. Source witnesses retain
the original cohort steps and their old native revisions.
-/

namespace Netlib.Federation.Cohort

variable {input : Input} {profile : Profile} {certificate : Certified input profile}
variable {headers : Vector Packet.Header certificate.prepared.size} {actions : List InFlight.Action} {bound : Nat}

theorem Certified.common_history (certificate : Certified input profile)
    (headers : Vector Packet.Header certificate.prepared.size) (accepted : Accepted certificate.prepared.context headers)
    {events : List (Event input certificate.prepared.size)} {after : State input certificate.prepared.size}
    (trace : (Execution.system certificate.prepared.context headers).Trace
      (initialState certificate.prepared.context) events after) (index : Fin certificate.prepared.size) :
    Safety.CommonHistory certificate.prepared.context headers index events after :=
  Safety.common_history certificate.prepared.family headers accepted trace index

theorem CheckedExecution.common_history (value : CheckedExecution certificate headers actions bound)
    (index : Fin certificate.prepared.size) :
    Safety.CommonHistory certificate.prepared.context headers index
      (value.report.steps.map Replay.Step.event) value.report.final :=
  certificate.common_history headers value.accepted value.report.trace index

theorem CheckedExecution.history_at (value : CheckedExecution certificate headers actions bound)
    (cut : Nat) (within : cut ≤ value.report.prefix.length) (index : Fin certificate.prepared.size) :
    Safety.CommonHistory certificate.prepared.context headers index ((value.report.steps.take cut).map Replay.Step.event)
      (value.report.prefix.state cut) :=
  certificate.common_history headers value.accepted (value.report.prefix_trace cut within) index

theorem CheckedExecution.isolate_at (value : CheckedExecution certificate headers actions bound)
    (cut : Nat) (within : cut ≤ value.report.prefix.length) (index : Fin certificate.prepared.size)
    (query : Query) (member : query ∈ input.intent.queries) (kind : query.kind = .isolate)
    (sameCase : query.caseID = (certificate.prepared.context.packets.get index).query.caseID)
    (sameSource : query.source = (certificate.prepared.context.packets.get index).query.source) :
    InFlight.Safety.publicPosition (certificate.prepared.context.packets.get index)
      ((value.report.prefix.state cut).packet index) ≠ query.target :=
  Safety.isolate certificate.prepared.family headers value.accepted (value.report.prefix_trace cut within)
    index query member kind sameCase sameSource

theorem CheckedExecution.mediated_on (value : CheckedExecution certificate headers actions bound)
    (cut : Nat) (within : cut ≤ value.report.prefix.length) (index : Fin certificate.prepared.size)
    (query : Query) (member : query ∈ input.intent.queries) (kind : query.kind = .mediated)
    (sameCase : query.caseID = (certificate.prepared.context.packets.get index).query.caseID)
    (sameSource : query.source = (certificate.prepared.context.packets.get index).query.source)
    (reached : InFlight.Safety.publicPosition (certificate.prepared.context.packets.get index)
      ((value.report.prefix.state cut).packet index) = query.target)
    (side : Side) (checkedSide : query.gateways.all (fun gateway => decide (gateway.side = side)) = true) :
    Nonempty (Safety.PEPVisit certificate.prepared.context headers index ((value.report.steps.take cut).map Replay.Step.event)
      (value.report.prefix.state cut) query side) :=
  Safety.mediated_on certificate.prepared.family headers value.accepted (value.report.prefix_trace cut within)
    index query member kind sameCase sameSource reached side checkedSide

theorem CheckedExecution.valid_at (value : CheckedExecution certificate headers actions bound)
    (cut : Nat) (within : cut ≤ value.report.prefix.length) :
    (value.report.prefix.state cut).Valid certificate.prepared.context headers :=
  Progress.valid_at (certificate.cellAt headers value.accepted).checked value.report.prefix value.report.initial cut within

theorem CheckedExecution.capacity_at (value : CheckedExecution certificate headers actions bound)
    (cut : Nat) (within : cut ≤ value.report.prefix.length) (node : InFlight.Node)
    (present : node ∈ InFlight.Control.nodes input) :
    Control.occupancy (value.report.prefix.state cut).key node ≤ Control.capacity certificate.prepared.context node :=
  Control.occupancy_le_capacity _ _ (value.valid_at cut within).1 node present

theorem CheckedExecution.receipt_origin (value : CheckedExecution certificate headers actions bound)
    (index : Fin certificate.prepared.size) :
    ∃ receipt, ((value.report.prefix.state value.completion).packet index).phase = .delivered receipt ∧
      Nonempty (Replay.ReceiptOrigin value.report index receipt) ∧ receipt < value.completion := by
  obtain ⟨receipt, delivered⟩ := value.complete.1 index
  have origin := value.report.delivered_source index value.completion value.within receipt delivered
  exact ⟨receipt, delivered, origin⟩

theorem CheckedExecution.flight_source (value : CheckedExecution certificate headers actions bound)
    (cut : Nat) (within : cut ≤ value.report.prefix.length) (index : Fin certificate.prepared.size)
    (stamp : InFlight.Stamp input) (flight : ((value.report.prefix.state cut).packet index).phase = .flight stamp) :
    Nonempty (Replay.SendOrigin value.report index stamp) ∧ stamp.sendIndex < cut :=
  value.report.flight_source index cut within stamp flight

theorem CheckedExecution.arrival_source (value : CheckedExecution certificate headers actions bound)
    (slot : Nat) (step : Replay.Step certificate.prepared.context headers) (found : value.report.steps[slot]? = some step)
    (observation : InFlight.Observation) (sendIndex : Nat) (action : step.action = .arrive observation sendIndex) :
    ∃ index stamp, (step.before.packet index).phase = .flight stamp ∧ step.event.effects.get index = .arrived stamp ∧
      sendIndex = stamp.sendIndex ∧ Nonempty (Replay.SendOrigin value.report index stamp) ∧ stamp.sendIndex < slot :=
  value.report.arrival_source slot step found observation sendIndex action

theorem CheckedExecution.native_source (value : CheckedExecution certificate headers actions bound)
    (index : Fin certificate.prepared.size) (stamp : InFlight.Stamp input) (origin : Replay.SendOrigin value.report index stamp) :
    Nonempty (Provenance.Origin input.left.contract input.right.contract
      (input.left.revisionAt stamp.current.1) (input.right.revisionAt stamp.current.2)
      (certificate.prepared.context.packets.get index).first (certificate.prepared.context.packets.get index).second
      input.intent (headers.get index) stamp.source stamp.target) := origin.native_source certificate.prepared.deployment

theorem CheckedExecution.flight_identity_unique (value : CheckedExecution certificate headers actions bound)
    (cut : Nat) (within : cut ≤ value.report.prefix.length) (first second : Fin certificate.prepared.size)
    (a b : InFlight.Stamp input)
    (firstFlight : ((value.report.prefix.state cut).packet first).phase = .flight a)
    (secondFlight : ((value.report.prefix.state cut).packet second).phase = .flight b)
    (sameID : a.packetID = b.packetID) : first = second :=
  Safety.flight_identity_unique certificate.prepared.context certificate.prepared.unique headers
    (value.report.prefix_trace cut within) first second a b firstFlight secondFlight sameID

end Netlib.Federation.Cohort
