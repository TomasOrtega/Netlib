import Netlib.Check.CampusTCP
import Netlib.Check.CampusTCPDeliveryEnabled
import Netlib.Check.CampusTCPGatewayEnabled
import Netlib.Check.CampusTCPSchedule

namespace NetlibTest.CampusTCPDeliveryEnabled

open Netlib Packet Protocol
namespace M
export Check.CampusTCPModel (Connection Report State beforeService)
end M
namespace D
export Check.CampusTCPDeliveryEnabled (ApplicationSource LinkPending InOrderReady FullAckReady)
end D
namespace A
export Check.CampusTCPEnabled (endpoint)
end A

private def load : Except String α → IO α
  | .ok value => pure value
  | .error reason => throw (IO.userError reason)

private def ensure (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def verify (property : Prop) [Decidable property] (message : String) : Except String { _value : Unit // property } :=
  if accepted : property then .ok ⟨(), accepted⟩ else .error message

private instance (before : M.State input) (gateway : Check.CampusTCPModel.Gateway) :
    Decidable (Check.CampusTCPGatewayEnabled.ServicePhaseReady before gateway) := by
  unfold Check.CampusTCPGatewayEnabled.ServicePhaseReady
  infer_instance

private def serviceReadiness (context : Check.CampusTCPService.Context) (before : Check.CampusTCPService.Before)
    (source : TCP.WireForwarding.Source) (zone : Nat) (ingress : IngressAttachment.InterfaceRef)
    (checks : Check.CampusTCPService.Checks context before ingress) (hop : String) :
    Except String (Σ hit, Σ session, Check.CampusTCPService.ExistingDataReady context before source zone ingress hit session hop) := do
  let budget ← verify (checks.budget = 100000) "The recorded preflight has a different budget."
  let permitted ← verify (before.guard.permits ingress.ifindex.val source.packet.header = true) "The actual ingress guard denies the packet."
  match phase : before.admission.phase with
  | .data session =>
    match _lookup : before.tracker.model.lookup zone source.packet.header with
    | none => throw "The actual pre-service table has no existing binding."
    | some hit =>
      let tracker ← verify (ConntrackLifecycle.ExistingReady (before.configuration.pipeline context.routing)
        before.tracker (Check.CampusTCPService.packetInput before source zone).lifecycle hit hop) "The old table, route, or filters are not ready."
      let binding ← verify (∀ record ∈ before.tracker.records, record.entry.flow = hit.entry → record.entry = session.entry)
        "The old tracker and admission session use different bindings."
      let data ← verify (TCP.Admission.DataReady session hit.direction source.packet.segment) "The old lane geometry is not ready."
      let ttl ← verify (1 < source.packet.ip.packet.ttl.toNat) "The packet TTL cannot traverse the gateway."
      let forward ← verify (checks.forward.passed = true) "The actual current forward comparison fails."
      let guard ← verify (checks.guard.passed = true) "The actual current ingress comparison fails."
      let covered ← verify (Check.CampusTCPService.coverage context source = true) "The packet is outside the application class."
      return ⟨hit, session, ⟨checks, budget.property, permitted.property, tracker.property, phase, binding.property,
        data.property, ttl.property, forward.property, guard.property, covered.property⟩⟩
  | _ => throw "The actual gateway has no established admission session."

private def inspect (report : M.Report input events) : IO (Nat × Nat × Nat) := do
  let mut dataCuts := 0
  let mut ackCuts := 0
  let mut serviceCuts := 0
  for count in List.range (report.steps.length + 1) do
    if within : count ≤ report.steps.length then
      let cut := Check.CampusTCPSchedule.Report.cut report count within
      if inside : count < report.steps.length then
        match currentAt : report.steps[count]? with
        | none => pure ()
        | some current =>
          have beforeEq : current.before = cut.final := by
            obtain ⟨actual, found, before, _, _⟩ := Check.CampusTCPSchedule.Trace.at report.trace count inside
            have same : actual = current := Option.some.inj (found.symm.trans currentAt)
            subst actual
            exact before
          match serviceAt : current.result.service with
          | none => pure ()
          | some served =>
            match event : current.event with
            | .serve id none =>
              have sourceBefore : served.before = M.beforeService input cut.final served.ticket.value.gateway := by
                obtain ⟨_, _, _, before, _, _⟩ := Check.CampusTCPFacts.serve_origin current id none event served serviceAt
                exact before.trans (congrArg (fun state => M.beforeService input state served.ticket.value.gateway) beforeEq)
              let checks : Check.CampusTCPService.Checks (input.contextFor served.ticket.value.gateway)
                  (M.beforeService input cut.final served.ticket.value.gateway) served.ticket.value.ingress :=
                sourceBefore ▸ served.evidence.checks
              match serviceReadiness (input.contextFor served.ticket.value.gateway)
                  (M.beforeService input cut.final served.ticket.value.gateway) served.ticket.value.source input.zone
                  served.ticket.value.ingress checks served.ticket.value.produced.actor.nextHop with
              | .error _ => pure ()
              | .ok ready =>
                if phase : Check.CampusTCPGatewayEnabled.ServicePhaseReady cut.final served.ticket.value.gateway then
                  have pending : served.ticket ∈ cut.final.work.pending := by
                    obtain ⟨completed, _, ticket, _, _, _⟩ := Check.CampusTCPFacts.serve_origin current id none event served serviceAt
                    rw [ticket, ← beforeEq]
                    exact completed.member
                  let _ := Check.CampusTCPService.run_existing_enabled (input.contextFor served.ticket.value.gateway)
                    (M.beforeService input cut.final served.ticket.value.gateway) served.ticket.value.source input.zone
                    served.ticket.value.ingress ready.1 ready.2.1 served.ticket.value.produced.actor.nextHop ready.2.2
                  let _ := Check.CampusTCPGatewayEnabled.Report.serve_enabled cut served.ticket pending phase ready.1 ready.2.1 ready.2.2
                  serviceCuts := serviceCuts + 1
            | _ => pure ()
      match connection : cut.final.connection with
      | .startup .. => pure ()
      | .recovering .. => throw (IO.userError "The ordinary delivery test prefix entered recovery.")
      | .application complete endpoints =>
        for index in List.range cut.final.services.length do
          match found : cut.final.services[index]? with
          | none => pure ()
          | some served =>
            if application : D.ApplicationSource served.ticket.value.produced then
              if pending : D.LinkPending cut.final index then
                match emitted : served.evidence.output with
                | none => pure ()
                | some emission =>
                  let state := A.endpoint endpoints served.ticket.value.produced.actor.other
                  match state.recovery, state.ackReaction with
                  | some recovery, some reaction =>
                    if ready : D.InOrderReady state emission.asInput recovery reaction then
                      let _ := Check.CampusTCPDeliveryEnabled.Report.deliver_inOrder_enabled cut complete endpoints connection
                        index served found emission emitted application pending recovery reaction ready
                      let wrong : TCP.Endpoint.State := { state with core := { state.core with inbound := ⟨0, 0, Packet.Protocol.tcp, 0, 0⟩ } }
                      ensure (!decide (D.InOrderReady wrong emission.asInput recovery reaction))
                        "An old packet with a different receiver tuple cannot satisfy delivery readiness."
                      dataCuts := dataCuts + 1
                    if ready : D.FullAckReady state emission.asInput recovery reaction then
                      let _ := Check.CampusTCPDeliveryEnabled.Report.deliver_fullAck_enabled cut complete endpoints connection
                        index served found emission emitted application pending recovery reaction ready
                      ackCuts := ackCuts + 1
                  | _, _ => pure ()
  return (dataCuts, ackCuts, serviceCuts)

def run : IO Unit := do
  let input ← load (Check.CampusTCP.Input.parse (← IO.FS.readFile "examples/tcp-ack/trace.json"))
  let report ← load (input.check.mapError (·.message))
  let counts ← inspect report
  ensure (report.compliant && counts.1 > 0 && counts.2.1 > 0 && counts.2.2 > 0)
    "One actual campus history must supply service, data-delivery, and full-ACK readiness at real pending packet cuts."
  IO.println s!"Campus delivery predecessor tests passed: {counts.1} data cuts, {counts.2.1} ACK cuts, {counts.2.2} service cuts."

end NetlibTest.CampusTCPDeliveryEnabled
