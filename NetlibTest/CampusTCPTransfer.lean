import Netlib.Check.CampusTCP
import Netlib.Check.CampusTCPTransferFacts

namespace NetlibTest.CampusTCPTransfer

open Netlib Packet Protocol
namespace M
export Check.CampusTCPModel (Input State Step Event Report)
end M
namespace F
export Check.CampusTCPTransferFacts (assure checkpoint_origin installation_origin fence_origin resume_origin)
end F

def serverSent : Check.CampusTCPModel.Connection active passive → Option (List UInt8)
  | .startup .. | .recovering .. => none
  | .application _ endpoints => some endpoints.server.current.core.sent

structure Demonstration (input : Check.CampusTCP.Input) where
  report : M.Report input.model input.events
  assurance : Check.CampusTCPTransferFacts.Assurance report
  clientRead : assurance.application.endpoints.client.steps.flatMap TCP.ApplicationTrace.Step.readBytes = [120, 121, 122, 119]
  serverRead : assurance.application.endpoints.server.steps.flatMap TCP.ApplicationTrace.Step.readBytes = [97, 98, 99, 100, 101, 102]
  acknowledgment : Check.CampusTCPFacts.At report 50
  copied : TCP.Admission.Session
  sourcePhase : assurance.installation.checkpoint.snapshot.source.admission.phase = .data copied
  deferred : copied.reply.observed = 3 ∧ copied.reply.highEnd = 3 ∧ copied.reply.acknowledged = 0
  exactBefore : acknowledgment.step.before.standby.transport = assurance.installation.checkpoint.snapshot.source
  after : TCP.Admission.Session
  targetPhase : acknowledgment.step.result.state.standby.transport.admission.phase = .data after
  removed : after.reply.observed = 3 ∧ after.reply.acknowledged = 3 ∧ after.reply.outstanding = 0
  resumed : assurance.resume.step.before.time < acknowledgment.step.before.time
  served : Check.CampusTCPModel.Served input.model
  service : acknowledgment.step.result.service = some served
  standby : served.ticket.value.gateway = .standby
  acknowledges : served.ticket.value.source.packet.segment.acknowledgment = copied.reply.next
  endpointAck : Check.CampusTCPFacts.At report 51
  sentBefore : serverSent endpointAck.step.before.connection = some [120, 121, 122]
  sentAfter : serverSent endpointAck.step.result.state.connection = some []

theorem Demonstration.nonempty_prefixes (value : Demonstration input) :
    value.assurance.application.endpoints.client.steps.flatMap TCP.ApplicationTrace.Step.readBytes ≠ [] ∧
      value.assurance.application.endpoints.server.steps.flatMap TCP.ApplicationTrace.Step.readBytes ≠ [] ∧
      value.assurance.application.endpoints.server.steps.flatMap TCP.ApplicationTrace.Step.readBytes <+:
        value.assurance.application.endpoints.client.steps.flatMap TCP.ApplicationTrace.Step.written ∧
      value.assurance.application.endpoints.client.steps.flatMap TCP.ApplicationTrace.Step.readBytes <+:
        value.assurance.application.endpoints.server.steps.flatMap TCP.ApplicationTrace.Step.written :=
  ⟨by rw [value.clientRead]; decide, by rw [value.serverRead]; decide, value.assurance.application_prefix⟩

theorem Demonstration.deferred_ack (value : Demonstration input) :
    value.acknowledgment.step.before.standby.transport = value.assurance.installation.checkpoint.snapshot.source ∧
      value.copied.reply.outstanding = 3 ∧
      value.served.ticket.value.source.packet.segment.acknowledgment = value.copied.reply.next ∧
      value.after.reply.outstanding = 0 ∧
      serverSent value.endpointAck.step.before.connection = some [120, 121, 122] ∧
      serverSent value.endpointAck.step.result.state.connection = some [] := by
  exact ⟨value.exactBefore, by simp [TCP.Admission.Lane.outstanding, value.deferred.2.1, value.deferred.2.2],
    value.acknowledges, value.removed.2.2, value.sentBefore, value.sentAfter⟩

private def ensure (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def load : Except String α → IO α
  | .ok value => pure value
  | .error reason => throw (IO.userError reason)


private def operation (report : M.Report input events) (index : Nat) : IO (M.Step input) :=
  match report.steps[index]? with
  | none => throw (IO.userError "The transfer operation is missing from the actual replay.")
  | some step => pure step

private def session (gateway : TCP.Checkpoint.Gateway) : IO TCP.Admission.Session :=
  match gateway.admission.phase with
  | .data value => pure value
  | _ => throw (IO.userError "The transfer has no established TCP admission history.")

private def controlProofs (report : M.Report input events) : IO Unit := do
  for step in report.steps do
    match event : step.event with
    | .stageCheckpoint =>
      match present : step.result.checkpoint with
      | none => throw (IO.userError "The source cut is absent from the staging result.")
      | some checkpoint =>
        let _ := F.checkpoint_origin step event checkpoint present
        ensure (checkpoint.snapshot.source.same step.before.primary.transport &&
          checkpoint.time == step.before.time && checkpoint.snapshot.cut == step.before.primary.history.length)
          "The staged cut must name the actual source history and operation time."
    | .installCheckpoint executionNS =>
      match present : step.result.installation with
      | none => throw (IO.userError "The target install result is missing.")
      | some installed =>
        let _ := F.installation_origin step executionNS event installed present
        ensure (step.before.assignmentPaused && step.before.outstanding .primary == 0 &&
          step.result.state.primarySealed && step.result.state.standby.transport.same installed.checkpoint.snapshot.source)
          "Installation must use a paused, drained, exact source and seal primary processing."
    | .fencePrimary =>
      let _ := F.fence_origin step event
      ensure (step.result.state.primaryFenced && step.before.outstanding .primary == 0)
        "The primary tickets must be processed before the actual fence."
    | .resume =>
      let _ := F.resume_origin step event
      ensure (!step.result.state.assignmentPaused && step.before.primaryFenced)
        "Assignments must resume only after the actual primary fence."
    | _ => pure ()
    if fenced : step.before.primaryFenced = true then
      match present : step.result.service with
      | none => pure ()
      | some served =>
        let _ := Check.CampusTCPTransferFacts.service_after_fence step served present fenced
        ensure (served.ticket.value.gateway == .standby)
          "A service after the actual primary fence must use the standby."

private def rejected (value : Except Check.CampusTCPModel.Error α) (text : String) : IO Unit :=
  match value with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError text)

private def demonstrate (input : Check.CampusTCP.Input) : Except String (Demonstration input) := do
  let report ← input.check.mapError (·.message)
  let assurance ← F.assure report
  if clientRead : assurance.application.endpoints.client.steps.flatMap TCP.ApplicationTrace.Step.readBytes = [120, 121, 122, 119] then
    if serverRead : assurance.application.endpoints.server.steps.flatMap TCP.ApplicationTrace.Step.readBytes = [97, 98, 99, 100, 101, 102] then
      let acknowledgment ← Check.CampusTCPFacts.findStep report 50
      match sourcePhase : assurance.installation.checkpoint.snapshot.source.admission.phase with
      | .data copied =>
        match targetPhase : acknowledgment.step.result.state.standby.transport.admission.phase with
        | .data after =>
          if deferred : copied.reply.observed = 3 ∧ copied.reply.highEnd = 3 ∧ copied.reply.acknowledged = 0 then
            if exactBefore : acknowledgment.step.before.standby.transport.same assurance.installation.checkpoint.snapshot.source = true then
              if removed : after.reply.observed = 3 ∧ after.reply.acknowledged = 3 ∧ after.reply.outstanding = 0 then
                if resumed : assurance.resume.step.before.time < acknowledgment.step.before.time then
                  match service : acknowledgment.step.result.service with
                  | none => throw "The deferred acknowledgment has no actual gateway service."
                  | some served =>
                    if standby : served.ticket.value.gateway = .standby then
                      if acknowledges : served.ticket.value.source.packet.segment.acknowledgment = copied.reply.next then
                        let endpointAck ← Check.CampusTCPFacts.findStep report 51
                        if sentBefore : serverSent endpointAck.step.before.connection = some [120, 121, 122] then
                          if sentAfter : serverSent endpointAck.step.result.state.connection = some [] then
                            return ⟨report, assurance, clientRead, serverRead, acknowledgment, copied, sourcePhase, deferred,
                              (TCP.Checkpoint.Gateway.same_correct _ _).mp exactBefore, after, targetPhase, removed, resumed,
                              served, service, standby, acknowledges, endpointAck, sentBefore, sentAfter⟩
                          else throw "The endpoint ACK did not remove its actual unacknowledged server bytes."
                        else throw "The endpoint had different unacknowledged bytes before deferred ACK delivery."
                      else throw "The deferred ACK does not name the copied reply cursor."
                    else throw "The deferred acknowledgment did not use the installed standby."
                else throw "The deferred acknowledgment preceded assignment resumption."
              else throw "The deferred acknowledgment did not remove the transferred reply bytes."
            else throw "The acknowledgment did not start from the exact installed source cut."
          else throw "The copied reply epoch is not a complete deferred prefix."
        | _ => throw "The acknowledgment result has no TCP application admission phase."
      | _ => throw "The installed source has no TCP application admission phase."
    else throw "The server read does not contain the expected bytes spanning transfer."
  else throw "The client read does not contain the expected bytes spanning transfer."

def run : IO Unit := do
  let input ← load (Check.CampusTCP.Input.parse (← IO.FS.readFile "examples/campus-tcp-transfer/trace.json"))
  let demonstration ← load (demonstrate input)
  let report := demonstration.report
  let _ := demonstration.nonempty_prefixes
  let _ := demonstration.deferred_ack
  ensure (report.compliant && report.steps.length == 71 && report.remaining.isEmpty)
    "The full planned transfer trace must be supported and compliant."
  let assurance ← load (F.assure report)
  let _ := assurance.application_prefix
  let clientReads := assurance.application.endpoints.client.steps.flatMap TCP.ApplicationTrace.Step.readBytes
  let serverReads := assurance.application.endpoints.server.steps.flatMap TCP.ApplicationTrace.Step.readBytes
  ensure (clientReads == [120, 121, 122, 119] && serverReads == [97, 98, 99, 100, 101, 102])
    "The same endpoint histories must read nonempty bytes from the two gateways."
  for count in [44, 45, 46, 47] do
    let prefixReport ← load ((input.model.check (input.events.take count)).mapError (·.message))
    match F.assure prefixReport with
    | .error _ => pure ()
    | .ok _ => throw (IO.userError "An unfinished route, fence, or resume sequence must remain pending.")
  let reorderedEvents := (input.events.eraseIdx 38).insertIdx 42 (.pause)
  let reordered ← load ((input.model.check reorderedEvents).mapError (·.message))
  let _ ← load (Check.CampusTCPFacts.assure reordered)
  let _ ← load (F.assure reordered)
  controlProofs report
  let old ← operation report 39
  let drained ← operation report 41
  let stage ← operation report 42
  let installed ← operation report 43
  let resumed ← operation report 47
  let acknowledged ← operation report 50
  let original ← session installed.before.primary.transport
  ensure (original.original.observed == 3 && original.original.acknowledged == 3 &&
    original.reply.observed == 3 && original.reply.acknowledged == 0 && original.reply.outstanding == 3)
    "The installed cut must carry nonzero directional history and deferred reply acknowledgments."
  let settled ← session acknowledged.result.state.standby.transport
  ensure (settled.reply.acknowledged == 3 && settled.reply.outstanding == 0 &&
    acknowledged.before.primaryFenced && acknowledged.result.state.primary.transport.same installed.before.primary.transport)
    "The standby ACK must use the copied reply epoch while the source remains unchanged."
  ensure (old.result.state.primary.history.length == 5 && stage.result.state.primary.history.length == 6)
    "The explicit primary drain must advance the source cut before restaging."
  let targetNS := (input.model.deployment .standby).executionNS
  rejected (Check.CampusTCPModel.step input.model drained.result.state (.installCheckpoint targetNS))
    "A stale cache must not become a current source cut after primary service."
  rejected (Check.CampusTCPModel.step input.model stage.result.state
    (.installCheckpoint { targetNS with birth := targetNS.birth + 1 }))
    "A different target namespace lifetime must not authorize installation."
  let occupied := { stage.result.state with standby := { stage.result.state.standby with
    transport := stage.result.state.primary.transport, history := stage.result.state.primary.history } }
  rejected (Check.CampusTCPModel.step input.model occupied (.installCheckpoint targetNS))
    "A target with existing transport state must not accept the checkpoint."
  let paused ← operation report 38
  let ingress := (input.model.deployment .primary).authenticationPort
  rejected (Check.CampusTCPModel.step input.model paused.result.state (.assign 0 ingress))
    "The pause must block new assignment before ticket lookup."
  ensure (resumed.result.state.primaryFenced && !resumed.result.state.assignmentPaused)
    "The resumed suffix must retain the primary fence."
  let denied ← operation report 70
  match denied.result.service with
  | none => throw (IO.userError "The post-Logoff standby service is missing.")
  | some served =>
    ensure (served.evidence.output.isNone && served.ticket.value.gateway == .standby &&
      !denied.result.state.standby.transport.tracker.records.isEmpty)
      "Current standby denial must suppress output while retaining the copied NAT binding."
  IO.println "Checked campus TCP transfer tests passed."

end NetlibTest.CampusTCPTransfer
