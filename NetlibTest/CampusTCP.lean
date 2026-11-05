import Netlib.Check.CampusTCP
import Netlib.Check.CampusTCPFacts

namespace NetlibTest.CampusTCP

open Netlib Packet Protocol
namespace M
export Check.CampusTCPModel (Report Step Served)
end M
namespace F
export Check.CampusTCPFacts (Assurance At assure findStep)
end F

structure Demonstration (input : Check.CampusTCP.Input) where
  report : M.Report input.model input.events
  assurance : F.Assurance report
  clientRead : assurance.endpoints.client.steps.flatMap TCP.ApplicationTrace.Step.readBytes = [120, 121, 122]
  serverRead : assurance.endpoints.server.steps.flatMap TCP.ApplicationTrace.Step.readBytes = [97, 98, 99]
  queued : F.At report 43
  served : M.Served input.model
  present : queued.step.result.service = some served
  revoked : queued.step.before.authentication = 8
  oldSource : served.ticket.value.produced.time = 38
  payload : served.ticket.value.source.packet.segment.payload = [100, 101, 102]
  unauthorized : (Check.SessionFirewall.stateAt input.model.context.authentication queued.step.before.authentication).auth.authorized = false

theorem Demonstration.nonempty_prefixes (value : Demonstration input) :
    value.assurance.endpoints.client.steps.flatMap TCP.ApplicationTrace.Step.readBytes ≠ [] ∧
      value.assurance.endpoints.server.steps.flatMap TCP.ApplicationTrace.Step.readBytes ≠ [] ∧
      value.assurance.endpoints.server.steps.flatMap TCP.ApplicationTrace.Step.readBytes <+:
        value.assurance.endpoints.client.steps.flatMap TCP.ApplicationTrace.Step.written ∧
      value.assurance.endpoints.client.steps.flatMap TCP.ApplicationTrace.Step.readBytes <+:
        value.assurance.endpoints.server.steps.flatMap TCP.ApplicationTrace.Step.written := by
  exact ⟨by rw [value.clientRead]; decide, by rw [value.serverRead]; decide, value.assurance.application_prefix⟩

theorem Demonstration.queued_output_none (value : Demonstration input) : value.served.evidence.output = none :=
  Check.CampusTCPFacts.service_output_none_of_unauthorized value.report value.assurance.compliant
    value.queued.step value.queued.member value.served value.present value.unauthorized

private def load : Except String α → IO α
  | .ok value => pure value
  | .error reason => throw (IO.userError reason)

private def ensure (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def check (input : Check.CampusTCP.Input) : Except String (M.Report input.model input.events) :=
  input.check.mapError (·.message)

private def demonstrate (input : Check.CampusTCP.Input) : Except String (Demonstration input) := do
  let report ← check input
  let assurance ← F.assure report
  if clientRead : assurance.endpoints.client.steps.flatMap TCP.ApplicationTrace.Step.readBytes = [120, 121, 122] then
    if serverRead : assurance.endpoints.server.steps.flatMap TCP.ApplicationTrace.Step.readBytes = [97, 98, 99] then
      let queued ← F.findStep report 43
      match present : queued.step.result.service with
      | none => throw "The queued service is absent from the joint replay."
      | some served =>
        if revoked : queued.step.before.authentication = 8 then
          if oldSource : served.ticket.value.produced.time = 38 then
            if payload : served.ticket.value.source.packet.segment.payload = [100, 101, 102] then
              if unauthorized : (Check.SessionFirewall.stateAt input.model.context.authentication
                  queued.step.before.authentication).auth.authorized = false then
                return ⟨report, assurance, clientRead, serverRead, queued, served, present, revoked, oldSource, payload, unauthorized⟩
              else throw "The queued service did not use the revoked authentication state."
            else throw "The queued service replaced the earlier data source."
          else throw "The queued service did not retain the earlier endpoint output."
        else throw "The queued service used a different authentication prefix."
    else throw "The server read does not contain the expected nonempty application bytes."
  else throw "The client read does not contain the expected nonempty application bytes."

private def positive : IO Unit := do
  let input ← load (Check.CampusTCP.Input.parse (← IO.FS.readFile "examples/campus-tcp/trace.json"))
  let value ← load (demonstrate input)
  have prefixes := value.nonempty_prefixes
  have denied := value.queued_output_none
  ensure (value.report.compliant && value.report.steps.length == 44 && value.served.evidence.output.isNone &&
      value.served.before.tracker.records.length == 1 && value.report.final.authentication == 8)
    "The checked history must preserve nonempty reads and deny the earlier queued source after Logoff."
  ensure (decide (value.assurance.endpoints.client.steps.flatMap TCP.ApplicationTrace.Step.readBytes ≠ []) &&
      decide (value.assurance.endpoints.server.steps.flatMap TCP.ApplicationTrace.Step.readBytes ≠ []))
    "The application prefix proofs must have nonempty reads in each direction."
  let _ := prefixes
  let _ := denied

private def fixtureCases : IO Unit := do
  let json ← load (Import.Json.parse (← IO.FS.readFile "examples/campus-tcp/fixtures.json"))
  let cases ← load ((← load (json.getObjVal? "cases")).getArr?)
  let mut checked := 0
  let mut pending := 0
  for row in cases do
    let id ← load (row.getObjValAs? String "id")
    let input ← load (Check.CampusTCP.Input.fromJson (← load (row.getObjVal? "input")))
    let report ← load (check input)
    match report.final.connection with
    | .startup stage _ =>
      ensure stage.passiveSeed.isNone "Pending startup cannot expose a passive application state."
      match F.assure report with
      | .error _ => pending := pending + 1
      | .ok _ => throw (IO.userError "Pending startup cannot produce full application assurance.")
    | .application _ _ =>
      if report.compliant then
        let assurance ← load (F.assure report)
        let _ := assurance.application_prefix
        checked := checked + 1
        if id == "received-bytes-remain-readable-after-logoff" then
          ensure (report.final.authentication == 8 &&
              assurance.endpoints.server.steps.flatMap TCP.ApplicationTrace.Step.readBytes == [97, 98, 99])
            "A later read can retain bytes that an earlier permitted service delivered before Logoff."
        if id == "zero-peer-window-rejects-data-send" then
          ensure ((assurance.endpoints.server.steps.flatMap TCP.ApplicationTrace.Step.readBytes).isEmpty)
            "A valid safety proof does not require a nonempty read in every input trace."
      else
        match F.assure report with
        | .error _ => pure ()
        | .ok _ => throw (IO.userError "A stale or mismatched actual policy cannot produce application assurance.")
  ensure (checked ≥ 7 && pending ≥ 3) "The fixture set must exercise checked, pending, and failed assurance results."

def run : IO Unit := do
  positive
  fixtureCases
  IO.println "Campus TCP composition tests passed."

end NetlibTest.CampusTCP
