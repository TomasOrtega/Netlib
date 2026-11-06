import Netlib.Check.CampusTCP
import Netlib.Check.CampusTCPSchedule
import Netlib.Check.CampusTCPChronology

namespace NetlibTest.CampusTCPSchedule

open Netlib
namespace M
export Check.CampusTCPModel (Report Event)
end M
namespace S
export Check.CampusTCPSchedule (system stateAt eventAt)
end S

theorem actual_final (report : M.Report input events) :
    (Check.CampusTCPSchedule.Trace.prefix report.trace).state report.steps.length = report.final :=
  Check.CampusTCPSchedule.Trace.last_state report.trace

theorem actual_slot (report : M.Report input events) (index : Nat) (within : index < report.steps.length) :
    ∃ effect, Check.CampusTCPModel.step input (S.stateAt input.initial report.steps index)
      (S.eventAt report.steps index) = .ok effect ∧
      effect.state = S.stateAt input.initial report.steps (index + 1) :=
  (Check.CampusTCPSchedule.Trace.prefix report.trace).checked index within

private def load : Except String α → IO α
  | .ok value => pure value
  | .error reason => throw (IO.userError reason)

private def ensure (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def checkStates (report : M.Report input events) : IO Unit := do
  let execution := Check.CampusTCPSchedule.Trace.prefix report.trace
  let _ := actual_final report
  let _ := Check.CampusTCPChronology.Report.chronological report
  let _ := Check.CampusTCPOrigins.Report.work_valid report
  ensure (execution.length == report.steps.length && (execution.state 0).time == 0)
    "The checked prefix must start at the actual initial state."
  for (step, index) in report.steps.zipIdx do
    ensure ((Check.CampusTCP.stateJson (execution.state index)).compress == (Check.CampusTCP.stateJson step.before).compress &&
        (Check.CampusTCP.eventJson (execution.action index)).compress == (Check.CampusTCP.eventJson step.event).compress &&
        (Check.CampusTCP.stateJson (execution.state (index + 1))).compress == (Check.CampusTCP.stateJson step.result.state).compress)
      "Each finite slot must retain the same actual state, event, and stored result."
  ensure ((Check.CampusTCP.stateJson (execution.state execution.length)).compress == (Check.CampusTCP.stateJson report.final).compress)
    "The final checked slot must end at the actual report state."

def run : IO Unit := do
  let input ← load (Check.CampusTCP.Input.parse (← IO.FS.readFile "examples/packet-custody/trace.json"))
  let report ← load (input.check.mapError (·.message))
  checkStates report
  ensure (report.supported && report.steps.length == 175) "The complete custody example must retain all actual slots."
  let some reopen := input.events.find? (fun event => match event with | .open .. => true | _ => false)
    | throw (IO.userError "The actual initial open event is missing.")
  let stopped := { input with events := input.events ++ [reopen, .write .client [], .write .server []] }
  let report ← load (stopped.check.mapError (·.message))
  checkStates report
  ensure (!report.supported && report.steps.length == 176 && report.remaining.length == 2 && stopped.events.length == 178)
    "An unsupported operation must retain its unread suffix without adding fictitious service slots."
  IO.println "Campus finite schedule tests passed."

end NetlibTest.CampusTCPSchedule
