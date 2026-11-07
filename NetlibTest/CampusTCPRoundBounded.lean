import Netlib.Check.CampusTCPRoundBounded
import Netlib.Check.CampusTCPRoundReport
import NetlibTest.CampusTCPRoundTheorem

namespace NetlibTest.CampusTCPRoundBounded

open Netlib Packet Protocol
namespace M
export Check.CampusTCPModel (Input Event Report State Step Trace)
end M
namespace T
export NetlibTest.CampusTCPRoundTheorem (verify ordinary cleanServices native setup_environment)
end T
namespace S
export Check.CampusTCPRoundServiceBound (actions check)
end S

private def load : Except String α → IO α
  | .ok value => pure value
  | .error reason => throw (IO.userError reason)

variable {input : M.Input} {startupEvents preparedEvents : List M.Event} {final : M.State input}

def check (startup : M.Report input startupEvents) (supported : startup.supported = true)
    (finished : startup.remaining = []) (config : Check.CampusTCPRoundMonitor.Config)
    (prepared : M.Report input preparedEvents) (setupSteps : List (M.Step input))
    (setupTrace : M.Trace input startup.final (Check.CampusTCPRoundSetup.setupEvents config.bytes)
      setupSteps prepared.final [])
    (steps : List (M.Step input)) (trace : M.Trace input prepared.final (steps.map (·.event)) steps final [])
    (bound : Nat)
    (allowed : S.actions config prepared.final Check.CampusTCPRoundMonitor.Monitor.initial steps = true)
    (service : S.check config prepared.final Check.CampusTCPRoundMonitor.Monitor.initial steps bound = true)
    (enough : 9 * bound ≤ steps.length) : IO Unit := do
  match connection : startup.final.connection with
  | .startup .. => throw (IO.userError "The bounded initial prefix must complete startup.")
  | .recovering .. => throw (IO.userError "The ordinary test prefix entered recovery.")
  | .application complete endpoints =>
    let clientEmpty ← load (T.verify (endpoints.client.steps = []) "The bounded initial client has prior operations.")
    let serverEmpty ← load (T.verify (endpoints.server.steps = []) "The bounded initial server has prior operations.")
    have initialConnection : startup.final.connection =
        .application complete (Check.CampusTCPModel.Applications.initial complete) := by
      rw [connection, Check.CampusTCPRoundSetup.applications_initial endpoints clientEmpty.property serverEmpty.property]
    let ordinary ← load (T.ordinary startup)
    let clean ← load (T.cleanServices startup complete ordinary)
    let nonempty ← load (T.verify (config.bytes ≠ []) "The bounded request must contain bytes.")
    let pending ← load (T.verify (config.bytes.length ≤ input.active.pendingLimit) "The bounded request exceeds pending storage.")
    let mss ← load (T.verify (config.bytes.length ≤ TCP.Handshake.effectiveMSS input.active (TCP.Handshake.receiveOffer input.passive))
      "The bounded request exceeds learned MSS.")
    let window ← load (T.verify (config.bytes.length ≤ input.passive.capacity) "The bounded request exceeds the peer window.")
    let request : Check.CampusTCPRoundStart.Request input :=
      ⟨config.bytes, nonempty.property, pending.property, mss.property, window.property⟩
    let before := Check.CampusTCPModel.beforeService input startup.final .primary
    match records : before.tracker.records with
    | [⟨entry, true⟩] =>
      let original ← load (T.native (input.contextFor .primary) before config.clientIngress entry .original "server")
      let reply ← load (T.native (input.contextFor .primary) before config.serverIngress entry .reply "client")
      let client ← load (T.verify (startup.final.owner .client = .primary) "The bounded client route must use primary.")
      let server ← load (T.verify (startup.final.owner .server = .primary) "The bounded server route must use primary.")
      let unpaused ← load (T.verify (startup.final.assignmentPaused = false) "The bounded initial gateway is paused.")
      let unsealed ← load (T.verify (startup.final.primarySealed = false) "The bounded initial gateway is sealed.")
      let unfenced ← load (T.verify (startup.final.primaryFenced = false) "The bounded initial gateway is fenced.")
      have actualRead : ∃ actual ∈ steps.take (9 * bound),
          actual.event = .read .server config.bytes.length ∧ actual.result.read = config.bytes := by
        obtain ⟨initial⟩ := Check.CampusTCPRoundStart.Initial.prepareOrdinary ordinary initialConnection
          (clean.property (Check.CampusTCPRoundStart.historyOfOrdinary ordinary complete initialConnection))
          supported finished request
        have current : initial.beforeService = before := Check.CampusTCPRoundLocal.setup_service initial.start .primary
        have selected := initial.records
        change initial.beforeService.tracker.records = [⟨initial.entry, true⟩] at selected
        rw [current, records] at selected
        have entryEq : initial.entry = entry :=
          (congrArg ConntrackLifecycle.Record.entry (List.cons.inj selected).1).symm
        have fixed := T.setup_environment initial.start
        have owners := congrArg Check.CampusTCPRoundEnvironment.Environment.owners fixed
        have paused := congrArg Check.CampusTCPRoundEnvironment.Environment.assignmentPaused fixed
        have sealed := congrArg Check.CampusTCPRoundEnvironment.Environment.primarySealed fixed
        have fenced := congrArg Check.CampusTCPRoundEnvironment.Environment.primaryFenced fixed
        change startup.final.owners = initial.state.owners at owners
        let env : Check.CampusTCPRoundStart.NativeEnv initial := {
          dataIngress := config.clientIngress, ackIngress := config.serverIngress
          original := by rw [current, entryEq]; exact original
          reply := by rw [current, entryEq]; exact reply
          clientOwner := by simpa only [Check.CampusTCPModel.State.owner, ← owners] using client.property
          serverOwner := by simpa only [Check.CampusTCPModel.State.owner, ← owners] using server.property
          unpaused := paused.symm.trans unpaused.property
          unsealed := sealed.symm.trans unsealed.property
          unfenced := fenced.symm.trans unfenced.property
          configured := rfl }
        have sameConfig : Check.CampusTCPRoundPhaseBase.config initial env = config := by cases config; rfl
        have stateEq : initial.state = prepared.final :=
          Check.CampusTCPRoundReport.Trace.final_unique initial.start.suffix setupTrace
        have actualTrace : M.Trace input initial.state (steps.map (·.event)) steps final [] := by
          rw [stateEq]
          exact trace
        exact Check.CampusTCPRoundBounded.read_by_checked (initial := initial) (native := env) actualTrace
          (by rw [sameConfig, stateEq]; exact allowed)
          (by rw [sameConfig, stateEq]; exact service) enough
      let _ := actualRead
      IO.println s!"Bounded TCP theorem applied to {steps.length} actual slots with bound {bound}."
    | _ => throw (IO.userError "The bounded initial prefix must retain one confirmed binding that has seen a reply.")

end NetlibTest.CampusTCPRoundBounded
