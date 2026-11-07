import Netlib.Check.FederatedPacketCompletion
import Netlib.Check.FederatedPacketReplayEvidence
import Netlib.Check.FederatedPacketSafety
import NetlibTest.FederatedPacketFixture

namespace NetlibTest.FederatedPacket

open Netlib Federation InFlight

variable {bundle : Bundle}

theorem arbitrary_history (certificate : Certified input profile) (header : Packet.Header)
    (accepted : certificate.context.first.selector.accepts header = true)
    (trace : (Execution.system certificate.context header).Trace (initialState certificate.context) events after) :
    Safety.CommonHistory certificate.context header events after :=
  Safety.common_history certificate.valid header accepted trace

theorem arbitrary_prefix (certificate : Certified input profile) (header : Packet.Header)
    (accepted : certificate.context.first.selector.accepts header = true)
    (trace : (Execution.system certificate.context header).Trace (initialState certificate.context) (prior ++ later) after) :
    ∃ middle, (Execution.system certificate.context header).Trace (initialState certificate.context) prior middle ∧
      (Execution.system certificate.context header).Trace middle later after ∧
      Safety.CommonHistory certificate.context header prior middle :=
  Safety.prefix_history certificate.valid header accepted trace

theorem arbitrary_isolation (certificate : Certified input profile) (header : Packet.Header)
    (accepted : certificate.context.first.selector.accepts header = true)
    (trace : (Execution.system certificate.context header).Trace (initialState certificate.context) events after)
    (query : Query) (member : query ∈ input.intent.queries) (kind : query.kind = .isolate)
    (sameCase : query.caseID = certificate.context.query.caseID) (sameSource : query.source = certificate.context.query.source) :
    Safety.publicPosition certificate.context after ≠ query.target :=
  Safety.isolate certificate.valid header accepted trace query member kind sameCase sameSource

theorem arbitrary_side_mediation (certificate : Certified input profile) (header : Packet.Header)
    (accepted : certificate.context.first.selector.accepts header = true)
    (trace : (Execution.system certificate.context header).Trace (initialState certificate.context) events after)
    (query : Query) (member : query ∈ input.intent.queries) (kind : query.kind = .mediated)
    (sameCase : query.caseID = certificate.context.query.caseID) (sameSource : query.source = certificate.context.query.source)
    (reached : Safety.publicPosition certificate.context after = query.target) (side : Side)
    (sameSide : query.gateways.all (fun gateway => decide (gateway.side = side)) = true) :
    Nonempty (Safety.PEPVisit certificate.context header events after query side) :=
  Safety.mediated_on certificate.valid header accepted trace query member kind sameCase sameSource reached side sameSide

private def loadValue : Except String α → IO α
  | .ok value => pure value
  | .error reason => throw (IO.userError reason)

private def ensure (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def rejects (result : Except String α) (expected : List String) : IO Unit :=
  match result with
  | .ok _ => throw (IO.userError "An invalid raw packet execution unexpectedly certified.")
  | .error reason => ensure (expected.all (fun item => reason.contains item)) s!"Unexpected packet rejection: {reason}"

private def replace (actions : List Action) (index : Nat) (action : Action) : List Action :=
  actions.take index ++ [action] ++ actions.drop (index + 1)

def withIdles (actions : List Action) : List Action :=
  actions.flatMap fun action => [.idle, match action with
    | .arrive observed index => .arrive observed (2 * index + 1)
    | other => other]

private def shifted (offset : Nat) (actions : List Action) : List Action :=
  actions.map fun action => match action with
    | .arrive observed index => .arrive observed (index + offset)
    | other => other

private def verifyEnabled (value : CheckedBundle bundle) : IO Unit := do
  let execution := value.execution
  let cell := value.certificate.cellAt bundle.header execution.accepted
  let mut positiveCuts := 0
  for member : slot in List.range (execution.report.prefix.length + 1) do
    have within : slot ≤ execution.report.prefix.length := by have := List.mem_range.mp member; omega
    let state := execution.report.prefix.state slot
    if positive : 0 < Progress.rank cell state then
      let _ := execution.enabled_at slot within positive
      let some move := Progress.pending cell state
        | throw (IO.userError "A positive actual cut has no current packet demand.")
      let advanced ← loadValue (Execution.advance value.certificate.context bundle.header state
        (canonicalAction value.certificate.context bundle.header state move))
      ensure (Progress.serves move advanced.event && Progress.rank cell advanced.outcome.after < Progress.rank cell state)
        "The current demand must have an actual supported action with decreasing rank."
      positiveCuts := positiveCuts + 1
  ensure (positiveCuts == execution.completion) "The complete recorded prefix must retain every positive cut through its terminal check."

private def verifyOldSend (value : CheckedBundle bundle)
    (within : 7 ≤ value.execution.report.steps.length) : IO Unit := do
  let report := value.execution.report
  let state := report.prefix.state 7
  match flight : state.phase with
  | .flight stamp =>
    ensure (state.current.1.val == 2 && stamp.current.1.val == 1 && stamp.sendIndex == 5 &&
        stamp.source == .inl "old-relay" && stamp.target == .inl "egress" &&
        Control.nativeEdge value.certificate.context bundle.header stamp.current stamp.source stamp.target &&
        !Control.nativeEdge value.certificate.context bundle.header state.current stamp.source stamp.target)
      "The pending flight must retain its real old sender revision after that sender has retired."
    let _ := report.flight_source 7 within stamp flight
    have rawSource : ∃ observation, bundle.actions[stamp.sendIndex]? = some (.send observation stamp.target) := by
      obtain ⟨origin⟩ := (report.flight_source 7 within stamp flight).1
      exact ⟨origin.observation, origin.raw_action⟩
    have sourceNative : Nonempty (Provenance.Origin bundle.deployment.left.contract bundle.deployment.right.contract
        (bundle.deployment.left.revisionAt stamp.current.1) (bundle.deployment.right.revisionAt stamp.current.2)
        value.certificate.context.first value.certificate.context.second bundle.deployment.intent bundle.header stamp.source stamp.target) := by
      obtain ⟨origin⟩ := (report.flight_source 7 within stamp flight).1
      exact origin.native_source value.certificate.deployment
    let _ := rawSource
    let _ := sourceNative
    ensure ((report.prefix.state 8).phase == .held (.inl "egress"))
      "Arrival must consume the earlier send even after its native source route disappears."
    match found : report.steps[7]? with
    | none => throw (IO.userError "The recorded old-relay arrival row is absent.")
    | some step =>
      match action : step.action with
      | .arrive observed sendIndex =>
        let _ := report.arrival_source 7 step found action
        ensure (sendIndex == 5 && observed.node == .inl "egress" && step.event.effect == .arrived stamp)
          "The actual arrival row must retain the exact send stamp and its original raw index."
      | _ => throw (IO.userError "The stored old-relay arrival row has another action.")
  | _ => throw (IO.userError "The retirement cut must retain the old relay flight.")

private def verifyShape (value : CheckedBundle bundle) (completion length : Nat) : IO Unit := do
  let execution := value.execution
  let cell := value.certificate.cellAt bundle.header execution.accepted
  ensure (execution.completion == completion && execution.report.steps.length == length &&
      Progress.deadline cell bundle.serviceBound == 228 &&
      execution.report.steps.map Replay.Step.action == bundle.actions &&
      value.certificate.cells.length == 3 &&
      value.certificate.totalWork + Completion.replayWork value.certificate.context bundle.actions bundle.serviceBound ≤ bundle.profile.work)
    "The public result must retain the literal replay, all three cells, first completion, and one aggregate budget."
  ensure (finished execution.report.final.key) "The recorded final state must include packet receipt and both complete plans."
  let _ := execution.report.trace
  match delivered : execution.report.final.phase with
  | .delivered index =>
    have actual : (execution.report.prefix.state execution.report.steps.length).phase = .delivered index := by
      change (execution.report.prefix.state execution.report.prefix.length).phase = _
      rw [execution.report.final_state]
      exact delivered
    have rawReceipt : ∃ observation, bundle.actions[index]? = some (.receive observation) := by
      obtain ⟨origin⟩ := (execution.report.delivered_source execution.report.steps.length (Nat.le_refl _) index actual).1
      exact ⟨origin.observation, origin.raw_action⟩
    let _ := rawReceipt
    ensure (index + 1 == completion) "The fixture's first completion must follow its actual receive action."
  | _ => throw (IO.userError "The completed report must retain its actual receive index.")
  verifyEnabled value

private def verifySafety (value : CheckedBundle bundle) : IO Unit := do
  let execution := value.execution
  let certificate := value.certificate
  let _ := arbitrary_history certificate bundle.header execution.accepted execution.report.trace
  let mut mediated := 0
  let mut isolated := 0
  for member : query in bundle.deployment.intent.queries do
    if sameCase : query.caseID = certificate.context.query.caseID then
      if sameSource : query.source = certificate.context.query.source then
        if kind : query.kind = .isolate then
          let _ := Safety.isolate certificate.valid bundle.header execution.accepted execution.report.trace
            query member kind sameCase sameSource
          ensure (Safety.publicPosition certificate.context execution.report.final != query.target)
            "The recorded packet must remain outside the isolated management endpoint."
          isolated := isolated + 1
        if kind : query.kind = .mediated then
          if reached : Safety.publicPosition certificate.context execution.report.final = query.target then
            for side in [Side.left, Side.right] do
              if sameSide : query.gateways.all (fun gateway => decide (gateway.side = side)) = true then
                let _ := arbitrary_side_mediation certificate bundle.header execution.accepted execution.report.trace
                  query member kind sameCase sameSource reached side sameSide
                mediated := mediated + 1
          else throw (IO.userError "The completed packet must reach the mediated query target.")
      else throw (IO.userError "The fixture's safety query has a different source.")
    else throw (IO.userError "The fixture's safety query has a different packet case.")
  ensure (mediated == 2 && isolated == 1) "Both operators' PEP queries and management isolation must apply to this same packet history."
  let left := execution.report.prefix.state 2
  let right := execution.report.prefix.state 12
  ensure (left.phase == .held (.inl "gateway") && right.phase == .held (.inr "gateway") &&
      ((bundle.deployment.left.revisionAt left.current.1).snapshot.intent.select
        (bundle.deployment.left.revisionAt left.current.1).snapshot.intent.enforcement).contains "gateway" &&
      ((bundle.deployment.right.revisionAt right.current.2).snapshot.intent.select
        (bundle.deployment.right.revisionAt right.current.2).snapshot.intent.enforcement).contains "gateway")
    "The actual no-idle history must hold the packet at both native enforcement nodes at their own epochs."

private def verifyTruncation (value : CheckedBundle bundle) : IO Unit := do
  let actions := bundle.actions.take 4
  let report ← loadValue (Replay.run value.certificate.context bundle.header actions)
  let cell := value.certificate.cellAt bundle.header value.execution.accepted
  ensure (Theory.BoundedServiceCheck.check report.prefix.length
      (fun slot => Progress.pending cell (report.prefix.state slot)) report.prefix.action Progress.serves bundle.serviceBound)
    "The short pending suffix must expose the incomplete-window service case."
  ensure ((Completion.cut? report).isNone) "A short pending trace cannot contain a recorded completion."
  let state := report.prefix.state report.prefix.length
  if positive : 0 < Progress.rank cell state then
    let _ := Progress.current_enabled value.certificate.valid cell report.prefix report.initial
      report.prefix.length (Nat.le_refl _) positive
    let some move := Progress.pending cell state | throw (IO.userError "The truncated terminal cut has no demand.")
    let _ ← loadValue (Execution.advance value.certificate.context bundle.header state
      (canonicalAction value.certificate.context bundle.header state move))
    pure ()
  else throw (IO.userError "The truncated replay must end with positive rank.")
  rejects (checkExecution value.certificate bundle.header actions bundle.serviceBound) ["no recorded completion"]

private def verifyObservations (value : CheckedBundle bundle) : IO Unit := do
  let some (Action.send first target) := bundle.actions[0]? | throw (IO.userError "The first send is absent.")
  let some (Action.arrive arriving index) := bundle.actions[4]? | throw (IO.userError "The old-relay arrival is absent.")
  let check := fun actions => checkExecution value.certificate bundle.header actions bundle.serviceBound
  rejects (check (replace bundle.actions 0 (.send { first with packetID := "forged-packet" } target))) ["slot 0", "observation"]
  rejects (check (replace bundle.actions 0 (.send { first with header := { first.header with sourcePort := 52001 } } target)))
    ["slot 0", "observation"]
  rejects (check (replace bundle.actions 0 (.send { first with node := .inr "ingress" } target))) ["slot 0", "observation"]
  rejects (check (replace bundle.actions 0 (.send first (.inl "old-relay")))) ["slot 0", "not currently enabled"]
  rejects (check (replace bundle.actions 4 (.arrive arriving 0))) ["slot 4", "observation"]
  rejects (check (replace bundle.actions 4 (.arrive arriving (index + 100)))) ["slot 4", "observation"]
  rejects (check (replace bundle.actions 4 (.arrive { arriving with packetID := "other-packet" } index)))
    ["slot 4", "observation"]
  rejects (check (replace bundle.actions 4 (.arrive { arriving with node := .inl "management" } index)))
    ["slot 4", "observation"]
  let some arrival := bundle.actions[1]? | throw (IO.userError "The first arrival is absent.")
  rejects (check (bundle.actions.take 2 ++ [arrival] ++ bundle.actions.drop 2)) ["slot 2", "observation"]
  rejects (check (replace bundle.actions 3 (.updateLeft 1))) ["slot 3", "not currently enabled"]
  rejects (check (bundle.actions.take 16 ++ bundle.actions.drop 17)) ["no recorded completion"]
  rejects (checkExecution value.certificate bundle.header bundle.actions 0) ["positive"]
  rejects (checkExecution value.certificate { bundle.header with destinationPort := 22 } bundle.actions bundle.serviceBound)
    ["outside the certified class"]
  let starved := List.replicate 12 Action.idle ++ shifted 12 bundle.actions
  rejects (check starved) ["persistent-demand service bound"]

private def verifyPostReceiptUpdate (bundle : Bundle) : IO Unit := do
  let some (Action.updateRight 1) := bundle.actions[16]?
    | throw (IO.userError "The final provider update is absent.")
  let actions := bundle.actions.take 16 ++ bundle.actions.drop 17 ++ [.updateRight 1]
  let delayed := { bundle with actions }
  let value ← loadValue (checkBundle delayed)
  let execution := value.execution
  let cell := value.certificate.cellAt delayed.header execution.accepted
  let state := execution.report.prefix.state 18
  ensure (execution.completion == 19 && execution.report.steps.length == 19 &&
      state.phase == .delivered 17 && state.current.2.val == 1 && !finished state.key &&
      (Control.occupied state.phase.key).isNone && Progress.deadline cell delayed.serviceBound == 228)
    "Receipt must clear the reservation while the final provider update still prevents completion."
  if unfinished : finished state.key = false then
    have notComplete : ¬Progress.Complete state := by
      intro done
      have opposite := (Progress.finished_iff state).mpr done
      rw [unfinished] at opposite
      cases opposite
    let _ := notComplete
  else throw (IO.userError "The delivered packet must still have an unfinished local plan.")
  if within : 18 ≤ execution.report.prefix.length then
    if positive : 0 < Progress.rank cell state then
      let _ := execution.enabled_at 18 within positive
      let some move := Progress.pending cell state | throw (IO.userError "The post-receipt update demand is absent.")
      ensure (move == .updateRight 1) "The remaining demand must select the actual final provider update."
      let advanced ← loadValue (Execution.advance value.certificate.context delayed.header state
        (canonicalAction value.certificate.context delayed.header state move))
      ensure (advanced.event.action == .updateRight 1 && advanced.outcome.after.phase == .delivered 17 &&
          advanced.outcome.after.current.2.val == 2 && finished advanced.outcome.after.key &&
          Progress.serves move advanced.event && Progress.rank cell advanced.outcome.after < Progress.rank cell state)
        "The real supported update must finish the plans while retaining the earlier receipt."
    else throw (IO.userError "A delivered packet with a pending update must retain positive rank.")
  else throw (IO.userError "The post-receipt cut must be part of the actual report.")
  ensure (finished execution.report.final.key) "The recorded post-receipt update must establish final completion."

private def verifyRaw (json : Lean.Json) : IO Unit := do
  rejects (InFlight.checkJson ((json.setObjVal! "scope" (.str "unsupported-packet-scope")).compress)) ["Unsupported packet"]
  rejects (InFlight.checkJson ((json.setObjVal! "unknown" (.bool true)).compress)) ["Unknown"]
  rejects (InFlight.checkJson ("{\"schema\":1," ++ (json.compress.drop 1).toString)) ["Duplicate"]
  let deployment ← loadValue (json.getObjVal? "deployment")
  let left ← loadValue (deployment.getObjVal? "left")
  let initial ← loadValue (left.getObjVal? "initial")
  let snapshot ← loadValue (initial.getObjVal? "snapshot")
  let bad := json.setObjVal! "deployment" (deployment.setObjVal! "left" (left.setObjVal! "initial"
    (initial.setObjVal! "snapshot" (snapshot.setObjVal! "scope" (.str "unsupported-native-scope")))))
  rejects (InFlight.checkJson bad.compress) ["scope"]
  rejects (InFlight.checkJson (← loadValue (FederatedPacketFixture.removedReceiver json)).compress)
    ["slot 3", "not currently enabled"]
  rejects (InFlight.checkJson (← loadValue (FederatedPacketFixture.projectionJump json)).compress)
    ["slot 3", "not currently enabled"]
  rejects (InFlight.checkJson (← loadValue (FederatedPacketFixture.strandedHeader json)).compress) ["dead end"]
  rejects (InFlight.checkJson (← loadValue (FederatedPacketFixture.drainingCycle json)).compress) ["dead end"]

def run : IO Unit := do
  let text ← IO.FS.readFile FederatedPacketFixture.file
  let ⟨bundle, checked⟩ ← loadValue (InFlight.checkJson text)
  verifyShape checked 19 19
  verifySafety checked
  if within : 7 ≤ checked.execution.report.steps.length then verifyOldSend checked within
  else throw (IO.userError "The checked report is too short for the retirement regression.")
  verifyTruncation checked
  verifyObservations checked
  let idleBundle := { bundle with actions := withIdles bundle.actions }
  let idleChecked ← loadValue (checkBundle idleBundle)
  verifyShape idleChecked 38 38
  verifyPostReceiptUpdate bundle
  rejects (checkBundle { bundle with serviceBound := 0 }) ["positive"]
  rejects (certify bundle.deployment { bundle.profile with cells := 0 }) ["Selected packet classes"]
  rejects (certify bundle.deployment { bundle.profile with work := 0 }) ["Raw packet context"]
  rejects (certify { bundle.deployment with work := 0 } bundle.profile) ["budget 0"]
  let tightProfile := { bundle.profile with work := checked.certificate.totalWork, cells := 3 }
  let tight ← loadValue (certify bundle.deployment tightProfile)
  ensure (tight.cells.length == 3) "A selected-cell budget of three must cover the full traffic class despite 324 Cartesian cells."
  rejects (checkExecution tight bundle.header bundle.actions bundle.serviceBound) ["replay and class analysis"]
  verifyRaw (← FederatedPacketFixture.raw)
  IO.println "Public packet checks: literal observations, old-send origins, bounded idles, finite completion, semantic negatives, and shared budgets."

end NetlibTest.FederatedPacket
