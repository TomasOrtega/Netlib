import Netlib.Check.FederatedCohortCompletion
import Netlib.Check.FederatedCohortCheckedFacts
import NetlibTest.FederatedCohortFixture

namespace NetlibTest.FederatedCohort

open Netlib Federation

variable {bundle : Cohort.Bundle}

theorem all_headers_history (certificate : Cohort.Certified input profile)
    (headers : Vector Packet.Header certificate.prepared.size) (accepted : Cohort.Accepted certificate.prepared.context headers)
    {events : List (Cohort.Event input certificate.prepared.size)} {after : Cohort.State input certificate.prepared.size}
    (trace : (Cohort.Execution.system certificate.prepared.context headers).Trace
      (Cohort.initialState certificate.prepared.context) events after) (index : Fin certificate.prepared.size) :
    Cohort.Safety.CommonHistory certificate.prepared.context headers index events after :=
  certificate.common_history headers accepted trace index

private def loadValue : Except String α → IO α
  | .ok value => pure value
  | .error reason => throw (IO.userError reason)

private def ensure (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def rejects (value : Except String α) (words : List String) : IO Unit :=
  match value with
  | .ok _ => throw (IO.userError "An invalid finite cohort unexpectedly certified.")
  | .error reason => ensure (words.all (fun word => reason.contains word)) s!"Unexpected cohort rejection: {reason}"

private def factorial : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * factorial n

/-- Admission uses the finite phase and FIFO-order ceiling for the supplied input. -/
def limits (data : FederatedCohortFixture.Data) (classes : Nat) : Cohort.Limits :=
  let count := data.packets.length
  let nodes := (InFlight.Control.nodes data.input).length
  let states := data.input.left.versions.length * data.input.right.versions.length *
    (2 * nodes + 1) ^ count * factorial count
  let candidates := count * (nodes + 2) + 3
  let rows := (data.input.left.versions ++ data.input.right.versions).foldl
      (fun total revision => total + 1 + Native.nativeRows revision + revision.projection.length + revision.anchors.length) 0 +
    data.input.intent.borders.foldl (fun total border => total + 1 + border.cases.length) 0 +
    data.packets.foldl (fun total packet => total +
      packet.profile.leftFences.foldl (fun total names => total + 1 + names.length) 0 +
      packet.profile.rightFences.foldl (fun total names => total + 1 + names.length) 0) 0 + 1
  let costs : Theory.FiniteSuccessorGraph.Costs := ⟨candidates * (rows + 1) ^ 2 * (nodes + count + 1) ^ 2, nodes + count + 1⟩
  let edges := states * candidates
  let graphWork := Theory.FiniteSuccessorGraph.workEstimate costs states edges
  let zero : Cohort.Limits := ⟨0, 0, 0, 0⟩
  let admission := Deployment.workEstimate data.input + Cohort.rawWork data.input (data.profile zero) +
    (data.packets.map (·.profile.work)).sum
  let singleUniverse := data.input.left.versions.length * data.input.right.versions.length * (2 * nodes + 1)
  let signatureRows := (data.packets.map (·.profile.cells)).sum * singleUniverse * (nodes + 6)
  let comparisons := (classes + 1) ^ 2 * (signatureRows + 1) * (nodes + count + 1)
  let slots := 3 * data.actions.length + data.serviceBound + 1
  let replay := slots ^ 2 * (min data.serviceBound slots + 1) *
    (costs.row + classes * states * (costs.key + 1) + count + slots + 1)
  ⟨classes, states, edges, admission + (classes + 1) * (count + 1) + comparisons + classes * graphWork + replay⟩

private def replace (actions : List InFlight.Action) (index : Nat) (action : InFlight.Action) : List InFlight.Action :=
  actions.take index ++ [action] ++ actions.drop (index + 1)

private def headers (value : Cohort.CheckedBundle bundle) : Vector Packet.Header value.certificate.prepared.size :=
  Theory.FiniteProduct.vector bundle.headers value.headerCount

private def verifyEnabled (value : Cohort.CheckedBundle bundle) : IO Unit := do
  let execution := value.execution
  let actual := headers value
  let context := value.certificate.prepared.context
  let cell := value.certificate.cellAt actual execution.accepted
  for member : slot in List.range (execution.report.prefix.length + 1) do
    have within : slot ≤ execution.report.prefix.length := by have := List.mem_range.mp member; omega
    let state := execution.report.prefix.state slot
    let _ := execution.valid_at slot within
    for present : node in InFlight.Control.nodes bundle.input do
      let _ := execution.capacity_at slot within node present
      pure ()
    for index in List.finRange value.certificate.prepared.size do
      let _ := execution.history_at slot within index
      pure ()
    if positive : 0 < Cohort.Progress.rank cell.checked state then
      let _ := execution.enabled_at slot within positive
      let some move := Cohort.Progress.pending cell.checked state | throw (IO.userError "A positive cohort cut has no demand.")
      let advanced ← loadValue (Cohort.Execution.advance context actual state (Cohort.canonicalAction context actual state move))
      ensure (Cohort.Progress.serves context move advanced.event &&
          Cohort.Progress.rank cell.checked advanced.outcome.after < Cohort.Progress.rank cell.checked state)
        "Each positive cut must have an actual supported action for the exact joint demand."

private def verifyPositive (value : Cohort.CheckedBundle bundle) : IO Unit := do
  let execution := value.execution
  let context := value.certificate.prepared.context
  let actual := headers value
  ensure (execution.completion == 34 && execution.report.steps.length == 34 && value.certificate.cells.length == 9 &&
      execution.report.steps.map Cohort.Replay.Step.action == bundle.actions && Cohort.finished execution.report.final.key)
    "The closed raw result must retain every literal slot, independent tuple, and actual whole-group completion."
  ensure (Cohort.Control.reservations (execution.report.prefix.state 2).key (.inl "gateway") == 2 &&
      (Cohort.queueAt (execution.report.prefix.state 2).queues (.inl "gateway")).isEmpty)
    "Both sends must reserve capacity before either gateway arrival."
  ensure ((Cohort.queueAt (execution.report.prefix.state 4).queues (.inl "gateway")).map Fin.val == [0, 1])
    "The gateway FIFO must retain actual arrival order."
  rejects (Cohort.Execution.advance context actual (execution.report.prefix.state 6) (.updateLeft 1)) ["not currently enabled"]
  rejects (Cohort.Execution.advance context actual (execution.report.prefix.state 9) (.updateLeft 1)) ["not currently enabled"]
  ensure (Cohort.Control.good context (execution.report.prefix.state 22).key &&
      !Cohort.finished (execution.report.prefix.state 22).key)
    "One packet's receipt must not complete a group whose other packet is still draining."
  for index in List.finRange value.certificate.prepared.size do
    let component := (execution.report.prefix.state 34).packet index
    let _ := execution.common_history index
    let _ := execution.receipt_origin index
    match component.phase with
    | .delivered received => ensure (received == 21 || received == 33) "Each packet must retain its own actual receipt slot."
    | _ => throw (IO.userError "A packet is unresolved at whole-group completion.")
  let _ := execution.report.trace
  verifyEnabled value

private def verifyHistories (value : Cohort.CheckedBundle bundle) : IO Unit := do
  let execution := value.execution
  let context := value.certificate.prepared.context
  let mut mediated := 0
  let mut isolated := 0
  for index in List.finRange value.certificate.prepared.size do
    let packet := context.packets.get index
    for member : query in bundle.input.intent.queries do
      if sameCase : query.caseID = packet.query.caseID then
        if sameSource : query.source = packet.query.source then
          if kind : query.kind = .isolate then
            let _ := execution.isolate_at execution.report.prefix.length (Nat.le_refl _) index query member kind sameCase sameSource
            isolated := isolated + 1
          if kind : query.kind = .mediated then
            if reached : InFlight.Safety.publicPosition packet
                ((execution.report.prefix.state execution.report.prefix.length).packet index) = query.target then
              for side in [Side.left, Side.right] do
                if sameSide : query.gateways.all (fun reference => decide (reference.side = side)) = true then
                  let _ := execution.mediated_on execution.report.prefix.length (Nat.le_refl _) index
                    query member kind sameCase sameSource reached side sameSide
                  mediated := mediated + 1
            else throw (IO.userError "The completed packet did not reach its matched mediated target.")
    if within : 20 ≤ execution.report.prefix.length then
      match flight : ((execution.report.prefix.state 20).packet index).phase with
      | .flight stamp =>
        ensure (stamp.sendIndex == 18 && stamp.current.2.val == 1 &&
            (execution.report.prefix.state 20).current.2.val == 2 && stamp.source == .inr "old-relay" &&
            !InFlight.Control.nativeEdge packet ((headers value).get index)
              (execution.report.prefix.state 20).current stamp.source stamp.target)
          "The old sender must remain in the stamp after provider retirement removes its current edge."
        have rawSource : ∃ origin : Cohort.Replay.SendOrigin execution.report index stamp,
            bundle.actions[stamp.sendIndex]? = some (.send origin.projected.observation stamp.target) := by
          obtain ⟨origin⟩ := (execution.flight_source 20 within index stamp flight).1
          let _ := execution.native_source index stamp origin
          exact ⟨origin, origin.raw_action⟩
        let _ := rawSource
      | _ => pure ()
    else throw (IO.userError "The actual cohort history is too short for its old-send witness.")
  ensure (mediated == 4 && isolated == 2) "Both identities need their own campus/provider PEP visits and management isolation."

private def verifyActions (value : Cohort.CheckedBundle bundle) : IO Unit := do
  let actual := headers value
  let check := fun actions => Cohort.checkExecution value.certificate actual actions bundle.serviceBound
  let some (InFlight.Action.send a target) := bundle.actions[0]? | throw (IO.userError "Packet A's send is absent.")
  let some bSend := bundle.actions[1]? | throw (IO.userError "Packet B's send is absent.")
  let some (InFlight.Action.arrive aArrival aIndex) := bundle.actions[2]? | throw (IO.userError "Packet A's arrival is absent.")
  rejects (check (replace bundle.actions 0 bSend)) ["slot 0", "not currently enabled"]
  rejects (check (replace bundle.actions 0 (.send { a with packetID := "unknown" } target))) ["outside the cohort"]
  rejects (check (replace bundle.actions 0 (.send { a with header := { a.header with sourcePort := 52001 } } target))) ["component executions"]
  rejects (check (replace bundle.actions 2 (.arrive aArrival (aIndex + 99)))) ["slot 2", "component executions"]
  rejects (check (replace bundle.actions 2 (.arrive { aArrival with packetID := "packet-b" } aIndex))) ["slot 2", "component executions"]
  rejects (check (bundle.actions.take 3 ++ [.arrive aArrival aIndex] ++ bundle.actions.drop 3)) ["slot 3", "not currently enabled"]
  let some receipt := bundle.actions[21]? | throw (IO.userError "Packet B's receipt is absent.")
  rejects (check (bundle.actions ++ [receipt])) ["not currently enabled"]
  let short := bundle.actions.take 2
  let report ← loadValue (Cohort.Replay.run value.certificate.prepared.context actual short)
  let cell := value.certificate.cellAt actual value.execution.accepted
  ensure (Theory.BoundedServiceCheck.check report.prefix.length
      (fun slot => Cohort.Progress.pending cell.checked (report.prefix.state slot)) report.prefix.action
      (Cohort.Progress.serves value.certificate.prepared.context) bundle.serviceBound)
    "The short service suffix must expose vacuous incomplete windows."
  rejects (check short) ["no recorded whole-group completion"]
  let shifted := bundle.actions.map fun action => match action with
    | .arrive observed index => .arrive observed (index + 12)
    | other => other
  rejects (check (List.replicate 12 InFlight.Action.idle ++ shifted)) ["persistent-demand service bound"]
  rejects (Cohort.checkExecution value.certificate actual bundle.actions 0) ["positive"]
  rejects (check (List.replicate 1000 InFlight.Action.idle)) ["work budget"]
  let some first := bundle.headers.head? | throw (IO.userError "The first independent header is absent.")
  let same := Vector.ofFn (fun _ : Fin value.certificate.prepared.size => first)
  let sameActions := bundle.actions.map fun action => match action with
    | .send observed target => .send { observed with header := first } target
    | .arrive observed index => .arrive { observed with header := first } index
    | .receive observed => .receive { observed with header := first }
    | other => other
  let identical ← loadValue (Cohort.checkExecution value.certificate same sameActions bundle.serviceBound)
  ensure (identical.completion == 34) "Equal headers must retain two distinct identities through the same checked class product."

private def verifyGuards (value : Cohort.CheckedBundle bundle) : IO Unit := do
  let context := value.certificate.prepared.context
  let actual := headers value
  let initial := value.execution.report.prefix.state 0
  let some a := Cohort.packetIndex context "packet-a" | throw (IO.userError "Packet A is absent.")
  let some b := Cohort.packetIndex context "packet-b" | throw (IO.userError "Packet B is absent.")
  let malformed := { initial with queues := Cohort.putQueue initial.queues (.inl "ingress") [a, a, b] }
  rejects (Cohort.Execution.advance context actual malformed .idle) ["queues"]
  let capacities := Vector.ofFn fun index =>
    if Cohort.nodeAt bundle.input index = .inl "gateway" then 1 else context.capacities.get index
  let narrow : Cohort.Context bundle.input value.certificate.prepared.size := { context with capacities }
  let some secondSend := bundle.actions[1]? | throw (IO.userError "The second reserving send is absent.")
  rejects (Cohort.Execution.advance narrow actual (value.execution.report.prefix.state 1) secondSend) ["not currently enabled"]
  let tailProfile := { bundle.profile with packets := bundle.profile.packets.map fun packet =>
    if packet.packetID == "packet-b" then { packet with leftFences := ["gateway"] :: packet.leftFences.drop 1 } else packet }
  let prepared ← loadValue (Cohort.prepare bundle.input tailProfile)
  if count : bundle.headers.length = prepared.size then
    let tailHeaders := Theory.FiniteProduct.vector bundle.headers count
    let report ← loadValue (Cohort.Replay.run prepared.context tailHeaders (bundle.actions.take 4))
    let some head := Cohort.packetIndex prepared.context "packet-a" | throw (IO.userError "The queue head identity is absent.")
    ensure ((InFlight.Control.step (prepared.context.packets.get head) (tailHeaders.get head)
      (report.final.packet head).key (.updateLeft 0)).isSome)
      "The head packet must permit the update that the tail packet's extra fence forbids."
    rejects (Cohort.Execution.advance prepared.context tailHeaders report.final (.updateLeft 0)) ["not currently enabled"]
  else throw (IO.userError "Prepared tail-fence headers changed count.")

private def verifyRawAndBudgets (bundle : Cohort.Bundle) (json : Lean.Json) : IO Unit := do
  rejects (Cohort.checkBundle { bundle with headers := [] }) ["header count"]
  rejects (Cohort.checkBundle { bundle with serviceBound := 0 }) ["positive"]
  rejects (Cohort.certify bundle.input { bundle.profile with limits := { bundle.profile.limits with classes := 0 } }) ["class budget"]
  rejects (Cohort.certify bundle.input { bundle.profile with limits := { bundle.profile.limits with states := 0 } }) ["states"]
  rejects (Cohort.certify bundle.input { bundle.profile with limits := { bundle.profile.limits with edges := 0 } }) ["successors"]
  rejects (Cohort.certify bundle.input { bundle.profile with limits := { bundle.profile.limits with work := 0 } }) ["work budget"]
  rejects (Cohort.certify { bundle.input with work := 0 } bundle.profile) ["budget 0"]
  let some packet := bundle.profile.packets.head? | throw (IO.userError "The profile has no packet.")
  rejects (Cohort.certify bundle.input { bundle.profile with packets := [packet, packet] }) ["repeated packet ID"]
  rejects (Cohort.certify bundle.input { bundle.profile with capacities := bundle.profile.capacities.tail }) ["Capacity rows"]
  rejects (Cohort.Json.parse ((json.setObjVal! "scope" (.str "unsupported")).compress)) ["Unsupported"]
  rejects (Cohort.Json.parse ((json.setObjVal! "unknown" (.bool true)).compress)) ["Unknown"]
  rejects (Cohort.Json.parse ("{\"schema\":1," ++ (json.compress.drop 1).toString)) ["Duplicate"]

private def verifyDiagonalGraphs (data : FederatedCohortFixture.Data) : IO Unit := do
  let profile := data.profile (limits data 4)
  let prepared ← loadValue (Cohort.prepare data.input profile)
  let graphLimits : Theory.FiniteSuccessorGraph.Limits :=
    ⟨profile.limits.states, profile.limits.edges, profile.limits.work - prepared.totalWork⟩
  let mut passed := 0
  let mut spent := prepared.totalWork
  for member : tuple in prepared.headerTuples do
    match tuple.toList with
    | [first, second] =>
      if first.destination = second.destination then
        let checked ← loadValue (Cohort.Graph.check prepared.family tuple
          (prepared.headerTuple_accepted tuple member) prepared.initialGood graphLimits)
        spent := spent + checked.sparse.graph.work
        passed := passed + 1
    | _ => throw (IO.userError "The diagonal counterexample must retain its two independent packet identities.")
  ensure (passed == 2 && spent ≤ profile.limits.work)
    "Both complete diagonal graphs must certify before the full product exposes its hidden mixed-tuple deadlock."

def run : IO Unit := do
  let data ← FederatedCohortFixture.positive
  let resourceLimits := limits data 9
  let json ← FederatedCohortFixture.positiveJson resourceLimits
  let text ← IO.FS.readFile "examples/federation/packet-cohorts.json"
  let saved ← loadValue (Import.Json.parse text)
  ensure (saved.compress == json.compress)
    "The saved cohort example differs from the generated native fixture."
  let ⟨bundle, checked⟩ ← loadValue (Cohort.checkJson text)
  verifyPositive checked
  verifyHistories checked
  verifyActions checked
  verifyGuards checked
  verifyRawAndBudgets bundle json
  for count in [0, 3] do
    let data ← FederatedCohortFixture.zeroHop count
    let json ← FederatedCohortFixture.zeroHopJson count (limits data 1)
    let ⟨_, value⟩ ← loadValue (Cohort.checkJson json.compress)
    ensure (value.certificate.prepared.size == count && value.execution.completion == count)
      "Empty and three-ID singleton cohorts must use their actual size and recorded receive actions."
    verifyEnabled value
  let emptyData := { data with packets := [], actions := [.updateBoth 0 0, .updateBoth 1 1] }
  let emptyJson ← FederatedCohortFixture.emptyJson (limits emptyData 1)
  let ⟨emptyBundle, empty⟩ ← loadValue (Cohort.checkJson emptyJson.compress)
  let emptyCell := empty.certificate.cellAt (headers empty) empty.execution.accepted
  ensure (empty.certificate.prepared.size == 0 && empty.execution.completion == 2 &&
      empty.execution.report.steps.map Cohort.Replay.Step.action == [.updateBoth 0 0, .updateBoth 1 1] &&
      Cohort.Progress.rank emptyCell.checked (empty.execution.report.prefix.state 0) == 4 &&
      Cohort.Progress.deadline emptyCell.checked emptyBundle.serviceBound == 4 * emptyBundle.serviceBound)
    "An empty cohort must retain the unfinished-plan potential and complete only after both actual shared updates."
  verifyEnabled empty
  let deadlock ← FederatedCohortFixture.deadlock
  rejects (Cohort.checkJson (← FederatedCohortFixture.deadlockJson (limits deadlock 1)).compress) ["dead end"]
  let hidden ← FederatedCohortFixture.hiddenTuple
  verifyDiagonalGraphs hidden
  rejects (Cohort.checkJson (← FederatedCohortFixture.hiddenTupleJson (limits hidden 4)).compress) ["dead end"]
  let resource ← FederatedCohortFixture.resourceDeadlock
  rejects (Cohort.checkJson (← FederatedCohortFixture.resourceDeadlockJson (limits resource 1)).compress) ["dead end"]
  IO.println "Finite cohorts: complete independent classes, FIFO reservations, exact identities, update fences, and recorded completion."

end NetlibTest.FederatedCohort
