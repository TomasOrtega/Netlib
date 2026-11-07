import Netlib.Check.CampusTCP
import Netlib.Check.CampusTCPRoundReverse

namespace NetlibTest.CampusTCPRoundTheorem

open Netlib Packet Protocol
namespace M
export Check.CampusTCPModel (Input Event Report State Step Applications Connection Actor Receipt Served beforeService)
end M
namespace H
export Check.TCPHandshake (Step Completed)
end H
namespace O
export Check.CampusTCPStartupOrigins (Ordinary ReceiveAt)
end O
namespace R
export Check.CampusTCPRoundStart (Request Initial NativeEnv)
end R

variable {input : M.Input} {events : List M.Event} {report : M.Report input events}

private def load : Except String α → IO α
  | .ok value => pure value
  | .error reason => throw (IO.userError reason)

def verify (property : Prop) [Decidable property] (message : String) : Except String { _value : Unit // property } :=
  if accepted : property then .ok ⟨(), accepted⟩ else .error message

private structure Reference (steps : List (M.Step input)) where
  joint : M.Step input
  member : joint ∈ steps
  actual : H.Step input.active input.passive
  recorded : joint.result.startup = some actual

private def references : (steps : List (M.Step input)) → List (Reference steps)
  | [] => []
  | head :: tail =>
    let rest := (references tail).map (fun value =>
      (⟨value.joint, List.mem_cons_of_mem head value.member, value.actual, value.recorded⟩ : Reference (head :: tail)))
    match recorded : head.result.startup with
    | none => rest
    | some actual => ⟨head, List.mem_cons_self, actual, recorded⟩ :: rest

private theorem references_map (steps : List (M.Step input)) :
    (references steps).map (·.actual) = steps.filterMap (·.result.startup) := by
  induction steps with
  | nil => rfl
  | cons head tail ih =>
    unfold references
    split
    · rename_i absent
      simpa only [List.map_map, Function.comp_def, List.filterMap_cons, absent] using ih
    · rename_i actual present
      simpa only [List.map_cons, List.map_map, Function.comp_def, List.filterMap_cons, present] using
        congrArg (actual :: ·) ih

private def receiveAt (report : M.Report input events) (value : Reference report.steps) :
    Except String (O.ReceiveAt report value.actual) :=
  match event : value.joint.event with
  | .deliver index bytes policy => .ok ⟨value.joint, value.member, value.recorded, index, bytes, policy, event⟩
  | _ => .error "The selected startup record must be an actual delivery."

deriving instance DecidableEq for Check.TCPHandshake.Event

def ordinary (report : M.Report input events) : Except String (O.Ordinary report) := do
  match recorded : references report.steps with
  | [opened, syn, synAck, ack] =>
    let first ← receiveAt report syn
    let second ← receiveAt report synAck
    let third ← receiveAt report ack
    let synEvent ← verify (syn.actual.event = .listenSyn first.bytes .rewrite first.policy)
      "The first actual receipt must consume the SYN."
    let synAckEvent ← verify (synAck.actual.event = .synSentSynAck second.bytes .rewrite second.policy)
      "The second actual receipt must consume the SYNACK."
    let ackEvent ← verify (ack.actual.event = .synReceivedAck third.bytes .rewrite)
      "The third actual receipt must consume the final ACK."
    return ⟨opened.actual, syn.actual, synAck.actual, ack.actual, by
      have same := references_map report.steps
      rw [recorded] at same
      exact same.symm, first, second, third, synEvent.property, synAckEvent.property, ackEvent.property⟩
  | _ => throw "The initial prefix must contain exactly four stored startup operations."

private theorem service_member (report : M.Report input events) (joint : M.Step input)
    (member : joint ∈ report.steps) (served : M.Served input) (recorded : joint.result.service = some served) :
    served ∈ report.final.services := by
  rw [Check.CampusTCPPrimaryTransport.Report.services report]
  exact List.mem_filterMap.mpr ⟨joint, member, recorded⟩

private theorem service_time_unique (report : M.Report input events) (first second : M.Served input)
    (firstMember : first ∈ report.final.services) (secondMember : second ∈ report.final.services)
    (same : first.time = second.time) : first = second := by
  obtain ⟨a, am, presentA, timeA, _⟩ := Check.CampusTCPOrigins.Report.services_origin report first firstMember
  obtain ⟨b, bm, presentB, timeB, _⟩ := Check.CampusTCPOrigins.Report.services_origin report second secondMember
  have steps := Check.CampusTCPFacts.At.unique
    (⟨a, am, timeA.symm⟩ : Check.CampusTCPFacts.At report first.time)
    (⟨b, bm, timeB.symm.trans same.symm⟩ : Check.CampusTCPFacts.At report first.time)
  change a = b at steps
  rw [steps] at presentA
  exact Option.some.inj (presentA.symm.trans presentB)

private structure ReceiptPast (report : M.Report input events) (time : Nat) (canonical : M.Served input) where
  joint : M.Step input
  member : joint ∈ report.steps
  receipt : M.Receipt input
  recorded : joint.result.receipt = some receipt
  stamp : joint.before.time = time
  serviceTime : receipt.served.time = canonical.time

private def receiptPast (value : O.ReceiveAt report actual) (time : Nat) (canonical : M.Served input) :
    Except String (ReceiptPast report time canonical) := do
  match recorded : value.joint.result.receipt with
  | none => throw "The actual startup delivery has no stored receipt."
  | some receipt =>
    let stamp ← verify (value.joint.before.time = time) "The completed startup stamp differs from its actual receipt."
    let serviceTime ← verify (receipt.served.time = canonical.time) "The initial receipt names a different stored service."
    return ⟨value.joint, value.member, receipt, recorded, stamp.property, serviceTime.property⟩

private theorem canonical_service (delivery : Check.CampusTCPFacts.DeliveryAt report time actor)
    (past : ReceiptPast report time canonical) (member : canonical ∈ report.final.services)
    (service : Check.CampusTCPFacts.GatewayService delivery) : delivery.receipt.served = canonical := by
  have joint := delivery.joint.unique ⟨past.joint, past.member, past.stamp⟩
  change delivery.joint.step = past.joint at joint
  have recorded := delivery.recorded
  rw [joint] at recorded
  have receipts : delivery.receipt = past.receipt := Option.some.inj (recorded.symm.trans past.recorded)
  apply service_time_unique report delivery.receipt.served canonical
  · exact service_member report service.joint.step service.joint.member delivery.receipt.served service.present
  · exact member
  · rw [receipts]
    exact past.serviceTime

def cleanServices (report : M.Report input events) (complete : H.Completed input.active input.passive)
    (ordinary : O.Ordinary report) :
    Except String { _value : Unit // ∀ history : Check.CampusTCPFacts.StartupHistory report complete,
      Check.CampusTCPStartupTransport.CleanServices history } := do
  match stored : report.final.services with
  | [syn, synAck, ack] =>
    let first ← receiptPast ordinary.synAt complete.input.times.synReceived syn
    let second ← receiptPast ordinary.synAckAt complete.input.times.synAckReceived synAck
    let third ← receiptPast ordinary.ackAt complete.input.times.ackReceived ack
    let synPrimary ← verify (syn.ticket.value.gateway = .primary) "The initial SYN service must use primary."
    let synAckPrimary ← verify (synAck.ticket.value.gateway = .primary) "The initial SYNACK service must use primary."
    let ackPrimary ← verify (ack.ticket.value.gateway = .primary) "The initial ACK service must use primary."
    return ⟨(), by
      intro history
      have a := canonical_service history.syn.receive first (by rw [stored]; simp) history.syn.service
      have b := canonical_service history.synAck.receive second (by rw [stored]; simp) history.synAck.service
      have c := canonical_service history.ack.receive third (by rw [stored]; simp) history.ack.service
      constructor
      · rw [a, b, c, ← Check.CampusTCPPrimaryTransport.Report.services report]
        exact stored
      · rw [a]; exact synPrimary.property
      · rw [b]; exact synAckPrimary.property
      · rw [c]; exact ackPrimary.property⟩
  | _ => throw "The initial prefix must contain exactly three stored gateway services."

private def checks (context : Check.CampusTCPService.Context) (before : Check.CampusTCPService.Before)
    (ingress : IngressAttachment.InterfaceRef) : Except String (Check.CampusTCPService.Checks context before ingress) := do
  let bounded ← verify (before.after ≤ context.authentication.observations.length) "The initial authentication cut is out of range."
  let live ← verify (ingress ∈ before.live) "The initial ingress lifetime is not live."
  let namespaceEq ← verify (ingress.ns = context.executionNS) "The initial ingress uses a different namespace lifetime."
  match forwardComputed : Check.SessionInstallation.check context.authentication context.requirements before.after
      (Check.CampusTCPService.active context before) context.configs 100000 with
  | .error reason => throw reason
  | .ok forward =>
    match guardComputed : Check.IngressGuard.check (Check.CampusTCPService.current context before)
        context.executionNS before.attachments [] context.application before.guard 100000 with
    | .error reason => throw reason
    | .ok guard =>
      return ⟨bounded.property, live.property, namespaceEq.property, 100000, forward, forwardComputed,
        guard, guardComputed, Check.IngressGuard.check_source guard guardComputed⟩

def native (context : Check.CampusTCPService.Context) (before : Check.CampusTCPService.Before)
    (ingress : IngressAttachment.InterfaceRef) (entry : NetfilterNAT.Entry) (direction : FlowNAT.Direction) (hop : String) :
    Except String (Check.CampusTCPRoundGateway.Native context before ingress entry direction hop) := do
  let actual ← checks context before ingress
  let budget ← verify (actual.budget = 100000) "The initial comparison budget differs."
  let forward ← verify (actual.forward.passed = true) "The initial installed forward comparison fails."
  let guard ← verify (actual.guard.passed = true) "The initial installed ingress comparison fails."
  let ingressPermit ← verify (before.guard.permits ingress.ifindex.val (entry.flow.input direction) = true)
    "The initial ingress denies the selected tuple."
  let forwarding ← verify (ConntrackLifecycle.ForwardConditions (before.configuration.pipeline context.routing)
    (entry.flow.input direction) (ConntrackLifecycle.selectedAttachment ⟨entry, true⟩ direction) hop)
    "The initial native route or filters deny the selected tuple."
  let covered ← verify (context.application.any (·.accepts (entry.flow.input direction)) = true)
    "The initial tuple is outside the application class."
  return ⟨actual, budget.property, forward.property, guard.property, ingressPermit.property,
    forwarding.property, covered.property⟩

theorem setup_environment (start : Check.CampusTCPRoundSetup.PreparedStart report complete bytes) :
    Check.CampusTCPRoundEnvironment.environment report.final =
      Check.CampusTCPRoundEnvironment.environment start.next.report.final := by
  apply Check.CampusTCPRoundEnvironment.Trace.environment start.suffix
  intro actual member
  have covered := start.suffix.covered
  simp only [List.append_nil] at covered
  have event : actual.event ∈ Check.CampusTCPRoundSetup.setupEvents bytes := by
    rw [← covered]
    exact List.mem_map.mpr ⟨actual, member, rfl⟩
  simp only [Check.CampusTCPRoundSetup.setupEvents, List.mem_cons, List.not_mem_nil, or_false] at event
  rcases event with same | same | same | same | same
  all_goals rw [same]; trivial

private theorem apply_actual_round (report : M.Report input events) (supported : report.supported = true)
    (finished : report.remaining = []) (complete : H.Completed input.active input.passive)
    (connection : report.final.connection = .application complete (Netlib.Check.CampusTCPModel.Applications.initial complete))
    (ordinary : O.Ordinary report)
    (clean : ∀ history : Check.CampusTCPFacts.StartupHistory report complete, Check.CampusTCPStartupTransport.CleanServices history)
    (request : R.Request input) (entry : NetfilterNAT.Entry)
    (records : (M.beforeService input report.final .primary).tracker.records = [⟨entry, true⟩])
    (dataIngress ackIngress : IngressAttachment.InterfaceRef)
    (original : Check.CampusTCPRoundGateway.Native (input.contextFor .primary) (M.beforeService input report.final .primary)
      dataIngress entry .original "server")
    (reply : Check.CampusTCPRoundGateway.Native (input.contextFor .primary) (M.beforeService input report.final .primary)
      ackIngress entry .reply "client")
    (client : report.final.owner .client = .primary) (server : report.final.owner .server = .primary)
    (unpaused : report.final.assignmentPaused = false) (unsealed : report.final.primarySealed = false)
    (unfenced : report.final.primaryFenced = false) :
    ∃ (initial : R.Initial report complete request) (env : R.NativeEnv initial),
      Nonempty (Check.CampusTCPRoundReverse.CompleteRound initial env) := by
  obtain ⟨initial⟩ := Netlib.Check.CampusTCPRoundStart.Initial.prepareOrdinary ordinary connection
    (clean (Check.CampusTCPRoundStart.historyOfOrdinary ordinary complete connection)) supported finished request
  have current : initial.beforeService = M.beforeService input report.final .primary :=
    Check.CampusTCPRoundLocal.setup_service initial.start .primary
  have selected := initial.records
  change initial.beforeService.tracker.records = [⟨initial.entry, true⟩] at selected
  rw [current, records] at selected
  have entryEq : initial.entry = entry := by
    have recordEq := (List.cons.inj selected).1
    exact (congrArg ConntrackLifecycle.Record.entry recordEq).symm
  have fixed := setup_environment initial.start
  have owners := congrArg Check.CampusTCPRoundEnvironment.Environment.owners fixed
  have paused := congrArg Check.CampusTCPRoundEnvironment.Environment.assignmentPaused fixed
  have sealed := congrArg Check.CampusTCPRoundEnvironment.Environment.primarySealed fixed
  have fenced := congrArg Check.CampusTCPRoundEnvironment.Environment.primaryFenced fixed
  change report.final.owners = initial.state.owners at owners
  let env : R.NativeEnv initial := {
    dataIngress, ackIngress
    original := by rw [current, entryEq]; exact original
    reply := by rw [current, entryEq]; exact reply
    clientOwner := by simpa only [Check.CampusTCPModel.State.owner, ← owners] using client
    serverOwner := by simpa only [Check.CampusTCPModel.State.owner, ← owners] using server
    unpaused := paused.symm.trans unpaused
    unsealed := sealed.symm.trans unsealed
    unfenced := fenced.symm.trans unfenced
    configured := rfl }
  exact ⟨initial, env, Check.CampusTCPRoundReverse.execute initial env⟩

private def ensure (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def rejected : Except String α → Bool | .error _ => true | .ok _ => false

def ingress (input : M.Input) (direction : FlowNAT.Direction) : Except String IngressAttachment.InterfaceRef := do
  let some selected := input.primary.specifications.find? (·.direction == direction)
    | throw "The initial deployment has no directional ingress."
  return selected.ingress

private def checkTheorem (input : M.Input) (events : List M.Event) : IO Unit := do
  let report ← load ((input.check (events.take 25)).mapError (·.message))
  let supported ← load (verify (report.supported = true) "The actual startup prefix is unsupported.")
  let finished ← load (verify (report.remaining = []) "The actual startup prefix has unread input.")
  match connection : report.final.connection with
  | .startup .. => throw (IO.userError "The initial prefix must complete startup.")
  | .recovering .. => throw (IO.userError "The ordinary startup prefix entered recovery.")
  | .application complete endpoints =>
    let clientEmpty ← load (verify (endpoints.client.steps = []) "The initial client already has application operations.")
    let serverEmpty ← load (verify (endpoints.server.steps = []) "The initial server already has application operations.")
    have startup : report.final.connection =
        .application complete (Netlib.Check.CampusTCPModel.Applications.initial complete) := by
      rw [connection, Check.CampusTCPRoundSetup.applications_initial endpoints clientEmpty.property serverEmpty.property]
    let ordinary ← load (ordinary report)
    let clean ← load (cleanServices report complete ordinary)
    let bytes : List UInt8 := [37]
    let pendingFits ← load (verify (bytes.length ≤ input.active.pendingLimit) "The initial request exceeds pending storage.")
    let mssFits ← load (verify (bytes.length ≤ TCP.Handshake.effectiveMSS input.active (TCP.Handshake.receiveOffer input.passive))
      "The initial request exceeds learned MSS.")
    let receiveFits ← load (verify (bytes.length ≤ input.passive.capacity) "The initial request exceeds the peer window.")
    let request : R.Request input := ⟨bytes, by decide, pendingFits.property, mssFits.property, receiveFits.property⟩
    let before := M.beforeService input report.final .primary
    match records : before.tracker.records with
    | [⟨entry, true⟩] =>
      let dataIngress ← load (ingress input .original)
      let ackIngress ← load (ingress input .reply)
      let original ← load (native (input.contextFor .primary) before dataIngress entry .original "server")
      let reply ← load (native (input.contextFor .primary) before ackIngress entry .reply "client")
      let client ← load (verify (report.final.owner .client = .primary) "The client route must use primary.")
      let server ← load (verify (report.final.owner .server = .primary) "The server route must use primary.")
      let unpaused ← load (verify (report.final.assignmentPaused = false) "The initial gateway is paused.")
      let unsealed ← load (verify (report.final.primarySealed = false) "The initial gateway is sealed.")
      let unfenced ← load (verify (report.final.primaryFenced = false) "The initial gateway is fenced.")
      have applied := apply_actual_round report supported.property finished.property complete startup ordinary clean.property request
        entry records dataIngress ackIngress original reply client.property server.property unpaused.property unsealed.property unfenced.property
      let _ := applied
      let wrong : Header := ⟨0, 0, Packet.Protocol.tcp, 0, 0⟩
      ensure ((before.tracker.model.lookup input.zone wrong).isNone &&
          (before.tracker.model.lookup (input.zone + 1) (entry.flow.input .original)).isNone)
        "A wrong tuple or zone must fail the actual initial binding premise."
      let limit := TCP.Handshake.effectiveMSS input.active (TCP.Handshake.receiveOffer input.passive)
      ensure (rejected (verify (limit + 1 ≤ limit) "MSS") &&
          rejected (verify (input.passive.capacity + 1 ≤ input.passive.capacity) "Window"))
        "Oversized MSS and window requests must fail their initial premises."
      let absent := { before with configuration := { before.configuration with id := "netlib-test-missing-installation" } }
      ensure (rejected (native (input.contextFor .primary) absent dataIngress entry .original "server"))
        "An unknown installation must fail initial native evidence."
    | _ => throw (IO.userError "The actual startup must retain one confirmed binding that has seen a reply.")

def run : IO Unit := do
  let input ← load (Check.CampusTCP.Input.parse (← IO.FS.readFile "examples/tcp-ack/trace.json"))
  checkTheorem input.model input.events
  IO.println "Campus complete round theorem applied to the actual startup prefix."

end NetlibTest.CampusTCPRoundTheorem
