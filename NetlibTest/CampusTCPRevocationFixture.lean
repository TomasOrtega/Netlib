import Netlib.Check.CampusTCPRevocationDenial
import Netlib.Check.CampusTCPRevocationFrames
import Netlib.Check.CampusTCPRevocationControl
import Netlib.Check.CampusTCPRevocationPhased
import NetlibTest.CampusTCPStartupEndToEnd

namespace NetlibTest.CampusTCPRevocationFixture

open Netlib Packet Protocol
namespace M
export Check.CampusTCPModel (Input State Step Event Report Actor Gateway Transit)
end M
namespace T
export Check.CampusTCPRevocationTargets (Raw Targets)
end T

def payload : List UInt8 := [101, 102]

private def ensure (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def load : Except String α → IO α
  | .ok value => pure value
  | .error reason => throw (IO.userError reason)

private def addTargets (json : Lean.Json) : Except String Lean.Json := do
  let configs ← (← json.getObjVal? "configs").getArr?
  let guards ← (← json.getObjVal? "guards").getArr?
  let some configuration := configs[0]? | throw "The native deny source is absent."
  let some guard := guards[0]? | throw "The native deny ingress source is absent."
  unless (← (← configuration.getObjVal? "id").getStr?) == "deny" &&
      (← (← guard.getObjVal? "id").getStr?) == "deny" do
    throw "The base fixture must retain its initial deny sources."
  let configured := json.setObjVal! "configs" (.arr (configs.push (configuration.setObjVal! "id" (.str "revoke-deny"))))
  return configured.setObjVal! "guards" (.arr (guards.push (guard.setObjVal! "id" (.str "revoke-deny"))))

def source : IO Check.CampusTCP.Input := do
  let original ← load (Import.Json.parse (← IO.FS.readFile "examples/campus-tcp-transfer/trace.json"))
  let primary ← load (addTargets original)
  let standby ← load (addTargets (← load (original.getObjVal? "standby")))
  load (Check.CampusTCP.Input.fromJson (primary.setObjVal! "standby" standby))

structure Run (base : CampusTCPStartupEndToEnd.Completed) where
  events : List M.Event
  report : M.Report base.source.model events
  supported : report.supported = true
  finished : report.remaining = []
  extra : List (M.Step base.source.model)
  history : report.steps = base.report.steps ++ extra

private def start (base : CampusTCPStartupEndToEnd.Completed) : Run base :=
  ⟨base.events, base.report, base.supported, base.finished, [], by simp⟩

private def appendStep (before : Run base) (event : M.Event) (expected : Bool := true) :
    IO (Run base × M.Step base.source.model) := do
  match computed : Check.CampusTCPModel.step base.source.model before.report.final event with
  | .error reason => throw (IO.userError reason.message)
  | .ok effect =>
    if accepted : effect.supported = true then
      ensure (effect.passed == expected) "The actual revocation operation has a different policy verdict."
      let actual : M.Step base.source.model := ⟨before.report.final, event, effect, computed⟩
      let report := Check.CampusTCPSchedule.Report.appendStep before.report before.supported before.finished actual rfl accepted
      return (⟨before.events ++ [event], report,
        Check.CampusTCPSchedule.Report.appendStep_supported before.report before.supported before.finished actual rfl accepted,
        rfl, before.extra ++ [actual], by simp only [report, Check.CampusTCPSchedule.Report.appendStep,
          before.history, List.append_assoc]⟩, actual)
    else throw (IO.userError effect.decision)

private def append (before : Run base) (event : M.Event) (expected : Bool := true) : IO (Run base) := do
  return (← appendStep before event expected).1

private def assign (before : Run base) (output : Nat) : IO (Run base × Nat) := do
  let some produced := before.report.final.outputs[output]?
    | throw (IO.userError "The selected actual endpoint output is absent.")
  let ticket := before.report.final.work.nextID
  let gateway := before.report.final.owner produced.actor
  let after ← append before (.assign output (base.config.transfer.ingress gateway produced.actor))
  return (after, ticket)

private def serve (before : Run base) (ticket : Nat) (expected : Bool := true) : IO (Run base × Nat) := do
  let index := before.report.final.services.length
  let after ← append before (.serve ticket none) expected
  return (after, index)

private def deliver (before : Run base) (service : Nat) : IO (Run base) := do
  let some served := before.report.final.services[service]?
    | throw (IO.userError "The selected actual gateway service is absent.")
  let some emission := served.evidence.output
    | throw (IO.userError "The selected actual gateway service emitted no packet.")
  append before (.deliver service emission.bytes true)

private def pendingPacket (before : Run base) (selected : M.Transit base.source.model → Bool) : IO Nat := do
  let some id := before.report.final.custody.pendingID selected
    | throw (IO.userError s!"The selected actual custody packet is absent at slot {before.report.steps.length}.")
  return id

private def endpoint (before : Run base) (actor : M.Actor) : IO TCP.Endpoint.State :=
  load (CampusTCPRecoveryRound.endpoint before.report.final actor)

structure Fixture where
  base : CampusTCPStartupEndToEnd.Completed
  current : Run base
  raw : T.Raw
  triggerCut : Nat
  barrierCut : Nat
  completionCut : Nat
  oldService : Nat
  staleService : Nat
  oldPacket : Nat
  ackOutput : Nat
  heldIngress : Nat
  readSlot : Nat

def Fixture.transferEnd (fixture : Fixture) : Nat := fixture.base.report.steps.length
def Fixture.report (fixture : Fixture) := fixture.current.report
def Fixture.events (fixture : Fixture) := fixture.current.events
def Fixture.input (fixture : Fixture) := fixture.base.source.model

theorem Fixture.prefix (fixture : Fixture) :
    fixture.report.steps.take fixture.transferEnd = fixture.base.report.steps := by
  rw [Fixture.report, fixture.current.history]
  exact List.take_left

def Fixture.stateAt (fixture : Fixture) (slot : Nat) : M.State fixture.input :=
  Check.CampusTCPSchedule.stateAt fixture.input.initial fixture.report.steps slot

def Fixture.copyEvent (fixture : Fixture) : M.Event := .copyPacket fixture.oldPacket
def Fixture.rollbackEvent (_fixture : Fixture) : M.Event := .installAt .standby "permit"
def Fixture.excessDropEvent (fixture : Fixture) : M.Event := .dropPacket fixture.heldIngress

def Fixture.oldDeliveryEvent (fixture : Fixture) : Except String M.Event := do
  let some served := fixture.report.final.services[fixture.oldService]?
    | throw "The earlier actual service is absent."
  let some emission := served.evidence.output | throw "The earlier actual emission is absent."
  return .deliver fixture.oldService emission.bytes true

def Fixture.missingTargetEvents (fixture : Fixture) : List M.Event :=
  fixture.events.filter fun event => match event with
    | .installGuardAt .standby "revoke-deny" => false
    | _ => true

def Fixture.missingTargetReport (fixture : Fixture) :
    Except Check.CampusTCPModel.Error (M.Report fixture.input fixture.missingTargetEvents) :=
  fixture.input.check fixture.missingTargetEvents

def Fixture.starvedEvents (fixture : Fixture) : List M.Event :=
  fixture.events.take fixture.barrierCut ++ List.replicate 13 (.read .server 0)

def Fixture.starvedReport (fixture : Fixture) :
    Except Check.CampusTCPModel.Error (M.Report fixture.input fixture.starvedEvents) :=
  fixture.input.check fixture.starvedEvents

def Fixture.verifyNegative (fixture : Fixture) : IO Unit := do
  let targets ← load (Check.CampusTCPRevocationTargets.Targets.check fixture.input
    (fixture.stateAt fixture.triggerCut) fixture.raw)
  let final := fixture.report.final
  match Check.CampusTCPModel.step fixture.input final fixture.copyEvent with
  | .error reason => throw (IO.userError reason.message)
  | .ok copied =>
    ensure ((Check.CampusTCPRevocationCustody.frontier copied.state).length == 1)
      "Copying a completed application link must expose the forbidden resurrection."
  match Check.CampusTCPModel.step fixture.input final fixture.rollbackEvent with
  | .error reason => throw (IO.userError reason.message)
  | .ok rolledBack =>
    ensure (!rolledBack.passed && rolledBack.state.standby.configuration.id == "permit")
      "Rollback must retain the real restored source and its false native verdict."
  match Check.CampusTCPModel.step fixture.input final fixture.excessDropEvent with
  | .error reason => throw (IO.userError reason.message)
  | .ok dropped =>
    ensure (dropped.state.custody.dropped == 3)
      "The forbidden third loss must refer to a real pending ingress packet."
  match Check.CampusTCPModel.step fixture.input final (← load fixture.oldDeliveryEvent) with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "A completed old link must not be delivered again.")
  let missing ← match fixture.missingTargetReport with
    | .error reason => throw (IO.userError reason.message)
    | .ok report => pure report
  ensure (missing.supported && missing.remaining.isEmpty &&
      !Check.CampusTCPRevocationControl.service targets.names (fixture.stateAt fixture.triggerCut)
        Check.CampusTCPRevocationMonitor.initial (missing.steps.drop fixture.triggerCut) 4)
    "Omitting one actual target must fail the four-install service obligation."
  let starved ← match fixture.starvedReport with
    | .error reason => throw (IO.userError reason.message)
    | .ok report => pure report
  ensure (starved.supported && starved.remaining.isEmpty &&
      !Check.CampusTCPRevocationPhased.service fixture.base.config fixture.transferEnd fixture.triggerCut
        targets.names fixture.input.initial starved.steps 12)
    "Withholding a real old link beyond B12 must fail the same whole service contract."
  ensure (!Check.CampusTCPRevocationPhased.actions fixture.base.config fixture.transferEnd
      (fixture.triggerCut - 1) targets.names fixture.report)
    "A cut before the actual Logoff must fail the phased trigger check."

def build : IO Fixture := do
  let base ← CampusTCPStartupEndToEnd.completedInput (← source)
  ensure (base.report.steps.length == 95 && base.report.final.authentication == 7 &&
      base.report.final.custody.dropped == 2 && base.report.final.custody.pending.isEmpty)
    "Revocation must extend the exact 95-slot run and its two spent losses."
  let raw : T.Raw := ⟨⟨"revoke-deny", "revoke-deny"⟩, ⟨"revoke-deny", "revoke-deny"⟩⟩
  let firstOutput := base.report.final.outputs.length
  let written ← append (start base) (.write .client payload)
  let sent ← append written (.send .client 1 true)
  let (assigned, firstTicket) ← assign sent firstOutput
  let (old, oldService) ← serve assigned firstTicket
  let oldPacket ← pendingPacket old (Check.CampusTCPModel.Transit.linkAt oldService)
  let sent ← append old (.send .client 1 true)
  let (assigned, secondTicket) ← assign sent (firstOutput + 1)
  let revoked ← append assigned (.authentication 7)
  let triggerCut := revoked.report.steps.length
  ensure (Check.CampusTCPRevocationTargets.revoked base.source.model revoked.report.final.authentication)
    "The actual raw Logoff must revoke the same TCP session."
  let _targets ← load (Check.CampusTCPRevocationTargets.Targets.check base.source.model revoked.report.final raw)
  let primary ← append revoked (.installAt .primary "revoke-deny")
  let (stale, staleService) ← serve primary secondTicket false
  let some stalePacket := stale.report.final.services[staleService]?
    | throw (IO.userError "The actual stale service is absent.")
  ensure (stalePacket.evidence.output.isSome && !stalePacket.passed)
    "The stale installed permit must retain its real output and false policy verdict."
  let primary ← append stale (.installGuardAt .primary "revoke-deny")
  let received ← deliver primary oldService
  let standby ← append received (.installAt .standby "revoke-deny")
  let barrier ← append standby (.installGuardAt .standby "revoke-deny")
  let barrierCut := barrier.report.steps.length
  let drained ← deliver barrier staleService
  let completionCut := drained.report.steps.length
  ensure ((Check.CampusTCPRevocationCustody.frontier drained.report.final).isEmpty)
    "Both actual old receiver-link identities must be resolved."
  let ackOutput := drained.report.final.outputs.length
  let acknowledged ← append drained (.emitAck .server true)
  let heldIngress ← pendingPacket acknowledged (Check.CampusTCPModel.Transit.ingressAt ackOutput)
  let readSlot := acknowledged.report.steps.length
  let (read, actualRead) ← appendStep acknowledged (.read .server payload.length)
  ensure (actualRead.result.read == payload)
    "The later application read must return only bytes received before the cutoff."
  let sender ← endpoint read .client
  let some recovery := sender.recovery | throw (IO.userError "The original sender recovery is absent.")
  let some deadline := recovery.deadline | throw (IO.userError "The original data retry has no deadline.")
  let clocked ← append read (.advanceClock .client deadline)
  let retryOutput := clocked.report.final.outputs.length
  let retried ← append clocked (.timeout .client true)
  let (queued, retryTicket) ← assign retried retryOutput
  let (finished, deniedService) ← serve queued retryTicket
  let some denied := finished.report.final.services[deniedService]?
    | throw (IO.userError "The actual denied retry service is absent.")
  ensure (denied.evidence.output.isNone && finished.report.final.custody.dropped == 2 &&
      (Check.CampusTCPRevocationCustody.frontier finished.report.final).isEmpty &&
      finished.report.final.custody.pendingID (Check.CampusTCPModel.Transit.ingressAt ackOutput) == some heldIngress)
    "Later retry service must deny output and retain the earlier ACK ingress without another loss."
  let fixture : Fixture := ⟨base, finished, raw, triggerCut, barrierCut, completionCut,
    oldService, staleService, oldPacket, ackOutput, heldIngress, readSlot⟩
  let targets ← load (Check.CampusTCPRevocationTargets.Targets.check fixture.input (fixture.stateAt triggerCut) raw)
  ensure (Check.CampusTCPRevocationControl.actions targets.names 2 (fixture.report.steps.drop triggerCut) &&
      Check.CampusTCPRevocationControl.service targets.names (fixture.stateAt triggerCut)
        Check.CampusTCPRevocationMonitor.initial (fixture.report.steps.drop triggerCut) 4)
    "The actual shutdown suffix must pass its native action and B4 service checks."
  ensure (Check.CampusTCPRevocationPhased.actions base.config fixture.transferEnd triggerCut targets.names fixture.report &&
      Check.CampusTCPRevocationPhased.service base.config fixture.transferEnd triggerCut targets.names
        fixture.input.initial fixture.report.steps 12)
    "The same full report must pass one phased action and B12 service contract."
  ensure (!Check.CampusTCPRevocationControl.allowed targets.names 2 fixture.report.final fixture.copyEvent &&
      !Check.CampusTCPRevocationControl.allowed targets.names 2 fixture.report.final fixture.rollbackEvent &&
      !Check.CampusTCPRevocationControl.allowed targets.names 2 fixture.report.final fixture.excessDropEvent)
    "The shutdown profile must reject copy, policy rollback, and a third physical loss."
  fixture.verifyNegative
  return fixture

end NetlibTest.CampusTCPRevocationFixture
