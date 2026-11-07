import Netlib.Check.CampusTCPRevocationTransfer
import NetlibTest.CampusTCPRevocationFixture

namespace NetlibTest.CampusTCPRevocation

open Netlib Packet Protocol CampusTCPRevocationFixture

namespace M
export Check.CampusTCPModel (Step Event Report)
end M
namespace R
export Check.CampusTCPRevocation (certifyTransfer)
end R

private def ensure (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def load : Except String α → IO α
  | .ok value => pure value
  | .error reason => throw (IO.userError reason)

private def checked : Except Check.CampusTCPModel.Error α → IO α
  | .ok value => pure value
  | .error reason => throw (IO.userError reason.message)

private def rejects (value : Except String α) (message : String) : IO Unit := do
  match value with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError message)

private def atIndex (values : List α) (index : Nat) : IO α :=
  match values[index]? with
  | some value => pure value
  | none => throw (IO.userError s!"Missing TCP revocation fixture index {index}.")

private def publicRejections (fixture : Fixture) : IO Unit := do
  let config := fixture.base.config
  rejects (R.certifyTransfer fixture.report config fixture.transferEnd fixture.triggerCut 0 fixture.raw)
    "The public TCP certificate must reject a zero service bound."
  rejects (R.certifyTransfer fixture.report config fixture.transferEnd (fixture.triggerCut - 1) 12 fixture.raw)
    "The public TCP certificate must use the actual Logoff cut."
  let permit := { fixture.raw with primary := { fixture.raw.primary with configuration := "permit" } }
  rejects (R.certifyTransfer fixture.report config fixture.transferEnd fixture.triggerCut 12 permit)
    "The public TCP certificate must reject a native target that still permits the revoked session."
  let missing := { fixture.raw with standby := { fixture.raw.standby with guard := "missing-native-guard" } }
  rejects (R.certifyTransfer fixture.report config fixture.transferEnd fixture.triggerCut 12 missing)
    "The public TCP certificate must reject an absent native ingress source."
  let targets ← load (Check.CampusTCPRevocationTargets.Targets.check fixture.input
    (fixture.stateAt fixture.triggerCut) fixture.raw)
  let missingTarget ← checked fixture.missingTargetReport
  ensure (missingTarget.supported && missingTarget.remaining.isEmpty &&
      Check.CampusTCPRevocationPhased.service config fixture.transferEnd fixture.triggerCut targets.names
        fixture.input.initial missingTarget.steps 12)
    "The missing-target suffix must retain the finite B12 tail where service alone is vacuous."
  rejects (R.certifyTransfer missingTarget config fixture.transferEnd fixture.triggerCut 12 fixture.raw)
    "The public TCP certificate must reject an uninstalled target despite its vacuous finite service tail."
  let starved ← checked fixture.starvedReport
  ensure (starved.supported && starved.remaining.isEmpty &&
      !Check.CampusTCPRevocationPhased.service config fixture.transferEnd fixture.triggerCut targets.names
        fixture.input.initial starved.steps 12)
    "The real pending link must remain exposed for more than B12 in the starved report."
  rejects (R.certifyTransfer starved config fixture.transferEnd fixture.triggerCut 12 fixture.raw)
    "The public TCP certificate must reject a real link starved beyond its whole service bound."
  let short ← checked (fixture.input.check (fixture.events.take (fixture.completionCut - 1)))
  ensure (short.supported && short.remaining.isEmpty &&
      !(Check.CampusTCPRevocationCustody.frontier short.final).isEmpty &&
      Check.CampusTCPRevocationPhased.service config fixture.transferEnd fixture.triggerCut targets.names
        fixture.input.initial short.steps 12)
    "The truncated prefix must retain the real old link while finite service windows remain incomplete."
  rejects (R.certifyTransfer short config fixture.transferEnd fixture.triggerCut 12 fixture.raw)
    "The public TCP certificate must reject a prefix before the actual completion."

private def appendedRejections (fixture : Fixture) : IO Unit := do
  let config := fixture.base.config
  let copied ← checked (fixture.input.check (fixture.events ++ [fixture.copyEvent]))
  ensure (copied.supported && copied.remaining.isEmpty && copied.steps.length == 116 &&
      (Check.CampusTCPRevocationCustody.frontier copied.final).length == 1 && copied.final.custody.dropped == 2)
    "The copy negative must contain an actual fresh link copied from the completed parent."
  rejects (R.certifyTransfer copied config fixture.transferEnd fixture.triggerCut 12 fixture.raw)
    "The public TCP certificate must reject resurrection by an actual completed-parent copy."
  let rolledBack ← checked (fixture.input.check (fixture.events ++ [fixture.rollbackEvent]))
  ensure (rolledBack.supported && rolledBack.remaining.isEmpty &&
      rolledBack.final.standby.configuration.id == "permit" &&
      !(← atIndex rolledBack.steps 115).result.passed)
    "The rollback negative must contain the real restored native permit and its false verdict."
  rejects (R.certifyTransfer rolledBack config fixture.transferEnd fixture.triggerCut 12 fixture.raw)
    "The public TCP certificate must reject an actual native policy rollback after completion."
  let dropped ← checked (fixture.input.check (fixture.events ++ [fixture.excessDropEvent]))
  ensure (dropped.supported && dropped.remaining.isEmpty && dropped.final.custody.dropped == 3 &&
      dropped.final.custody.resolutions.any (fun entry => entry.item.id == fixture.heldIngress &&
        decide (entry.disposition = .dropped)))
    "The excess-loss negative must consume the actual retained ACK ingress as a third physical loss."
  rejects (R.certifyTransfer dropped config fixture.transferEnd fixture.triggerCut 12 fixture.raw)
    "The public TCP certificate must reject a third drop under the original total allowance of two."
  let some (Check.CampusTCPModel.Event.serve ticket _) := (fixture.events : List M.Event)[114]?
    | throw (IO.userError "The final actual retry service is absent.")
  let mismatched ← checked (fixture.input.check (fixture.events.take 114 ++ [.serve ticket (some ([0], none))]))
  let service ← atIndex mismatched.final.services (mismatched.final.services.length - 1)
  ensure (mismatched.supported && mismatched.remaining.isEmpty && !service.observed && service.routeMatched &&
      service.evidence.output.isNone && mismatched.final.custody.dropped == 2 &&
      (Check.CampusTCPRevocationCustody.frontier mismatched.final).isEmpty)
    "The observation negative must retain the actual denied retry, empty frontier, and mismatched raw input bytes."
  rejects (R.certifyTransfer mismatched config fixture.transferEnd fixture.triggerCut 12 fixture.raw)
    "The composed public certificate must reject mismatched observed retry bytes despite actual native denial."
  let oldDelivery ← load fixture.oldDeliveryEvent
  match fixture.input.check (fixture.events ++ [oldDelivery]) with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "A completed receiver-link identity cannot produce another actual delivery.")

private theorem transferFacts {input : Check.CampusTCPModel.Input} {events : List M.Event}
    {report : M.Report input events} {config : Check.CampusTCPStartupTransferMonitor.Config}
    {transferEnd triggerCut bound : Nat}
    (composed : Check.CampusTCPRevocation.CertifiedTransfer report config transferEnd triggerCut bound) :
    ∃ joint : Check.CampusTCPRevocation.WithTransfer composed.core.result,
      joint.prior.transfer.current.report.steps = report.steps.take transferEnd ∧
      joint.prior.transfer.readWrite.read.actual.result.read = config.transfer.lower ++ config.transfer.upper ∧
      joint.prior.transfer.value.completed.reader.result.read = config.transfer.reverseLower ++ config.transfer.reverseUpper ∧
      joint.prior.transfer.monitor.controls.map (·.1) =
        [.pause, .capture, .install, .clientRoute, .serverRoute, .fence, .resume] := by
  exact composed.transfer.elim (fun joint => ⟨joint, joint.history, joint.streams.1, joint.streams.2, joint.controls⟩)

private theorem readOrigin {input : Check.CampusTCPModel.Input} {events : List M.Event}
    (report : M.Report input events) (cut : Nat) (quiet : Check.CampusTCPRevocationReadOrigin.NoReceiptsAfter report cut)
    (complete : Check.TCPHandshake.Completed input.active input.passive)
    (endpoints : Check.CampusTCPModel.Applications complete)
    (connection : report.final.connection = .application complete endpoints)
    (actual : M.Step input) (actualMember : actual ∈ report.steps) (actor : Check.CampusTCPModel.Actor)
    (reader : TCP.ApplicationTrace.Step) (recorded : actual.result.application = some (actor, reader))
    (count : Nat) (event : reader.event = .read count) (later : cut ≤ reader.stamp)
    (index : Nat) (byte : UInt8) (selected : reader.readBytes[index]? = some byte) :
    Nonempty (Check.CampusTCPRevocationReadOrigin.Origin report cut
      (Check.CampusTCPRevocationReadOrigin.seed complete actor.other)
      (Check.CampusTCPEnabled.applicationSteps endpoints actor.other) actor
      (Check.CampusTCPEnabled.applicationSteps endpoints actor) reader index byte) := by
  have member := Check.CampusTCPApplicationHistory.Report.application_member report actual actualMember actor reader recorded
  have localMember : reader ∈ Check.CampusTCPEnabled.applicationSteps endpoints actor := by
    simpa only [connection, Check.CampusTCPApplicationHistory.connectionSteps] using member
  exact Check.CampusTCPRevocationReadOrigin.Report.read_origin_after_cut report cut quiet complete endpoints connection
    actor reader localMember count event later index byte selected

private def certified (fixture : Fixture) : IO Nat := do
  let composed ← load (R.certifyTransfer fixture.report fixture.base.config fixture.transferEnd fixture.triggerCut 12 fixture.raw)
  let certificate := composed.core
  let result := certificate.result
  let _ := transferFacts composed
  let _ : Check.CampusTCPRevocationPhased.CheckedActions fixture.base.config fixture.transferEnd fixture.triggerCut
      certificate.targets.names fixture.report := result.checked
  let _ : Check.CampusTCPRevocationClosure.Closed certificate.targets result.current := result.closed
  let _ : Check.CampusTCPRevocationClosure.Closed certificate.targets fixture.report.final ∧
      ∀ actual ∈ fixture.report.steps.drop result.completion, Check.CampusTCPRevocationClosure.Quiet actual := result.future
  let _ : Check.CampusTCPRevocationReadOrigin.NoReceiptsAfter fixture.report result.completion := result.no_receipts_after
  let _ : fixture.report.final.custody.dropped ≤ fixture.base.config.transfer.lossAllowance := result.whole_budget
  let _ := result.history
  let _ := certificate.targets.primary.configurationFound
  let _ := certificate.targets.primary.guardFound
  let _ := certificate.targets.standby.configurationFound
  let _ := certificate.targets.standby.guardFound
  ensure (result.slot == 7 && result.completion == 109 && result.completion == fixture.completionCut &&
      result.current.time == 109 && result.current.authentication == 8 &&
      result.current.primary.configuration.id == "revoke-deny" && result.current.primary.guard.id == "revoke-deny" &&
      result.current.standby.configuration.id == "revoke-deny" && result.current.standby.guard.id == "revoke-deny" &&
      (Check.CampusTCPRevocationCustody.frontier result.current).isEmpty &&
      result.completion < fixture.triggerCut + Check.CampusTCPRevocationBound.slots (fixture.stateAt fixture.triggerCut) 12)
    "The public certificate must select the real 109 cut and all four exact native deny sources."
  for actual in fixture.report.steps.drop result.completion do
    ensure (actual.result.receipt.isNone && actual.result.service.all (fun served => served.evidence.output.isNone))
      "Each stored post-cut operation must have no new network receipt or receiver-link emission."
  let shutdown := fixture.report.steps.drop fixture.triggerCut
  let initial := Check.CampusTCPRevocation.cutState fixture.report fixture.triggerCut
  let barrier := fixture.barrierCut - fixture.triggerCut
  if within : barrier ≤ shutdown.length then
    match selected : Check.CampusTCPRevocationControl.pendingAt certificate.targets.names initial
        Check.CampusTCPRevocationMonitor.initial shutdown barrier with
    | none => throw (IO.userError "The actual barrier must expose its unresolved stale-service link.")
    | some demand =>
      have witness := Check.CampusTCPRevocationEnabled.check_witness certificate.targets.names
        fixture.base.config.transfer.lossAllowance initial shutdown result.checked.enabled barrier within demand selected
      have _ : ∃ actual : M.Step fixture.input,
          actual.before = Check.CampusTCPSchedule.stateAt initial shutdown barrier ∧
          actual.result.supported = true ∧
          Check.CampusTCPRevocationControl.allowed certificate.targets.names
            fixture.base.config.transfer.lossAllowance actual.before actual.event = true ∧
          Check.CampusTCPRevocationControl.serves certificate.targets.names demand actual.event = true := by
        obtain ⟨enabled⟩ := witness
        exact ⟨enabled.actual, enabled.before, enabled.supported, enabled.allowed, enabled.serves⟩
      match demand with
      | .install _ => throw (IO.userError "The four real native installs must precede the remaining link demand.")
      | .resolveLink _ service bytes =>
        ensure (service == fixture.staleService &&
            Check.CampusTCPRevocationEnabled.proposed certificate.targets.names
              fixture.base.config.transfer.lossAllowance (Check.CampusTCPSchedule.stateAt initial shutdown barrier) demand ==
                .deliver service bytes true)
          "The exhausted original loss allowance must enable delivery of the actual stale link."
  else throw (IO.userError "The actual four-target barrier is outside the retained shutdown suffix.")
  match connection : fixture.report.final.connection with
  | .application complete endpoints =>
    match found : fixture.report.steps[fixture.readSlot]? with
    | none => throw (IO.userError "The actual post-cut application read is absent.")
    | some actual =>
      match recorded : actual.result.application with
      | none => throw (IO.userError "The post-cut read has no actual application operation.")
      | some (actor, reader) =>
        have actualMember := List.mem_of_getElem? found
        if event : reader.event = .read payload.length then
          if later : result.completion ≤ reader.stamp then
            for (index, byte) in (List.range payload.length).zip payload do
              if selected : reader.readBytes[index]? = some byte then
                let _ := readOrigin fixture.report result.completion result.no_receipts_after complete endpoints connection
                  actual actualMember actor reader recorded payload.length event later index byte selected
              else throw (IO.userError "A selected post-cut read byte differs from its actual application record.")
          else throw (IO.userError "The application read must follow the actual network completion cut.")
        else throw (IO.userError "The recorded application operation must be the actual two-byte read.")
  | _ => throw (IO.userError "The original endpoint cursors must remain in the established application phase.")
  return result.completion

def run : IO Unit := do
  let fixture ← build
  ensure (fixture.transferEnd == 95 && fixture.triggerCut == 102 && fixture.barrierCut == 108 &&
      fixture.completionCut == 109 && fixture.report.steps.length == 115 &&
      fixture.report.supported && fixture.report.remaining.isEmpty && !fixture.report.compliant &&
      fixture.base.report.final.custody.dropped == 2 && fixture.report.final.custody.dropped == 2)
    "The public TCP test must retain the same 95-slot transfer, real Logoff, false stale verdict, and original two losses."
  let _ := fixture.prefix
  let completion ← certified fixture
  let trigger := fixture.stateAt fixture.triggerCut
  let stale := fixture.stateAt (fixture.triggerCut + 2)
  let barrier := fixture.stateAt fixture.barrierCut
  ensure (trigger.authentication == 8 && (Check.CampusTCPRevocationCustody.frontier trigger).length == 1 &&
      (Check.CampusTCPRevocationCustody.frontier stale).length == 2 &&
      (Check.CampusTCPRevocationCustody.frontier barrier).length == 1 && barrier.custody.dropped == 2)
    "Stale permit service must add its real second link after Logoff before the four-target barrier."
  let old ← atIndex fixture.report.final.services fixture.oldService
  let stale ← atIndex fixture.report.final.services fixture.staleService
  ensure (old.ticket.value.gateway == .standby && stale.ticket.value.gateway == .standby &&
      old.evidence.output.isSome && stale.evidence.output.isSome && !stale.passed &&
      old.ticket.value.source.bytes != stale.ticket.value.source.bytes)
    "The two real old outputs must retain their distinct source bytes and actual standby service."
  ensure (fixture.report.final.custody.resolutions.any (fun entry => entry.item.id == fixture.oldPacket &&
      decide (entry.disposition = .delivered)) &&
      fixture.report.final.custody.pendingID (Check.CampusTCPModel.Transit.ingressAt fixture.ackOutput) ==
        some fixture.heldIngress)
    "The old link must be actually delivered while its later ACK remains a distinct pending ingress identity."
  let read ← atIndex fixture.report.steps fixture.readSlot
  ensure (read.event == .read .server payload.length && read.before.time ≥ completion &&
      read.result.read == payload && read.result.receipt.isNone)
    "The application read after network cutoff must return the two bytes accepted in earlier real receipts."
  let retry ← atIndex fixture.report.steps 114
  ensure (retry.result.service.any (fun served => served.ticket.value.gateway == .standby &&
      served.evidence.output.isNone) && (Check.CampusTCPRevocationCustody.frontier fixture.report.final).isEmpty)
    "The actual retry service after cutoff must reach the standby deny target without minting another link."
  publicRejections fixture
  appendedRejections fixture
  IO.println s!"TCP revocation: {fixture.report.steps.length} actual slots, completion {completion}, four native denies, two retained losses."

end NetlibTest.CampusTCPRevocation
