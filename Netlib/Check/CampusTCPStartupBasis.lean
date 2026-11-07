import Netlib.Check.CampusTCPStartupTransport
import Netlib.Check.CampusTCPRecoveredSetup

/-!
# Common startup source for the two-record task

The source is an actual report prefix with its real endpoint cursors.
Ordinary startup and recovery drain retain separate provenance.
-/

namespace Netlib.Check.CampusTCPStartupBasis

open Packet Protocol Protocol.TCP CampusTCPModel

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {events : List CampusTCPModel.Event} {report : Report input events}
variable {entry : NetfilterNAT.Entry} {session : Admission.Session}

structure StaticAlignment (input : Input) (complete : H.Completed input.active input.passive)
    (entry : NetfilterNAT.Entry) (session : Admission.Session) : Prop where
  entryEq : session.entry = entry
  clientMSS : session.clientMSS = Handshake.receiveOffer input.active
  serverMSS : session.serverMSS = Handshake.receiveOffer input.passive
  originalZone : entry.flow.originalZone = input.zone
  replyZone : entry.flow.replyZone = input.zone
  clientInput : Output.reverse complete.certificate.activeSeed.core.inbound = entry.flow.input .original
  serverInput : Output.reverse complete.certificate.passiveSeed.core.inbound = entry.flow.input .reply
  clientOutput : complete.certificate.activeSeed.core.inbound = entry.flow.output .reply
  serverOutput : complete.certificate.passiveSeed.core.inbound = entry.flow.output .original

theorem StaticAlignment.ofOrdinary (aligned : CampusTCPStartupAlignment.Alignment input complete entry session) :
    StaticAlignment input complete entry session :=
  ⟨aligned.entryEq, aligned.clientMSS, aligned.serverMSS, aligned.originalZone, aligned.replyZone,
    aligned.clientInput, aligned.serverInput, aligned.clientOutput, aligned.serverOutput⟩

inductive Origin (input : Input) : {events : List CampusTCPModel.Event} → (report : Report input events) →
    {complete : H.Completed input.active input.passive} → Applications complete → Prop where
  | ordinary {events : List CampusTCPModel.Event} {report : Report input events}
      {complete : H.Completed input.active input.passive} (ordinary : CampusTCPStartupOrigins.Ordinary report)
      (history : CampusTCPFacts.StartupHistory report complete)
      (clean : CampusTCPStartupTransport.CleanServices history) :
      Origin input report (Applications.initial complete)
  | recovered {priorEvents : List CampusTCPModel.Event} {prior : Report input priorEvents} (ready : CampusTCPRecoveredSetup.DrainReady prior)
      (archive : RecoveryArchive input.active input.passive) (drained : CampusTCPRecoveredSetup.Drained ready archive) :
      Origin input drained.next.report drained.next.endpoints

structure Basis (later : Report input laterEvents) (complete : H.Completed input.active input.passive) where
  events : List CampusTCPModel.Event
  report : Report input events
  supported : report.supported = true
  finished : report.remaining = []
  endpoints : Applications complete
  connection : report.final.connection = .application complete endpoints
  origin : Origin input report endpoints
  retained : ∃ extra, later.steps = report.steps ++ extra
  entry : NetfilterNAT.Entry
  session : Admission.Session
  aligned : StaticAlignment input complete entry session
  phase : report.final.primary.transport.admission.phase = .data session

def Basis.retain {later : Report input laterEvents} {current : Report input currentEvents}
    (basis : Basis later complete) (retained : later.steps <+: current.steps) : Basis current complete :=
  { basis with
    retained := by
      obtain ⟨earlier, before⟩ := basis.retained
      have old : basis.report.steps <+: later.steps := ⟨earlier, before.symm⟩
      obtain ⟨later, after⟩ := old.trans retained
      exact ⟨later, after.symm⟩ }

end Netlib.Check.CampusTCPStartupBasis
