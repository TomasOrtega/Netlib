import Netlib.Check.CampusTCPTwoTransferLocatedCore
import Netlib.Check.CampusTCPTwoTransferControlObserve
import Netlib.Check.CampusTCPTwoTransferHandoff

/-!
# Controls preserve the same progress core

Each actual control extends the complete suffix and retains every loss cause.
Installation moves the current gateway view without changing endpoint recovery.
-/

namespace Netlib.Check.CampusTCPTwoTransferLocatedCore

open Protocol Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart
open CampusTCPTwoTransferNative (Checks Routing)
open CampusTCPTwoTransferState (LiveAt)
open CampusTCPTwoTransferControlObserve (afterControl)

namespace T
export CampusTCPTransferEnabled (Control)
end T
namespace W
export CampusTCPTwoTransferMonitor (Monitor observe controlDemand drainTicket)
end W
namespace S
export CampusTCPTwoProgressSender (Stage)
end S
namespace R
export CampusTCPTwoProgressReceiver (Stage)
end R

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current : Cut input complete} {sender : Actor} {gateway location target : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {checks : Checks cut initial.gatewayState.session.entry} {routing : Routing cut gateway}
variable {quantum allowance : Nat} {reverseLower reverseUpper : List UInt8}
variable {monitor : W.Monitor} {sent : S.Stage initial} {received : R.Stage}
variable {actual : Step input} {kind : CampusTCPTwoTransferMonitor.Control}

local notation "cfg" => config initial checks routing quantum allowance reverseLower reverseUpper

private def controlLive (core : Core initial checks routing quantum allowance reverseLower reverseUpper
    current monitor location sent received) (value : T.Control current (kind.event cfg) actual)
    (copied : (value.move.after.report.final.resident target).transport =
      (current.report.final.resident location).transport) :
    LiveAt initial value.move.after target sent monitor.exchange.forward.retries received :=
  core.live.reindex value.move.retained (fun selected => (value.frame.policy selected).symm)
    (fun actor => congrArg (fun endpoints => endpoint endpoints actor) value.endpoints)
    (congrArg (fun endpoints => applicationSteps endpoints sender.other) value.endpoints) copied

private theorem controlRecovery (core : Core initial checks routing quantum allowance reverseLower reverseUpper
    current monitor location sent received) (value : T.Control current (kind.event cfg) actual)
    (copied : (value.move.after.report.final.resident target).transport =
      (current.report.final.resident location).transport) :
    (controlLive core value copied).senderFlight.recovery = core.live.senderFlight.recovery := by
  have next := (controlLive core value copied).senderFlight.runtime
  have same := congrArg (fun endpoints => (endpoint endpoints sender).recovery) value.endpoints
  exact Option.some.inj (next.symm.trans (same.trans core.live.senderFlight.runtime))

private def controlCore (core : Core initial checks routing quantum allowance reverseLower reverseUpper
    current monitor location sent received) (value : T.Control current (kind.event cfg) actual)
    (selected : W.controlDemand monitor = some kind) (drainless : W.drainTicket current.report.final monitor = none)
    (copied : (value.move.after.report.final.resident target).transport =
      (current.report.final.resident location).transport) :
    Core initial checks routing quantum allowance reverseLower reverseUpper
      value.move.after (W.observe cfg monitor actual) target sent received := by
  have observed := CampusTCPTwoTransferControlObserve.control_observe value selected drainless
  let raw := controlLive core value copied
  let live : LiveAt initial value.move.after target sent (W.observe cfg monitor actual).exchange.forward.retries received := {
    anchor := raw.anchor
    senderFlight := by rw [observed]; exact raw.senderFlight
    receiverFacts := raw.receiverFacts
    gatewayState := raw.gatewayState
    gatewayWindow := raw.gatewayWindow
    history := raw.history }
  let sources := CampusTCPTwoTransferSources.Frame.control value
  have recovery : live.senderFlight.recovery = core.live.senderFlight.recovery := by
    have next := live.senderFlight.runtime
    have same := congrArg (fun endpoints => (endpoint endpoints sender).recovery) value.endpoints
    exact Option.some.inj (next.symm.trans (same.trans core.live.senderFlight.runtime))
  have noDrop : CampusTCPTwoProgressLossHistory.isDrop actual = false := by
    unfold CampusTCPTwoProgressLossHistory.isDrop
    rw [value.eventEq]
    cases kind <;> rfl
  have noTimeout : CampusTCPTwoExchangeLoss.isTimeoutOutput actual = false := by
    unfold CampusTCPTwoExchangeLoss.isTimeoutOutput
    rw [value.eventEq]
    cases kind <;> rfl
  exact {
    live := live
    senderWindow := by simpa only [value.endpoints] using core.senderWindow
    originals := sources.originals core.originals
    originalTimes := core.originalTimes
    writer := sources.writer core.writer
    losses := core.losses.append value.move noDrop noTimeout
      (by rw [observed]; rfl) (by rw [observed]; rfl)
      (by rw [observed]; rfl) (by rw [observed]; rfl)
    lossBound := by simpa only [observed, afterControl] using core.lossBound
    primaryQueue := by simpa only [observed, afterControl] using core.primaryQueue.work_same value.frame.work
    retired := core.retired
    gatewayAck := core.gatewayAck
    peerSettled := core.peerSettled
    peerWindow := core.peerWindow
    covered := core.covered
    duplicates := by rw [recovery]; exact core.duplicates
    emptyDuplicate := by rw [recovery]; exact core.emptyDuplicate
    deadline := by rw [recovery]; exact core.deadline
    estimatorBeforeRetire := by rw [recovery]; exact core.estimatorBeforeRetire
    rtoBeforeRetire := by rw [recovery, observed]; exact core.rtoBeforeRetire
    rtoPending := by rw [recovery, observed]; exact core.rtoPending }

def Core.control (core : Core initial checks routing quantum allowance reverseLower reverseUpper
    current monitor location sent received) (value : T.Control current (kind.event cfg) actual)
    (selected : W.controlDemand monitor = some kind) (drainless : W.drainTicket current.report.final monitor = none)
    (ordinary : ∀ ns, kind.event cfg ≠ .installCheckpoint ns) :
    Core initial checks routing quantum allowance reverseLower reverseUpper
      value.move.after (W.observe cfg monitor actual) location sent received :=
  controlCore core value selected drainless
    (CampusTCPTwoTransferHandoff.control_transport value ordinary location)

def Core.install (core : Core initial checks routing quantum allowance reverseLower reverseUpper
    current monitor .primary sent received)
    (value : T.Control current (CampusTCPTwoTransferMonitor.Control.install.event cfg) actual)
    (selected : W.controlDemand monitor = some .install)
    (drainless : W.drainTicket current.report.final monitor = none)
    (installation : InstalledCheckpoint) (present : actual.result.installation = some installation) :
    Core initial checks routing quantum allowance reverseLower reverseUpper
      value.move.after (W.observe cfg monitor actual) .standby sent received := by
  have copied := CampusTCPTwoProgressGatewayAt.install_transport value.move (cfg).executionNS value.eventEq installation present
  exact controlCore (target := .standby) core value selected drainless copied

theorem Core.control_book (core : Core initial checks routing quantum allowance reverseLower reverseUpper
    current monitor location sent received) (value : T.Control current (kind.event cfg) actual)
    (selected : W.controlDemand monitor = some kind) (drainless : W.drainTicket current.report.final monitor = none)
    (ordinary : ∀ ns, kind.event cfg ≠ .installCheckpoint ns) :
    (core.control value selected drainless ordinary).losses.book = core.losses.book := rfl

theorem Core.install_book (core : Core initial checks routing quantum allowance reverseLower reverseUpper
    current monitor .primary sent received)
    (value : T.Control current (CampusTCPTwoTransferMonitor.Control.install.event cfg) actual)
    (selected : W.controlDemand monitor = some .install)
    (drainless : W.drainTicket current.report.final monitor = none)
    (installation : InstalledCheckpoint) (present : actual.result.installation = some installation) :
    (core.install value selected drainless installation present).losses.book = core.losses.book := rfl

theorem Core.install_gateway (core : Core initial checks routing quantum allowance reverseLower reverseUpper
    current monitor .primary sent received)
    (value : T.Control current (CampusTCPTwoTransferMonitor.Control.install.event cfg) actual)
    (selected : W.controlDemand monitor = some .install)
    (drainless : W.drainTicket current.report.final monitor = none)
    (installation : InstalledCheckpoint) (present : actual.result.installation = some installation) :
    (core.install value selected drainless installation present).live.gatewayState =
      core.live.gatewayState.after_install value.move (cfg).executionNS value.eventEq installation present := rfl

theorem Core.control_reaction (core : Core initial checks routing quantum allowance reverseLower reverseUpper
    current monitor location sent received) (value : T.Control current (kind.event cfg) actual)
    (selected : W.controlDemand monitor = some kind) (drainless : W.drainTicket current.report.final monitor = none)
    (ordinary : ∀ ns, kind.event cfg ≠ .installCheckpoint ns) :
    (core.control value selected drainless ordinary).live.receiverFacts.reaction = core.live.receiverFacts.reaction := by
  have next := (core.control value selected drainless ordinary).live.receiverFacts.ackRuntime
  have same := congrArg (fun endpoints => (endpoint endpoints sender.other).ackReaction) value.endpoints
  exact Option.some.inj (next.symm.trans (same.trans core.live.receiverFacts.ackRuntime))

theorem Core.install_reaction (core : Core initial checks routing quantum allowance reverseLower reverseUpper
    current monitor .primary sent received)
    (value : T.Control current (CampusTCPTwoTransferMonitor.Control.install.event cfg) actual)
    (selected : W.controlDemand monitor = some .install)
    (drainless : W.drainTicket current.report.final monitor = none)
    (installation : InstalledCheckpoint) (present : actual.result.installation = some installation) :
    (core.install value selected drainless installation present).live.receiverFacts.reaction = core.live.receiverFacts.reaction := by
  have next := (core.install value selected drainless installation present).live.receiverFacts.ackRuntime
  have same := congrArg (fun endpoints => (endpoint endpoints sender.other).ackReaction) value.endpoints
  exact Option.some.inj (next.symm.trans (same.trans core.live.receiverFacts.ackRuntime))

end Netlib.Check.CampusTCPTwoTransferLocatedCore
