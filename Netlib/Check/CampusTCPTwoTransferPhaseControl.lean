import Netlib.Check.CampusTCPTwoTransferPhaseState
import Netlib.Check.CampusTCPTwoTransferPreparationState
import Netlib.Check.CampusTCPTwoTransferWorkInstall

namespace Netlib.Check.CampusTCPTwoTransferPhaseState

open Protocol Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart
open CampusTCPTwoTransferNative (Checks Routing)
open CampusTCPTwoTransferLocatedCore (Core config)
open CampusTCPTwoTransferWork

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current next : Cut input complete} {sender : Actor} {gateway location target : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {checks : Checks cut initial.gatewayState.session.entry} {routing : Routing cut gateway}
variable {quantum allowance : Nat} {reverseLower reverseUpper : List UInt8}
variable {monitor updated : CampusTCPTwoTransferMonitor.Monitor}
variable {sent : CampusTCPTwoProgressSender.Stage initial} {received : CampusTCPTwoProgressReceiver.Stage}
variable {actual : Step input} {kind : CampusTCPTwoTransferMonitor.Control}

local notation "cfg" => config initial checks routing quantum allowance reverseLower reverseUpper

private theorem control_view_eq
    (core : Core initial checks routing quantum allowance reverseLower reverseUpper current monitor location sent received)
    (value : CampusTCPTransferEnabled.Control current (kind.event cfg) actual)
    (selected : CampusTCPTwoTransferMonitor.controlDemand monitor = some kind)
    (drainless : CampusTCPTwoTransferMonitor.drainTicket current.report.final monitor = none)
    (ordinary : ∀ ns, kind.event cfg ≠ .installCheckpoint ns) :
    control_view core.live.gatewayState value ordinary =
      (core.control value selected drainless ordinary).live.gatewayState := by
  rfl

private theorem control_recovery
    (core : Core initial checks routing quantum allowance reverseLower reverseUpper current monitor location sent received)
    (value : CampusTCPTransferEnabled.Control current (kind.event cfg) actual)
    (selected : CampusTCPTwoTransferMonitor.controlDemand monitor = some kind)
    (drainless : CampusTCPTwoTransferMonitor.drainTicket current.report.final monitor = none)
    (ordinary : ∀ ns, kind.event cfg ≠ .installCheckpoint ns) :
    (core.control value selected drainless ordinary).live.senderFlight.recovery = core.live.senderFlight.recovery := by
  have runtime := (core.control value selected drainless ordinary).live.senderFlight.runtime
  have same := congrArg (fun endpoints => (endpoint endpoints sender).recovery) value.endpoints
  exact Option.some.inj (runtime.symm.trans (same.trans core.live.senderFlight.runtime))

private theorem install_recovery
    (core : Core initial checks routing quantum allowance reverseLower reverseUpper current monitor .primary sent received)
    (value : CampusTCPTransferEnabled.Control current (CampusTCPTwoTransferMonitor.Control.install.event cfg) actual)
    (selected : CampusTCPTwoTransferMonitor.controlDemand monitor = some .install)
    (drainless : CampusTCPTwoTransferMonitor.drainTicket current.report.final monitor = none)
    (installation : InstalledCheckpoint) (present : actual.result.installation = some installation) :
    (core.install value selected drainless installation present).live.senderFlight.recovery = core.live.senderFlight.recovery := by
  have runtime := (core.install value selected drainless installation present).live.senderFlight.runtime
  have same := congrArg (fun endpoints => (endpoint endpoints sender).recovery) value.endpoints
  exact Option.some.inj (runtime.symm.trans (same.trans core.live.senderFlight.runtime))

variable {core : Core initial checks routing quantum allowance reverseLower reverseUpper current monitor location sent received}
variable {after : Core initial checks routing quantum allowance reverseLower reverseUpper next updated target sent received}
variable {part : CampusTCPTwoProgressSender.Part}

private def debt_frame (debt : Debt core part)
    (forward : updated.exchange.forward = monitor.exchange.forward)
    (book : after.losses.book = core.losses.book)
    (work : ∀ part lane, Work initial checks current location part lane → Work initial checks next target part lane)
    (ack : ∀ lane, AckWork checks core.live lane → AckWork checks after.live lane) : Debt after part := by
  cases debt with
  | cause position chosen => exact .cause position (by rw [book]; exact chosen)
  | lower same pending => exact .lower same (by rw [forward]; exact work _ _ pending)
  | upper same pending => exact .upper same (by rw [forward]; exact work _ _ pending)
  | retry pending => exact .retry (by rw [forward]; exact work _ _ pending)
  | ack lane pending waiting covered => exact .ack lane (by rw [forward]; exact pending) (ack lane waiting) covered

private def active_frame (value : Active core)
    (exchange : updated.exchange.mode = monitor.exchange.mode)
    (forward : updated.exchange.forward = monitor.exchange.forward)
    (book : after.losses.book = core.losses.book)
    (recovery : after.live.senderFlight.recovery = core.live.senderFlight.recovery)
    (gateway : (after.live.gatewayState.gateway.session.lane sender.direction).acknowledged =
      (core.live.gatewayState.gateway.session.lane sender.direction).acknowledged)
    (lowerLane : OriginalLane initial checks next after.live.gatewayState received .lower monitor.exchange.forward.lower)
    (upperLane : OriginalLane initial checks next after.live.gatewayState received .upper monitor.exchange.forward.upper)
    (retry : RetryLane initial checks next after.live.gatewayState sent monitor.exchange.forward.retry)
    (work : ∀ part lane, Work initial checks current location part lane → Work initial checks next target part lane)
    (ack : ∀ lane, AckWork checks core.live lane → AckWork checks after.live lane)
    (sources : CampusTCPTwoProgressReceiptSources.History initial next) : Active after := by
  refine {
    exchange := exchange.trans value.exchange
    mode := by rw [forward]; exact value.mode
    preparing := value.preparing
    nonempty := value.nonempty
    lowerLane := by rw [congrArg (·.lower) forward]; exact lowerLane
    upperLane := by rw [congrArg (·.upper) forward]; exact upperLane
    retry := by rw [congrArg (·.retry) forward]; exact retry
    ack := ?_
    originals := by rw [forward]; exact value.originals
    recovery := by rw [forward]; exact value.recovery
    recoveryHead := by rw [forward]; exact value.recoveryHead
    serial := by rw [forward]; exact value.serial
    ackNonempty := by rw [forward]; exact value.ackNonempty
    ackGateway := by rw [congrArg (·.ack) forward, gateway]; exact value.ackGateway
    waiting := by rw [forward]; exact value.waiting
    runnable := by rw [forward]; exact value.runnable
    originalOpen := by rw [forward]; exact value.originalOpen
    debt := fun part head rest selected => ?_
    upperMissing := by rw [forward, book]; exact value.upperMissing
    zeroAck := by rw [congrArg (·.ack) forward, recovery]; exact value.zeroAck
    sources := sources }
  · rw [congrArg (·.ack) forward]
    cases selected : monitor.exchange.forward.ack with
    | none => exact PUnit.unit
    | some lane =>
      have old : AckWork checks core.live lane := by simpa only [AckState, selected] using value.ack
      exact ack lane old
  · obtain ⟨debt⟩ := value.debt part head rest selected
    exact ⟨debt_frame debt forward book work ack⟩

def Debt.control (debt : Debt core part)
    (value : CampusTCPTransferEnabled.Control current (kind.event cfg) actual)
    (selected : CampusTCPTwoTransferMonitor.controlDemand monitor = some kind)
    (drainless : CampusTCPTwoTransferMonitor.drainTicket current.report.final monitor = none)
    (ordinary : ∀ ns, kind.event cfg ≠ .installCheckpoint ns) :
    Debt (core.control value selected drainless ordinary) part := by
  apply debt_frame debt
    (by rw [CampusTCPTwoTransferControlObserve.control_observe value selected drainless]; rfl)
    (core.control_book value selected drainless ordinary)
    (fun _ _ pending => pending.control value)
  intro lane pending
  cases pending with
  | pending phase queue =>
    exact .pending phase (by rw [core.control_reaction value selected drainless ordinary]; exact queue)
  | ingress path => exact .ingress (CampusTCPTwoTransferPaths.ackIngress_control path value)
  | ticket path located => exact .ticket (path.control value) located
  | link path => exact .link (CampusTCPTwoTransferPaths.ackLink_control path value)

def Active.control (active : Active core)
    (value : CampusTCPTransferEnabled.Control current (kind.event cfg) actual)
    (selected : CampusTCPTwoTransferMonitor.controlDemand monitor = some kind)
    (drainless : CampusTCPTwoTransferMonitor.drainTicket current.report.final monitor = none)
    (ordinary : ∀ ns, kind.event cfg ≠ .installCheckpoint ns) :
    Active (core.control value selected drainless ordinary) := by
  have view := control_view_eq core value selected drainless ordinary
  apply active_frame active
    (by rw [CampusTCPTwoTransferControlObserve.control_observe value selected drainless]; rfl)
    (by rw [CampusTCPTwoTransferControlObserve.control_observe value selected drainless]; rfl)
    (core.control_book value selected drainless ordinary)
    (control_recovery core value selected drainless ordinary) rfl
    (by rw [← view]; exact active.lowerLane.control value ordinary)
    (by rw [← view]; exact active.upperLane.control value ordinary)
    (by rw [← view]; exact active.retry.control value ordinary)
    (fun _ _ pending => pending.control value)
    ?_ ((CampusTCPTwoTransferSources.Frame.control value).receipts active.sources)
  intro lane pending
  cases pending with
  | pending phase queue =>
    exact .pending phase (by rw [core.control_reaction value selected drainless ordinary]; exact queue)
  | ingress path => exact .ingress (CampusTCPTwoTransferPaths.ackIngress_control path value)
  | ticket path located => exact .ticket (path.control value) located
  | link path => exact .link (CampusTCPTwoTransferPaths.ackLink_control path value)

def Debt.install
    {core : Core initial checks routing quantum allowance reverseLower reverseUpper current monitor .primary sent received}
    (debt : Debt core part)
    (value : CampusTCPTransferEnabled.Control current (CampusTCPTwoTransferMonitor.Control.install.event cfg) actual)
    (selected : CampusTCPTwoTransferMonitor.controlDemand monitor = some .install)
    (drainless : CampusTCPTwoTransferMonitor.drainTicket current.report.final monitor = none)
    (installation : InstalledCheckpoint) (present : actual.result.installation = some installation) :
    Debt (core.install value selected drainless installation present) part :=
  debt_frame debt
    (by rw [CampusTCPTwoTransferControlObserve.control_observe value selected drainless]; rfl)
    (core.install_book value selected drainless installation present)
    (fun _ _ pending => pending.install_at value installation present)
    (fun _ pending => AckWork.install core pending value selected drainless installation present)

def Active.install
    {core : Core initial checks routing quantum allowance reverseLower reverseUpper current monitor .primary sent received}
    (active : Active core)
    (value : CampusTCPTransferEnabled.Control current (CampusTCPTwoTransferMonitor.Control.install.event cfg) actual)
    (selected : CampusTCPTwoTransferMonitor.controlDemand monitor = some .install)
    (drainless : CampusTCPTwoTransferMonitor.drainTicket current.report.final monitor = none)
    (installation : InstalledCheckpoint) (present : actual.result.installation = some installation) :
    Active (core.install value selected drainless installation present) :=
  active_frame active
    (by rw [CampusTCPTwoTransferControlObserve.control_observe value selected drainless]; rfl)
    (by rw [CampusTCPTwoTransferControlObserve.control_observe value selected drainless]; rfl)
    (core.install_book value selected drainless installation present)
    (install_recovery core value selected drainless installation present) rfl
    (OriginalLane.install core active.lowerLane value selected drainless installation present)
    (OriginalLane.install core active.upperLane value selected drainless installation present)
    (RetryLane.install core active.retry value selected drainless installation present)
    (fun _ _ pending => pending.install_at value installation present)
    (fun _ pending => AckWork.install core pending value selected drainless installation present)
    ((CampusTCPTwoTransferSources.Frame.control value).receipts active.sources)

end Netlib.Check.CampusTCPTwoTransferPhaseState

namespace Netlib.Check.CampusTCPTwoTransferPreparationState

open Protocol Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart
open CampusTCPTwoTransferNative (Checks Routing)
open CampusTCPTwoTransferLocatedCore (config)

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current : Cut input complete} {sender : Actor} {gateway location : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {checks : Checks cut initial.gatewayState.session.entry} {routing : Routing cut gateway}
variable {quantum allowance : Nat} {reverseLower reverseUpper : List UInt8}
variable {monitor : CampusTCPTwoTransferMonitor.Monitor} {actual : Step input}
variable {kind : CampusTCPTwoTransferMonitor.Control} {first : CampusTCPTwoProgressSender.Original initial .lower}

local notation "cfg" => config initial checks routing quantum allowance reverseLower reverseUpper

def Written.control
    (state : Written initial checks routing quantum allowance reverseLower reverseUpper current monitor location)
    (value : CampusTCPTransferEnabled.Control current (kind.event cfg) actual)
    (selected : CampusTCPTwoTransferMonitor.controlDemand monitor = some kind)
    (drainless : CampusTCPTwoTransferMonitor.drainTicket current.report.final monitor = none)
    (ordinary : ∀ ns, kind.event cfg ≠ .installCheckpoint ns) :
    Written initial checks routing quantum allowance reverseLower reverseUpper value.move.after
      (CampusTCPTwoTransferMonitor.observe cfg monitor actual) location := by
  have observed := CampusTCPTwoTransferControlObserve.control_observe value selected drainless
  exact {
    core := state.core.control value selected drainless ordinary
    exchange := by rw [observed]; exact state.exchange
    mode := by rw [observed]; exact state.mode
    lowerPending := by rw [observed]; exact state.lowerPending
    upperPending := by rw [observed]; exact state.upperPending
    ack := by rw [observed]; exact state.ack
    waiting := by rw [observed]; exact state.waiting
    retry := by rw [observed]; exact state.retry
    retries := by rw [observed]; exact state.retries
    sources := (CampusTCPTwoTransferSources.Frame.control value).receipts state.sources }

def Written.install
    (state : Written initial checks routing quantum allowance reverseLower reverseUpper current monitor .primary)
    (value : CampusTCPTransferEnabled.Control current (CampusTCPTwoTransferMonitor.Control.install.event cfg) actual)
    (selected : CampusTCPTwoTransferMonitor.controlDemand monitor = some .install)
    (drainless : CampusTCPTwoTransferMonitor.drainTicket current.report.final monitor = none)
    (installation : InstalledCheckpoint) (present : actual.result.installation = some installation) :
    Written initial checks routing quantum allowance reverseLower reverseUpper value.move.after
      (CampusTCPTwoTransferMonitor.observe cfg monitor actual) .standby := by
  have observed := CampusTCPTwoTransferControlObserve.control_observe value selected drainless
  exact {
    core := state.core.install value selected drainless installation present
    exchange := by rw [observed]; exact state.exchange
    mode := by rw [observed]; exact state.mode
    lowerPending := by rw [observed]; exact state.lowerPending
    upperPending := by rw [observed]; exact state.upperPending
    ack := by rw [observed]; exact state.ack
    waiting := by rw [observed]; exact state.waiting
    retry := by rw [observed]; exact state.retry
    retries := by rw [observed]; exact state.retries
    sources := (CampusTCPTwoTransferSources.Frame.control value).receipts state.sources }

def PendingUpper.control
    (state : PendingUpper initial checks routing quantum allowance reverseLower reverseUpper current monitor location first)
    (value : CampusTCPTransferEnabled.Control current (kind.event cfg) actual)
    (selected : CampusTCPTwoTransferMonitor.controlDemand monitor = some kind)
    (drainless : CampusTCPTwoTransferMonitor.drainTicket current.report.final monitor = none)
    (ordinary : ∀ ns, kind.event cfg ≠ .installCheckpoint ns) :
    PendingUpper initial checks routing quantum allowance reverseLower reverseUpper value.move.after
      (CampusTCPTwoTransferMonitor.observe cfg monitor actual) location first := by
  have observed := CampusTCPTwoTransferControlObserve.control_observe value selected drainless
  refine {
    core := state.core.control value selected drainless ordinary
    exchange := by rw [observed]; exact state.exchange
    mode := by rw [observed]; exact state.mode
    lowerPath := ?_
    upperPending := by rw [observed]; exact state.upperPending
    ack := by rw [observed]; exact state.ack
    waiting := by rw [observed]; exact state.waiting
    retry := by rw [observed]; exact state.retry
    retries := by rw [observed]; exact state.retries
    sources := (CampusTCPTwoTransferSources.Frame.control value).receipts state.sources }
  have lowerEq := congrArg (fun next => next.exchange.forward.lower) observed
  rw [lowerEq, state.core.control_book value selected drainless ordinary]
  exact state.lowerPath.control value

def PendingUpper.install
    (state : PendingUpper initial checks routing quantum allowance reverseLower reverseUpper current monitor .primary first)
    (value : CampusTCPTransferEnabled.Control current (CampusTCPTwoTransferMonitor.Control.install.event cfg) actual)
    (selected : CampusTCPTwoTransferMonitor.controlDemand monitor = some .install)
    (drainless : CampusTCPTwoTransferMonitor.drainTicket current.report.final monitor = none)
    (installation : InstalledCheckpoint) (present : actual.result.installation = some installation) :
    PendingUpper initial checks routing quantum allowance reverseLower reverseUpper value.move.after
      (CampusTCPTwoTransferMonitor.observe cfg monitor actual) .standby first := by
  have observed := CampusTCPTwoTransferControlObserve.control_observe value selected drainless
  refine {
    core := state.core.install value selected drainless installation present
    exchange := by rw [observed]; exact state.exchange
    mode := by rw [observed]; exact state.mode
    lowerPath := ?_
    upperPending := by rw [observed]; exact state.upperPending
    ack := by rw [observed]; exact state.ack
    waiting := by rw [observed]; exact state.waiting
    retry := by rw [observed]; exact state.retry
    retries := by rw [observed]; exact state.retries
    sources := (CampusTCPTwoTransferSources.Frame.control value).receipts state.sources }
  have lowerEq := congrArg (fun next => next.exchange.forward.lower) observed
  rw [lowerEq, state.core.install_book value selected drainless installation present]
  exact state.lowerPath.control value

end Netlib.Check.CampusTCPTwoTransferPreparationState
