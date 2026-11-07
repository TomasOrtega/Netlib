import Netlib.Check.CampusTCPTwoTransferWork
import Netlib.Check.CampusTCPTwoTransferLocatedControl

/-!
# Stored packet work through actual checkpoint installation

Installation proves that no pending primary ticket remains.
Ingresses, links, range identities, and queued ACKs retain their original evidence.
-/

namespace Netlib.Check.CampusTCPTwoTransferWork

open Protocol Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart
open CampusTCPTwoTransferNative (Checks Routing)
open CampusTCPTwoTransferLocatedCore (Core config)
open CampusTCPTwoTransferPaths

namespace T
export CampusTCPTransferEnabled (Control)
end T
namespace W
export CampusTCPTwoTransferMonitor (Monitor observe controlDemand drainTicket)
end W

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current : Cut input complete} {sender : Actor} {gateway : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {checks : Checks cut initial.gatewayState.session.entry} {routing : Routing cut gateway}
variable {quantum allowance : Nat} {reverseLower reverseUpper : List UInt8}
variable {monitor : W.Monitor} {sent : CampusTCPTwoProgressSender.Stage initial}
variable {received : CampusTCPTwoProgressReceiver.Stage} {part : CampusTCPTwoProgressSender.Part}
variable {lane : CampusTCPTwoProgressMonitor.Lane} {actual : Step input}

local notation "cfg" => config initial checks routing quantum allowance reverseLower reverseUpper

theorem installation_drained (value : T.Control current (.installCheckpoint executionNS) actual)
    (installation : InstalledCheckpoint) (present : actual.result.installation = some installation) :
    current.report.final.outstanding .primary = 0 := by
  have drained := (CampusTCPTransferFacts.installation_origin actual executionNS value.eventEq installation present).drained
  rw [value.move.beforeEq] at drained
  exact drained

theorem no_primary_pending (value : T.Control current (.installCheckpoint executionNS) actual)
    (installation : InstalledCheckpoint) (present : actual.result.installation = some installation)
    (item : Theory.Outstanding.Item (Ticket input.active input.passive))
    (pending : item ∈ current.report.final.work.pending) (primary : item.value.gateway = .primary) : False := by
  have empty : current.report.final.work.pending.filter (fun item => decide (item.value.gateway = .primary)) = [] :=
    List.length_eq_zero_iff.mp (installation_drained value installation present)
  have selected : item ∈ current.report.final.work.pending.filter (fun item => decide (item.value.gateway = .primary)) :=
    List.mem_filter.mpr ⟨pending, decide_eq_true primary⟩
  rw [empty] at selected
  cases selected

def Work.install_at (work : Work initial checks current .primary part lane)
    (value : T.Control current (.installCheckpoint executionNS) actual)
    (installation : InstalledCheckpoint) (present : actual.result.installation = some installation) :
    Work initial checks value.move.after .standby part lane := by
  cases work with
  | ingress path => exact .ingress (dataIngress_control path value)
  | ticket path selected =>
    exact False.elim (no_primary_pending value installation present path.ticket path.pending
      (path.ticket_gateway.trans selected))
  | link path => exact .link (dataLink_control path value)

def DataWork.install (core : Core initial checks routing quantum allowance reverseLower reverseUpper
    current monitor .primary sent received)
    (work : DataWork initial checks current core.live.gatewayState part lane)
    (value : T.Control current (CampusTCPTwoTransferMonitor.Control.install.event cfg) actual)
    (selected : W.controlDemand monitor = some .install)
    (drainless : W.drainTicket current.report.final monitor = none)
    (installation : InstalledCheckpoint) (present : actual.result.installation = some installation) :
    DataWork initial checks value.move.after
      (core.install value selected drainless installation present).live.gatewayState part lane := by
  cases work with
  | ingress path source => exact .ingress (dataIngress_control path value) (source.retain_steps value.move.retained)
  | ticket path located source =>
    exact False.elim (no_primary_pending value installation present path.ticket path.pending
      (path.ticket_gateway.trans located))
  | link path source covered =>
    refine .link (dataLink_control path value) (source.retain_steps value.move.retained) ?_
    rw [core.install_gateway value selected drainless installation present]
    exact covered

def OriginalLane.install (core : Core initial checks routing quantum allowance reverseLower reverseUpper
    current monitor .primary sent received)
    (work : OriginalLane initial checks current core.live.gatewayState received part lane)
    (value : T.Control current (CampusTCPTwoTransferMonitor.Control.install.event cfg) actual)
    (selected : W.controlDemand monitor = some .install)
    (drainless : W.drainTicket current.report.final monitor = none)
    (installation : InstalledCheckpoint) (present : actual.result.installation = some installation) :
    OriginalLane initial checks value.move.after
      (core.install value selected drainless installation present).live.gatewayState received part lane := by
  cases work with
  | active work missing => exact .active (DataWork.install core work value selected drainless installation present) missing
  | done phase => exact .done phase

def RetryLane.install (core : Core initial checks routing quantum allowance reverseLower reverseUpper
    current monitor .primary sent received)
    (work : RetryLane initial checks current core.live.gatewayState sent lane)
    (value : T.Control current (CampusTCPTwoTransferMonitor.Control.install.event cfg) actual)
    (selected : W.controlDemand monitor = some .install)
    (drainless : W.drainTicket current.report.final monitor = none)
    (installation : InstalledCheckpoint) (present : actual.result.installation = some installation) :
    RetryLane initial checks value.move.after
      (core.install value selected drainless installation present).live.gatewayState sent lane := by
  cases work with
  | active role head rest chosen work =>
    exact .active role head rest chosen (DataWork.install core work value selected drainless installation present)
  | done phase => exact .done phase

def AckWork.install (core : Core initial checks routing quantum allowance reverseLower reverseUpper
    current monitor .primary sent received)
    (work : AckWork checks core.live lane)
    (value : T.Control current (CampusTCPTwoTransferMonitor.Control.install.event cfg) actual)
    (selected : W.controlDemand monitor = some .install)
    (drainless : W.drainTicket current.report.final monitor = none)
    (installation : InstalledCheckpoint) (present : actual.result.installation = some installation) :
    AckWork checks (core.install value selected drainless installation present).live lane := by
  cases work with
  | pending phase queue =>
    apply AckWork.pending phase
    rw [core.install_reaction value selected drainless installation present]
    exact queue
  | ingress path => exact .ingress (ackIngress_control path value)
  | ticket path located =>
    exact False.elim (no_primary_pending value installation present path.ticket path.pending
      (path.ticket_gateway.trans located))
  | link path => exact .link (ackLink_control path value)

def AckState.install (core : Core initial checks routing quantum allowance reverseLower reverseUpper
    current monitor .primary sent received)
    (work : AckState checks core.live monitor.exchange.forward.ack)
    (value : T.Control current (CampusTCPTwoTransferMonitor.Control.install.event cfg) actual)
    (selected : W.controlDemand monitor = some .install)
    (drainless : W.drainTicket current.report.final monitor = none)
    (installation : InstalledCheckpoint) (present : actual.result.installation = some installation) :
    AckState checks (core.install value selected drainless installation present).live
      (W.observe cfg monitor actual).exchange.forward.ack := by
  have same : (W.observe cfg monitor actual).exchange.forward.ack = monitor.exchange.forward.ack := by
    rw [CampusTCPTwoTransferControlObserve.control_observe value selected drainless]
    rfl
  rw [same]
  cases ack : monitor.exchange.forward.ack with
  | none => exact PUnit.unit
  | some lane =>
    have pending : AckWork checks core.live lane := by simpa only [AckState, ack] using work
    exact AckWork.install core pending value selected drainless installation present

end Netlib.Check.CampusTCPTwoTransferWork
