import Netlib.Check.CampusTCPTwoTransferPaths
import Netlib.Check.CampusTCPTwoTransferAdmission
import Netlib.Check.CampusTCPTwoTransferHandoff

/-!
# Current packet work at the selected gateway location

Stored tickets retain their assignment location.
A current equality selects the gateway that may service them.
-/

namespace Netlib.Check.CampusTCPTwoTransferWork

open Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart
open CampusTCPTwoProgressGatewayAt (ViewAt)
open CampusTCPTwoTransferAdmission (rangeAt)
open CampusTCPTwoTransferNative (Checks)
open CampusTCPTwoTransferState (LiveAt)
open CampusTCPTwoTransferPaths
open CampusTCPTwoProgressReadWriter (SelectedOutput)
open CampusTCPTwoProgressPhaseBase (Arrived)

namespace S
export CampusTCPTwoProgressSender (Part Stage)
end S
namespace R
export CampusTCPTwoProgressReceiver (Stage)
end R
namespace M
export CampusTCPTwoProgressMonitor (Config Lane)
end M

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current next : Cut input complete} {sender : Actor} {gateway location : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {checks : Checks cut initial.gatewayState.session.entry}
variable {part : S.Part} {lane : M.Lane} {sent : S.Stage initial} {timeouts : Nat} {received : R.Stage}

inductive Work (initial : TwoWriteInitial cut sender gateway lower upper)
    (checks : Checks cut initial.gatewayState.session.entry) (current : Cut input complete)
    (location : Gateway) (part : S.Part) (lane : M.Lane) where
  | ingress (path : DataIngress initial current part lane)
  | ticket (path : DataTicket initial checks current part lane) (selected : path.assignedGateway = location)
  | link (path : DataLink initial current part lane)

inductive DataWork (initial : TwoWriteInitial cut sender gateway lower upper)
    (checks : Checks cut initial.gatewayState.session.entry) (current : Cut input complete)
    (view : ViewAt initial current location) (part : S.Part) (lane : M.Lane) where
  | ingress (path : DataIngress initial current part lane) (source : SelectedOutput initial current path.output.produced)
  | ticket (path : DataTicket initial checks current part lane) (selected : path.assignedGateway = location)
      (source : SelectedOutput initial current path.output.produced)
  | link (path : DataLink initial current part lane) (source : SelectedOutput initial current path.served.ticket.value.produced)
      (covered : (rangeAt view part).isSome = true)

inductive OriginalLane (initial : TwoWriteInitial cut sender gateway lower upper)
    (checks : Checks cut initial.gatewayState.session.entry) (current : Cut input complete)
    (view : ViewAt initial current location) (received : R.Stage) (part : S.Part) (lane : M.Lane) where
  | active (work : DataWork initial checks current view part lane) (missing : ¬Arrived received part)
  | done (phase : lane.phase = .done)

inductive RetryLane (initial : TwoWriteInitial cut sender gateway lower upper)
    (checks : Checks cut initial.gatewayState.session.entry) (current : Cut input complete)
    (view : ViewAt initial current location) (sent : S.Stage initial) (lane : M.Lane) where
  | active (part : S.Part) (head : Recovery.Outstanding) (rest : List Recovery.Outstanding)
      (selected : CampusTCPTwoProgressRetry.HeadRange sent part head rest)
      (work : DataWork initial checks current view part lane)
  | done (phase : lane.phase = .done)

inductive AckWork (checks : Checks cut initial.gatewayState.session.entry)
    (live : LiveAt initial current location sent timeouts received) (lane : M.Lane) where
  | pending (phase : lane.phase = .needAck) (queue : live.receiverFacts.reaction.work.pending ≠ [])
  | ingress (path : AckIngress initial current (received.bytes lower upper).length lane)
  | ticket (path : AckTicket initial checks current (received.bytes lower upper).length lane)
      (selected : path.assignedGateway = location)
  | link (path : AckLink initial current (received.bytes lower upper).length lane)

def AckState (checks : Checks cut initial.gatewayState.session.entry)
    (live : LiveAt initial current location sent timeouts received) : Option M.Lane → Type
  | none => PUnit
  | some lane => AckWork checks live lane

variable {view : ViewAt initial current location}

def DataWork.work (value : DataWork initial checks current view part lane) : Work initial checks current location part lane := by
  cases value with
  | ingress path _ => exact .ingress path
  | ticket path selected _ => exact .ticket path selected
  | link path _ _ => exact .link path

theorem Work.not_done (value : Work initial checks current location part lane) : lane.phase ≠ .done := by
  cases value with
  | ingress path => rw [path.phase]; decide
  | ticket path _ => rw [path.phase]; decide
  | link path => rw [path.phase]; decide

theorem Work.not_needSend (value : Work initial checks current location part lane) : lane.phase ≠ .needSend := by
  cases value with
  | ingress path => rw [path.phase]; decide
  | ticket path _ => rw [path.phase]; decide
  | link path => rw [path.phase]; decide

def Work.command (value : Work initial checks current location part lane) (config : M.Config) : CampusTCPRoundMonitor.Action :=
  match value with
  | .ingress path => .assign path.output.index (config.toConfig.ingress config.sender)
  | .ticket path _ => .serve path.ticket.id
  | .link path => .deliver path.index path.emission.bytes true

theorem Work.command_next (value : Work initial checks current location part lane) (config : M.Config) :
    CampusTCPGapProgressMonitor.nextAction config.toConfig current.report.final lane.toGap = some (value.command config) := by
  cases value with
  | ingress path => exact path.action config
  | ticket path _ => exact path.action config
  | link path => exact path.action config

def Work.packetID (value : Work initial checks current location part lane) : Option Nat :=
  match value with
  | .ingress path => some path.packetID
  | .ticket .. => none
  | .link path => some path.packetID

theorem Work.exposed_packet (value : Work initial checks current location part lane) (config : M.Config) :
    CampusTCPTwoProgressMonitor.exposedPacket config current.report.final lane = value.packetID := by
  cases value with
  | ingress path => exact path.exposed_packet config
  | ticket path _ => exact path.exposed_packet config
  | link path => exact path.exposed_packet config

theorem DataWork.not_done (value : DataWork initial checks current view part lane) : lane.phase ≠ .done := value.work.not_done

theorem DataWork.not_needSend (value : DataWork initial checks current view part lane) : lane.phase ≠ .needSend := value.work.not_needSend

def DataWork.command (value : DataWork initial checks current view part lane) (config : M.Config) :
    CampusTCPRoundMonitor.Action := value.work.command config

theorem DataWork.command_next (value : DataWork initial checks current view part lane) (config : M.Config) :
    CampusTCPGapProgressMonitor.nextAction config.toConfig current.report.final lane.toGap = some (value.command config) :=
  value.work.command_next config

theorem DataWork.exposed_packet (value : DataWork initial checks current view part lane) (config : M.Config) :
    CampusTCPTwoProgressMonitor.exposedPacket config current.report.final lane = value.work.packetID :=
  value.work.exposed_packet config

theorem OriginalLane.not_needSend (value : OriginalLane initial checks current view received part lane) : lane.phase ≠ .needSend := by
  cases value with
  | active work _ => exact work.not_needSend
  | done phase => rw [phase]; decide

def OriginalLane.work (value : OriginalLane initial checks current view received part lane) (pending : lane.phase ≠ .done) :
    Work initial checks current location part lane := by
  cases value with
  | active work _ => exact work.work
  | done phase => exact False.elim (pending phase)

def OriginalLane.dataWork (value : OriginalLane initial checks current view received part lane) (pending : lane.phase ≠ .done) :
    DataWork initial checks current view part lane := by
  cases value with
  | active work _ => exact work
  | done phase => exact False.elim (pending phase)

theorem RetryLane.not_needSend (value : RetryLane initial checks current view sent lane) : lane.phase ≠ .needSend := by
  cases value with
  | active _ _ _ _ work => exact work.not_needSend
  | done phase => rw [phase]; decide

def RetryLane.work (value : RetryLane initial checks current view sent lane) (pending : lane.phase ≠ .done)
    {head : Recovery.Outstanding} {rest : List Recovery.Outstanding}
    (selected : CampusTCPTwoProgressRetry.HeadRange sent part head rest) : Work initial checks current location part lane := by
  cases value with
  | active role head rest chosen work =>
    have same : role = part := by cases chosen <;> cases selected <;> rfl
    subst role
    exact work.work
  | done phase => exact False.elim (pending phase)

variable {live : LiveAt initial current location sent timeouts received}

theorem AckWork.not_done (value : AckWork checks live lane) : lane.phase ≠ .done := by
  cases value with
  | pending phase _ => rw [phase]; decide
  | ingress path => rw [path.phase]; decide
  | ticket path _ => rw [path.phase]; decide
  | link path => rw [path.phase]; decide

theorem AckWork.not_needSend (value : AckWork checks live lane) : lane.phase ≠ .needSend := by
  cases value with
  | pending phase _ => rw [phase]; decide
  | ingress path => rw [path.phase]; decide
  | ticket path _ => rw [path.phase]; decide
  | link path => rw [path.phase]; decide

def AckWork.command (value : AckWork checks live lane) (config : M.Config) : CampusTCPRoundMonitor.Action :=
  match value with
  | .pending .. => .emitAck config.sender.other true
  | .ingress path => .assign path.output.index (config.toConfig.ingress config.sender.other)
  | .ticket path _ => .serve path.ticket.id
  | .link path => .deliver path.index path.emission.bytes true

theorem AckWork.command_next (value : AckWork checks live lane) (config : M.Config) :
    CampusTCPGapProgressMonitor.nextAction config.toConfig current.report.final lane.toGap = some (value.command config) := by
  cases value with
  | pending phase _ => simp only [CampusTCPGapProgressMonitor.nextAction, CampusTCPTwoProgressMonitor.Lane.toGap, phase]; rfl
  | ingress path => exact path.action config
  | ticket path _ => exact path.action config
  | link path => exact path.action config

def AckWork.packetID (value : AckWork checks live lane) : Option Nat :=
  match value with
  | .pending .. | .ticket .. => none
  | .ingress path => some path.packetID
  | .link path => some path.packetID

theorem AckWork.exposed_packet (value : AckWork checks live lane) (config : M.Config) :
    CampusTCPTwoProgressMonitor.exposedPacket config current.report.final lane = value.packetID := by
  cases value with
  | pending phase _ => simp only [CampusTCPTwoProgressMonitor.exposedPacket, CampusTCPGapProgressMonitor.nextAction,
      CampusTCPGapProgressMonitor.packetAt, CampusTCPTwoProgressMonitor.Lane.toGap, phase, bind, Option.bind]; rfl
  | ingress path => exact path.exposed_packet config
  | ticket path _ => exact path.exposed_packet config
  | link path => exact path.exposed_packet config

def Work.clock (value : Work initial checks current location part lane)
    (placement : CampusTCPRecoveryRoundPhaseBase.At current next) : Work initial checks next location part lane := by
  cases value with
  | ingress path => exact .ingress (path.clock placement)
  | ticket path selected => exact .ticket (path.clock placement) selected
  | link path => exact .link (path.clock placement)

def DataWork.clock (value : DataWork initial checks current view part lane)
    (placement : CampusTCPRecoveryRoundPhaseBase.At current next) :
    DataWork initial checks next (view.reframe (placement.frame.beforeService location)) part lane := by
  cases value with
  | ingress path source => exact .ingress (path.clock placement) (source.clock placement)
  | ticket path selected source => exact .ticket (path.clock placement) selected (source.clock placement)
  | link path source covered => exact .link (path.clock placement) (source.clock placement) covered

def OriginalLane.clock (value : OriginalLane initial checks current view received part lane)
    (placement : CampusTCPRecoveryRoundPhaseBase.At current next) :
    OriginalLane initial checks next (view.reframe (placement.frame.beforeService location)) received part lane := by
  cases value with
  | active work missing => exact .active (work.clock placement) missing
  | done phase => exact .done phase

def RetryLane.clock (value : RetryLane initial checks current view sent lane)
    (placement : CampusTCPRecoveryRoundPhaseBase.At current next) :
    RetryLane initial checks next (view.reframe (placement.frame.beforeService location)) sent lane := by
  cases value with
  | active role head rest selected work => exact .active role head rest selected (work.clock placement)
  | done phase => exact .done phase

def AckWork.clock (value : AckWork checks live lane)
    (placement : CampusTCPRecoveryRoundPhaseBase.At current next)
    (senderTimely : Endpoint.AckTimeReady (endpoint current.endpoints sender) (endpoint next.endpoints sender).now)
    (receiverTimely : Endpoint.AckTimeReady (endpoint current.endpoints sender.other) (endpoint next.endpoints sender.other).now) :
    AckWork checks (live.clock placement senderTimely receiverTimely) lane := by
  cases value with
  | pending phase queue => exact .pending phase queue
  | ingress path => exact .ingress (path.clock placement)
  | ticket path selected => exact .ticket (path.clock placement) selected
  | link path => exact .link (path.clock placement)

variable {actual : Step input} {event : CampusTCPModel.Event}

private theorem control_before (value : CampusTCPTransferEnabled.Control current event actual)
    (ordinary : ∀ ns, event ≠ .installCheckpoint ns) (location : Gateway) :
    beforeService input value.move.after.report.final location = beforeService input current.report.final location := by
  cases location <;> simp only [beforeService, State.resident, value.frame.authentication,
    value.frame.primary, value.frame.standby ordinary]

def control_view (view : ViewAt initial current location)
    (value : CampusTCPTransferEnabled.Control current event actual)
    (ordinary : ∀ ns, event ≠ .installCheckpoint ns) : ViewAt initial value.move.after location :=
  view.reframe (control_before value ordinary location)

def Work.control (value : Work initial checks current location part lane)
    (control : CampusTCPTransferEnabled.Control current event actual) :
    Work initial checks control.move.after location part lane := by
  cases value with
  | ingress path => exact .ingress (dataIngress_control path control)
  | ticket path selected => exact .ticket (path.control control) selected
  | link path => exact .link (dataLink_control path control)

def DataWork.control (value : DataWork initial checks current view part lane)
    (control : CampusTCPTransferEnabled.Control current event actual)
    (ordinary : ∀ ns, event ≠ .installCheckpoint ns) :
    DataWork initial checks control.move.after (control_view view control ordinary) part lane := by
  cases value with
  | ingress path source => exact .ingress (dataIngress_control path control) (source.retain_steps control.move.retained)
  | ticket path selected source => exact .ticket (path.control control) selected (source.retain_steps control.move.retained)
  | link path source covered => exact .link (dataLink_control path control) (source.retain_steps control.move.retained) covered

def OriginalLane.control (value : OriginalLane initial checks current view received part lane)
    (control : CampusTCPTransferEnabled.Control current event actual)
    (ordinary : ∀ ns, event ≠ .installCheckpoint ns) :
    OriginalLane initial checks control.move.after (control_view view control ordinary) received part lane := by
  cases value with
  | active work missing => exact .active (work.control control ordinary) missing
  | done phase => exact .done phase

def RetryLane.control (value : RetryLane initial checks current view sent lane)
    (control : CampusTCPTransferEnabled.Control current event actual)
    (ordinary : ∀ ns, event ≠ .installCheckpoint ns) :
    RetryLane initial checks control.move.after (control_view view control ordinary) sent lane := by
  cases value with
  | active role head rest selected work => exact .active role head rest selected (work.control control ordinary)
  | done phase => exact .done phase

private theorem control_reaction (live : LiveAt initial current location sent timeouts received)
    (control : CampusTCPTransferEnabled.Control current event actual)
    (ordinary : ∀ ns, event ≠ .installCheckpoint ns) :
    (CampusTCPTwoTransferHandoff.control_live live control ordinary).receiverFacts.reaction = live.receiverFacts.reaction := by
  apply Option.some.inj
  have same := congrArg (fun endpoints => (endpoint endpoints sender.other).ackReaction) control.endpoints
  exact (CampusTCPTwoTransferHandoff.control_live live control ordinary).receiverFacts.ackRuntime.symm.trans
    (same.trans live.receiverFacts.ackRuntime)

def AckWork.control (value : AckWork checks live lane)
    (control : CampusTCPTransferEnabled.Control current event actual)
    (ordinary : ∀ ns, event ≠ .installCheckpoint ns) :
    AckWork checks (CampusTCPTwoTransferHandoff.control_live live control ordinary) lane := by
  cases value with
  | pending phase queue =>
    apply AckWork.pending phase
    rw [control_reaction live control ordinary]
    exact queue
  | ingress path => exact .ingress (ackIngress_control path control)
  | ticket path selected => exact .ticket (path.control control) selected
  | link path => exact .link (ackLink_control path control)

end Netlib.Check.CampusTCPTwoTransferWork
