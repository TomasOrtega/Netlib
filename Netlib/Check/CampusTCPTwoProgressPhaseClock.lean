import Netlib.Check.CampusTCPTwoProgressPhaseState

namespace Netlib.Check.CampusTCPTwoProgressPhaseState

open Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart
open CampusTCPTwoProgressPhaseBase (Core)
open CampusTCPTwoProgressSetup (config)

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current : Cut input complete} {sender : Actor} {gateway : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {native : NativeEnv cut gateway initial.gatewayState.session.entry} {quantum allowance : Nat}
variable {monitor : M.Monitor} {sent : S.Stage initial} {received : R.Stage}
variable {core : Core initial native quantum allowance current monitor sent received}
variable {part : S.Part} {lane : M.Lane} {actor : Actor} {millis : Nat} {actual : Step input}

theorem clock_sender_recovery (core : Core initial native quantum allowance current monitor sent received)
    (clocked : CampusTCPTwoProgressClock.Clocked cut current
      (config initial native quantum allowance) monitor actor millis actual)
    (allowed : CampusTCPTwoProgressMonitor.Allowed (config initial native quantum allowance)
      current.report.final monitor (.advanceClock actor millis)) :
    (core.clock clocked allowed).live.senderFlight.recovery =
      { core.live.senderFlight.recovery with now := (endpoint clocked.move.after.endpoints sender).now } := by
  apply Option.some.inj
  exact (core.clock clocked allowed).live.senderFlight.runtime.symm.trans
    ((clocked.placement.frame.endpointFrame sender).runtime core.live.senderFlight.runtime)

theorem clock_receiver_reaction (core : Core initial native quantum allowance current monitor sent received)
    (clocked : CampusTCPTwoProgressClock.Clocked cut current
      (config initial native quantum allowance) monitor actor millis actual)
    (allowed : CampusTCPTwoProgressMonitor.Allowed (config initial native quantum allowance)
      current.report.final monitor (.advanceClock actor millis)) :
    (core.clock clocked allowed).live.receiverFacts.reaction = core.live.receiverFacts.reaction := by
  apply Option.some.inj
  exact (core.clock clocked allowed).live.receiverFacts.ackRuntime.symm.trans
    ((clocked.placement.frame.endpointFrame sender.other).ackReaction.trans core.live.receiverFacts.ackRuntime)

theorem clock_duplicates (core : Core initial native quantum allowance current monitor sent received)
    (clocked : CampusTCPTwoProgressClock.Clocked cut current
      (config initial native quantum allowance) monitor actor millis actual)
    (allowed : CampusTCPTwoProgressMonitor.Allowed (config initial native quantum allowance)
      current.report.final monitor (.advanceClock actor millis)) :
    (core.clock clocked allowed).live.senderFlight.recovery.duplicateAcks = core.live.senderFlight.recovery.duplicateAcks := by
  rw [clock_sender_recovery core clocked allowed]

def DataWork.clock (value : DataWork initial native current core.live.gatewayState part lane)
    (clocked : CampusTCPTwoProgressClock.Clocked cut current
      (config initial native quantum allowance) monitor actor millis actual)
    (allowed : CampusTCPTwoProgressMonitor.Allowed (config initial native quantum allowance)
      current.report.final monitor (.advanceClock actor millis)) :
    DataWork initial native clocked.move.after (core.clock clocked allowed).live.gatewayState part lane := by
  cases value with
  | ingress path source => exact .ingress (path.clock clocked.placement) (source.clock clocked.placement)
  | ticket path source => exact .ticket (path.clock clocked.placement) (source.clock clocked.placement)
  | link path source covered => exact .link (path.clock clocked.placement) (source.clock clocked.placement) covered

def OriginalLane.clock (value : OriginalLane initial native current core.live.gatewayState received part lane)
    (clocked : CampusTCPTwoProgressClock.Clocked cut current
      (config initial native quantum allowance) monitor actor millis actual)
    (allowed : CampusTCPTwoProgressMonitor.Allowed (config initial native quantum allowance)
      current.report.final monitor (.advanceClock actor millis)) :
    OriginalLane initial native clocked.move.after (core.clock clocked allowed).live.gatewayState received part lane := by
  cases value with
  | active work missing => exact .active (work.clock clocked allowed) missing
  | done phase => exact .done phase

def RetryLane.clock (value : RetryLane initial native current core.live.gatewayState sent lane)
    (clocked : CampusTCPTwoProgressClock.Clocked cut current
      (config initial native quantum allowance) monitor actor millis actual)
    (allowed : CampusTCPTwoProgressMonitor.Allowed (config initial native quantum allowance)
      current.report.final monitor (.advanceClock actor millis)) :
    RetryLane initial native clocked.move.after (core.clock clocked allowed).live.gatewayState sent lane := by
  cases value with
  | active role head rest selected work => exact .active role head rest selected (work.clock clocked allowed)
  | done phase => exact .done phase

def AckWork.clock (value : AckWork core lane)
    (clocked : CampusTCPTwoProgressClock.Clocked cut current
      (config initial native quantum allowance) monitor actor millis actual)
    (allowed : CampusTCPTwoProgressMonitor.Allowed (config initial native quantum allowance)
      current.report.final monitor (.advanceClock actor millis)) : AckWork (core.clock clocked allowed) lane := by
  cases value with
  | pending phase queue =>
    apply AckWork.pending phase
    rw [clock_receiver_reaction core clocked allowed]
    exact queue
  | ingress path => exact .ingress (path.clock clocked.placement)
  | ticket path => exact .ticket (path.clock clocked.placement)
  | link path => exact .link (path.clock clocked.placement)

def AckState.clock (value : AckState core)
    (clocked : CampusTCPTwoProgressClock.Clocked cut current
      (config initial native quantum allowance) monitor actor millis actual)
    (allowed : CampusTCPTwoProgressMonitor.Allowed (config initial native quantum allowance)
      current.report.final monitor (.advanceClock actor millis)) : AckState (core.clock clocked allowed) := by
  cases selected : monitor.ack with
  | none => simpa only [AckState, selected] using PUnit.unit
  | some lane =>
    have work : AckWork core lane := by simpa only [AckState, selected] using value
    simpa only [AckState, selected] using work.clock clocked allowed

def Active.clock (value : Active core)
    (clocked : CampusTCPTwoProgressClock.Clocked cut current
      (config initial native quantum allowance) monitor actor millis actual)
    (allowed : CampusTCPTwoProgressMonitor.Allowed (config initial native quantum allowance)
      current.report.final monitor (.advanceClock actor millis)) : Active (core.clock clocked allowed) where
  mode := value.mode
  preparing := value.preparing
  nonempty := value.nonempty
  lowerLane := value.lowerLane.clock clocked allowed
  upperLane := value.upperLane.clock clocked allowed
  retry := value.retry.clock clocked allowed
  ack := value.ack.clock clocked allowed
  originals := value.originals
  recovery := value.recovery
  recoveryHead := value.recoveryHead
  serial := value.serial
  ackNonempty := value.ackNonempty
  ackGateway := value.ackGateway
  waiting := value.waiting
  runnable := value.runnable
  originalOpen := value.originalOpen
  debt := fun role head rest selected => by
    obtain ⟨debt⟩ := value.debt role head rest selected
    exact ⟨debt.clock clocked allowed⟩
  zeroAck := fun lane selected coordinate => by
    rw [clock_sender_recovery core clocked allowed]
    exact value.zeroAck lane selected coordinate
  upperMissing := value.upperMissing
  sources := value.sources.clock clocked

end Netlib.Check.CampusTCPTwoProgressPhaseState
