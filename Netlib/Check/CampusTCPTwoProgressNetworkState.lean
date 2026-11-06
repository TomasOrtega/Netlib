import Netlib.Check.CampusTCPTwoProgressState
import Netlib.Check.CampusTCPTwoProgressNetwork
import Netlib.Check.CampusTCPTwoProgressClock
import Netlib.Check.CampusTCPRecoveryRoundDrop

/-!
# Joint state through network and clock moves

The actual moves retain endpoint histories and range sources.
Clock guards supply both endpoint time obligations.
-/

namespace Netlib.Check.CampusTCPTwoProgressNetworkState

open Protocol.TCP CampusTCPModel CampusTCPEnabled CampusTCPRoundGuards
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart CampusTCPTwoProgressState

variable {input : Input} {complete : TCPHandshake.Completed input.active input.passive}
variable {cut current : Cut input complete} {sender : Actor} {gateway : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {sent : CampusTCPTwoProgressSender.Stage initial} {timeouts : Nat} {received : CampusTCPTwoProgressReceiver.Stage}
variable {actual : Step input}
variable {id : Nat}

theorem prepared_time (state : Endpoint.State) (prepared : Endpoint.AckPrepared state) : Endpoint.AckTimeReady state state.now := by
  intro reaction runtime
  have work := prepared.2
  rw [runtime] at work
  exact work.1

theorem clock_time (clocked : CampusTCPTwoProgressClock.Clocked cut current config monitor actor millis actual)
    (guards : Guards current.endpoints)
    (allowed : CampusTCPTwoProgressMonitor.Allowed config current.report.final monitor (.advanceClock actor millis))
    (receiver : Actor) :
    Endpoint.AckTimeReady (endpoint current.endpoints receiver) (endpoint clocked.move.after.endpoints receiver).now := by
  by_cases selected : receiver = actor
  · subst receiver
    obtain ⟨recovery, runtime, _, _, timely⟩ := CampusTCPGapProgressClock.clock_allowed_fields config.toConfig current actor millis
      (CampusTCPTwoProgressClock.allowed_guard config current monitor actor millis allowed)
    rw [clocked.selected]
    simpa only [Endpoint.clockState, Endpoint.State.now, runtime, Option.map_some, Option.getD_some] using timely
  · have peer : receiver = actor.other := by cases receiver <;> cases actor <;> simp_all [Actor.other]
    rw [peer, clocked.peer]
    exact prepared_time _ (guards actor.other).prepared

def clock_live (live : Live initial current sent timeouts received)
    (clocked : CampusTCPTwoProgressClock.Clocked cut current config monitor actor millis actual)
    (allowed : CampusTCPTwoProgressMonitor.Allowed config current.report.final monitor (.advanceClock actor millis)) :
    Live initial clocked.move.after sent timeouts received :=
  live.clock clocked.placement (clock_time clocked live.anchor.guards allowed sender)
    (clock_time clocked live.anchor.guards allowed sender.other)

def assignment_live (live : Live initial current sent timeouts received)
    (assigned : CampusTCPTwoProgressNetwork.AssignmentMove initial current index ingress produced actual) :
    Live initial assigned.move.after sent timeouts received := by
  apply live.reindex assigned.move.retained assigned.environment
  · intro actor
    rw [assigned.endpoints]
  · rw [assigned.endpoints]
  · exact assigned.serviceFrame gateway

def drop_live (live : Live initial current sent timeouts received)
    (appended : CampusTCPRecoveryRoundDrop.Append current id actual) :
    Live initial appended.move.after sent timeouts received := by
  apply live.reindex appended.move.retained
  · rw [appended.move.final, appended.facts.environment]
  · intro actor
    rw [appended.endpoints]
  · rw [appended.endpoints]
  · rw [appended.move.final]
    exact appended.facts.beforeService gateway

variable {item : Theory.Outstanding.Item (Ticket input.active input.passive)}
variable {hit : Protocol.FlowNAT.Hit} {session : Admission.Session} {served : Served input}
variable {emission : WireForwarding.Emission served.ticket.value.source.packet} {emitted : served.evidence.output = some emission}

def service_live (live : Live initial current sent timeouts received)
    (value : CampusTCPTwoProgressNetwork.ServiceMove initial current item hit session actual served emission emitted)
    (view : CampusTCPTwoProgressGatewayState.View initial value.move.after)
    (space : CampusTCPTwoProgressGatewayWindow.Reserved view) :
    Live initial value.move.after sent timeouts received := by
  refine ⟨value.anchor, ?_, ?_, view, space, ?_⟩
  · rw [value.endpoints]
    exact live.senderFlight
  · rw [value.endpoints]
    exact live.receiverFacts
  · exact live.history.same (by rw [value.endpoints])

end Netlib.Check.CampusTCPTwoProgressNetworkState
