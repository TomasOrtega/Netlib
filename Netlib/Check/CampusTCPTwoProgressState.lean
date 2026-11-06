import Netlib.Check.CampusTCPTwoProgressSetup
import Netlib.Check.CampusTCPTwoProgressSender
import Netlib.Check.CampusTCPTwoProgressReceiver
import Netlib.Check.CampusTCPTwoProgressGatewayWindow

/-!
# Current joint state of the two-record task

Endpoint, gateway, and stream facts refer to the same retained cut.
The sender stage and receiver stage can progress at different times.
-/

namespace Netlib.Check.CampusTCPTwoProgressState

open Protocol.TCP CampusTCPModel CampusTCPEnabled CampusTCPRoundGuards
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart
open CampusTCPGapProgressPhaseBase (Anchor)

namespace S
export CampusTCPTwoProgressSender (Stage Flight initial_flight)
end S
namespace R
export CampusTCPTwoProgressReceiver (Stage Facts initial_facts)
end R
namespace G
export CampusTCPTwoProgressGatewayState (View)
export CampusTCPTwoProgressGatewayWindow (Reserved)
end G
namespace H
export CampusTCPTwoProgressHistory (History)
end H

variable {input : Input} {complete : TCPHandshake.Completed input.active input.passive}
variable {cut current next : Cut input complete} {sender : Actor} {gateway : Gateway} {lower upper : List UInt8}

structure Live (initial : TwoWriteInitial cut sender gateway lower upper) (current : Cut input complete)
    (sent : S.Stage initial) (timeouts : Nat) (received : R.Stage) where
  anchor : Anchor cut current
  senderFlight : S.Flight initial (endpoint current.endpoints sender) sent timeouts
  receiverFacts : R.Facts initial (endpoint current.endpoints sender.other) received
  gatewayState : G.View initial current
  gatewayWindow : G.Reserved gatewayState
  history : H.History cut current sender.other (lower ++ upper) (received.bytes lower upper)

variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {sent : S.Stage initial} {timeouts : Nat} {received : R.Stage}

theorem endpoint_guards
    (flight : S.Flight initial (endpoint current.endpoints sender) sent timeouts)
    (receiver : R.Facts initial (endpoint current.endpoints sender.other) received) : Guards current.endpoints := by
  intro actor
  by_cases selected : actor = sender
  · rw [selected]
    exact ⟨flight.coherent, flight.prepared, congrArg Option.isSome flight.runtime⟩
  · have peer : actor = sender.other := by cases actor <;> cases sender <;> simp_all [Actor.other]
    rw [peer]
    exact ⟨receiver.coherent, receiver.prepared, congrArg Option.isSome receiver.runtime⟩

def Live.ofInitial (initial : TwoWriteInitial cut sender gateway lower upper) : Live initial cut .written 0 .empty :=
  ⟨CampusTCPTwoProgressSetup.initial_anchor initial, S.initial_flight initial, R.initial_facts initial,
    CampusTCPTwoProgressGatewayState.View.ofInitial initial,
    CampusTCPTwoProgressGatewayWindow.initial_reserved initial, CampusTCPTwoProgressSetup.initial_history initial⟩

def Live.clock (live : Live initial current sent timeouts received)
    (placement : CampusTCPRecoveryRoundPhaseBase.At current next)
    (senderTimely : Endpoint.AckTimeReady (endpoint current.endpoints sender) (endpoint next.endpoints sender).now)
    (receiverTimely : Endpoint.AckTimeReady (endpoint current.endpoints sender.other) (endpoint next.endpoints sender.other).now) :
    Live initial next sent timeouts received := by
  let flight := live.senderFlight.clock (placement.frame.endpointFrame sender) senderTimely
  let receiver := live.receiverFacts.clock (placement.frame.endpointFrame sender.other) receiverTimely
  exact ⟨⟨endpoint_guards flight receiver, live.anchor.retained.trans placement.retained,
    live.anchor.environment.trans placement.frame.environment.symm⟩, flight, receiver,
    live.gatewayState.reframe (placement.frame.beforeService gateway), live.gatewayWindow, live.history.clock placement⟩

def Live.reindex (live : Live initial current sent timeouts received)
    (retained : current.report.steps <+: next.report.steps)
    (environment : CampusTCPRoundEnvironment.environment current.report.final = CampusTCPRoundEnvironment.environment next.report.final)
    (endpoints : ∀ actor, endpoint next.endpoints actor = endpoint current.endpoints actor)
    (operations : applicationSteps next.endpoints sender.other = applicationSteps current.endpoints sender.other)
    (same : beforeService input next.report.final gateway = beforeService input current.report.final gateway) :
    Live initial next sent timeouts received := by
  let flight : S.Flight initial (endpoint next.endpoints sender) sent timeouts := by
    rw [endpoints sender]
    exact live.senderFlight
  let receiver : R.Facts initial (endpoint next.endpoints sender.other) received := by
    rw [endpoints sender.other]
    exact live.receiverFacts
  exact ⟨⟨endpoint_guards flight receiver, live.anchor.retained.trans retained, live.anchor.environment.trans environment⟩,
    flight, receiver, live.gatewayState.reframe same, live.gatewayWindow, live.history.same operations⟩

end Netlib.Check.CampusTCPTwoProgressState
