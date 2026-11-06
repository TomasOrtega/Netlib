import Netlib.Check.CampusTCPGapProgressSetup
import Netlib.Check.CampusTCPGapProgressReceiver

/-!
# Current joint state of a held-gap task

Sender, receiver, gateway, and stream facts refer to the same actual cut.
Clock frames preserve all historical operations and source identities.
-/

namespace Netlib.Check.CampusTCPGapProgressState

open Protocol.TCP CampusTCPModel CampusTCPEnabled CampusTCPRoundGuards
open CampusTCPRound (Cut)
open CampusTCPGapProgressStart
open CampusTCPGapProgressPhaseBase (Anchor)

variable {input : Input} {complete : H.Completed input.active input.passive}
  {cut current next : Cut input complete} {sender : Actor} {lower upper : List UInt8}

structure Live (initial : GapInitial cut sender lower upper) (current : Cut input complete)
    (retries : Nat) (released : Bool) where
  anchor : Anchor cut current
  senderFlight : CampusTCPGapProgressSender.Flight initial.flight (endpoint current.endpoints sender) retries
  receiverFacts : CampusTCPGapProgressReceiver.Facts initial (endpoint current.endpoints sender.other) released
  gateway : CampusTCPGapProgressGateway.Current initial.gateway current
  history : CampusTCPGapProgressHistory.History cut current sender.other (lower ++ upper) released

variable {initial : GapInitial cut sender lower upper} {retries : Nat} {released : Bool}

theorem endpoint_guards
    (flight : CampusTCPGapProgressSender.Flight initial.flight (endpoint current.endpoints sender) retries)
    (receiver : CampusTCPGapProgressReceiver.Facts initial (endpoint current.endpoints sender.other) released) :
    Guards current.endpoints := by
  intro actor
  by_cases selected : actor = sender
  · rw [selected]
    exact ⟨flight.coherent, flight.prepared, congrArg Option.isSome flight.runtime⟩
  · have peer : actor = sender.other := by cases actor <;> cases sender <;> simp_all [Actor.other]
    rw [peer]
    exact ⟨receiver.coherent, receiver.prepared, congrArg Option.isSome receiver.runtime⟩

def Live.ofInitial (initial : GapInitial cut sender lower upper)
    (geometry : CampusTCPGapProgressReceiver.Geometry initial) : Live initial cut 0 false :=
  ⟨CampusTCPGapProgressSetup.initial_anchor initial, CampusTCPGapProgressSetup.initial_sender initial,
    CampusTCPGapProgressReceiver.initial_facts initial geometry, CampusTCPGapProgressSetup.initial_gateway initial,
    CampusTCPGapProgressSetup.initial_history initial⟩

def gateway_reframe (gateway : CampusTCPGapProgressGateway.Current initial.gateway current)
    (same : beforeService input next.report.final .standby = beforeService input current.report.final .standby) :
    CampusTCPGapProgressGateway.Current initial.gateway next where
  session := gateway.session
  phase := by rw [same]; exact gateway.phase
  shape := gateway.shape
  observations := by rw [same]; exact gateway.observations
  trackerValid := by rw [same]; exact gateway.trackerValid
  record := gateway.record
  member := by rw [same]; exact gateway.member
  entry := gateway.entry
  confirmed := gateway.confirmed

def Live.clock (live : Live initial current retries released)
    (placement : CampusTCPRecoveryRoundPhaseBase.At current next)
    (timely : Endpoint.AckTimeReady (endpoint current.endpoints sender.other) (endpoint next.endpoints sender.other).now) :
    Live initial next retries released := by
  let flight := live.senderFlight.clock (placement.frame.endpointFrame sender)
  let receiver := live.receiverFacts.clock (placement.frame.endpointFrame sender.other) timely
  refine ⟨⟨endpoint_guards flight receiver, live.anchor.retained.trans placement.retained,
    live.anchor.environment.trans placement.frame.environment.symm⟩, flight, receiver,
    gateway_reframe live.gateway (placement.frame.beforeService .standby), live.history.clock placement⟩

def Live.reindex (live : Live initial current retries released)
    (retained : current.report.steps <+: next.report.steps)
    (environment : CampusTCPRoundEnvironment.environment current.report.final = CampusTCPRoundEnvironment.environment next.report.final)
    (endpoints : ∀ actor, endpoint next.endpoints actor = endpoint current.endpoints actor)
    (operations : applicationSteps next.endpoints sender.other = applicationSteps current.endpoints sender.other)
    (same : beforeService input next.report.final .standby = beforeService input current.report.final .standby) :
    Live initial next retries released := by
  let flight : CampusTCPGapProgressSender.Flight initial.flight (endpoint next.endpoints sender) retries :=
    endpoints sender ▸ live.senderFlight
  let receiver : CampusTCPGapProgressReceiver.Facts initial (endpoint next.endpoints sender.other) released :=
    endpoints sender.other ▸ live.receiverFacts
  exact ⟨⟨endpoint_guards flight receiver, live.anchor.retained.trans retained, live.anchor.environment.trans environment⟩,
    flight, receiver, gateway_reframe live.gateway same, live.history.same operations⟩

end Netlib.Check.CampusTCPGapProgressState
