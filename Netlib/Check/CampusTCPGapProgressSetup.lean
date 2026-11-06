import Netlib.Check.CampusTCPGapProgressGateway
import Netlib.Check.CampusTCPGapProgressSender
import Netlib.Check.CampusTCPGapProgressHistory
import Netlib.Check.CampusTCPGapProgressRank

/-!
# Initial obligations at the actual held-gap cut

The monitor starts at the retained lower packet's live link.
Its timer reserve comes from the current sender ledger.
-/

namespace Netlib.Check.CampusTCPGapProgressSetup

open Protocol.TCP CampusTCPModel CampusTCPEnabled CampusTCPRoundGuards
open CampusTCPRound (Cut)
open CampusTCPGapProgressStart

namespace M
export CampusTCPGapProgressMonitor (Config Monitor Demand nextDemand nextAction packetAt reserve)
end M

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut : Cut input complete} {sender : Actor} {lower upper : List UInt8}

def config (initial : GapInitial cut sender lower upper)
    (native : NativeEnv cut initial.gateway.seed.entry) (quantum allowance : Nat) : M.Config where
  sender := sender
  bytes := lower ++ upper
  clientIngress := native.ingress .client
  serverIngress := native.ingress .server
  quantum := quantum
  initialRTO := initial.flight.recovery.rto
  initialRemaining := initial.flight.head.lastAt + initial.flight.recovery.rto - initial.flight.recovery.now
  lossAllowance := allowance

def initialMonitor (initial : GapInitial cut sender lower upper) : M.Monitor :=
  Netlib.Check.CampusTCPGapProgressMonitor.Monitor.initial initial.lowerSource.index initial.selected.serviceIndex initial.selected.packetID

theorem initial_guards (initial : GapInitial cut sender lower upper) : Guards cut.endpoints := by
  intro actor
  cases sender <;> cases actor
  all_goals first
    | exact ⟨initial.flight.coherent, initial.flight.prepared, congrArg Option.isSome initial.flight.runtime⟩
    | exact ⟨initial.receiver.coherent, initial.receiver.prepared, congrArg Option.isSome initial.receiver.runtime⟩

theorem initial_anchor (initial : GapInitial cut sender lower upper) :
    CampusTCPGapProgressPhaseBase.Anchor cut cut :=
  CampusTCPGapProgressPhaseBase.Anchor.refl cut (initial_guards initial)

def initial_sender (initial : GapInitial cut sender lower upper) :
    CampusTCPGapProgressSender.Flight initial.flight (endpoint cut.endpoints sender) 0 :=
  CampusTCPGapProgressSender.initial_flight initial.flight

def initial_gateway (initial : GapInitial cut sender lower upper) :
    CampusTCPGapProgressGateway.Current initial.gateway cut :=
  CampusTCPGapProgressGateway.Current.ofStart initial.gateway

def initial_history (_initial : GapInitial cut sender lower upper) :
    CampusTCPGapProgressHistory.History cut cut sender.other (lower ++ upper) false :=
  CampusTCPGapProgressHistory.History.ofCut cut sender.other (lower ++ upper)

theorem initial_application_source (initial : GapInitial cut sender lower upper) :
    CampusTCPDeliveryEnabled.ApplicationSource initial.selected.served.ticket.value.produced := by
  rw [initial.selected.source, initial.lowerSource.application]
  trivial

theorem initial_action (initial : GapInitial cut sender lower upper)
    (native : NativeEnv cut initial.gateway.seed.entry) (quantum allowance : Nat) :
    M.nextAction (config initial native quantum allowance) cut.report.final (initialMonitor initial) =
      some (.deliver initial.selected.serviceIndex initial.selected.emission.bytes true) := by
  simp only [M.nextAction, initialMonitor, Netlib.Check.CampusTCPGapProgressMonitor.Monitor.initial, CampusTCPRoundMonitor.linkAction,
    bind, Option.bind, initial.selected.stored, initial.selected.emitted, initial.selected.pending, beq_self_eq_true,
    ↓reduceIte]
  rfl

theorem initial_demand (initial : GapInitial cut sender lower upper)
    (native : NativeEnv cut initial.gateway.seed.entry) (quantum allowance : Nat) :
    M.nextDemand (config initial native quantum allowance) cut.report.final (initialMonitor initial) =
      some (if 0 < allowance then
        .resolution (.deliver initial.selected.serviceIndex initial.selected.emission.bytes true) initial.selected.packetID
      else .operation (.deliver initial.selected.serviceIndex initial.selected.emission.bytes true)) := by
  unfold M.nextDemand
  rw [initial_action initial native quantum allowance]
  simp only [initialMonitor, Netlib.Check.CampusTCPGapProgressMonitor.Monitor.initial, Bool.false_eq_true, ↓reduceIte,
    M.packetAt, config, List.length_nil, bind, Option.bind]
  split <;> simp_all

theorem initial_rank_positive (initial : GapInitial cut sender lower upper)
    (native : NativeEnv cut initial.gateway.seed.entry) (quantum allowance : Nat) :
    0 < (initialMonitor initial).rank (config initial native quantum allowance) cut.report.final := by
  rw [initialMonitor, CampusTCPGapProgressMonitor.initial_rank]
  omega

end Netlib.Check.CampusTCPGapProgressSetup
