import Netlib.Check.CampusTCPTwoProgressPhaseSend
import Netlib.Check.CampusTCPTwoProgressPathsAssign
import Netlib.Check.CampusTCPTwoProgressPathsService

/-!
# Literal original packets on their current paths

The source is the actual original send operation and packet.
Equal packet fields alone do not establish that source.
-/

namespace Netlib.Check.CampusTCPTwoProgressOriginalPath

open Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart
open CampusTCPTwoProgressPhaseBase (Core)
open CampusTCPTwoProgressPaths

namespace S
export CampusTCPTwoProgressSender (Part Original Stage)
end S
namespace M
export CampusTCPTwoProgressMonitor (Lane Monitor)
end M

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current next : Cut input complete} {sender : Actor} {gateway : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {native : NativeEnv cut gateway initial.gatewayState.session.entry}
variable {part : S.Part} {original : S.Original initial part} {lane other : M.Lane}

def source (original : S.Original initial part) : Produced input.active input.passive :=
  .application sender original.operation original.packet original.origin

inductive InFlight (initial : TwoWriteInitial cut sender gateway lower upper)
    (native : NativeEnv cut gateway initial.gatewayState.session.entry) (current : Cut input complete)
    (part : S.Part) (original : S.Original initial part) (lane : M.Lane) where
  | ingress (path : DataIngress initial current part lane) (produced : path.output.produced = source original)
  | ticket (path : DataTicket initial native current part lane) (produced : path.output.produced = source original)
  | link (path : DataLink initial current part lane) (produced : path.served.ticket.value.produced = source original)

def InFlight.clock (path : InFlight initial native current part original lane)
    (placement : CampusTCPRecoveryRoundPhaseBase.At current next) : InFlight initial native next part original lane := by
  cases path with
  | ingress path produced => exact .ingress (path.clock placement) produced
  | ticket path produced => exact .ticket (path.clock placement) produced
  | link path produced => exact .link (path.clock placement) produced

def InFlight.reindex (path : InFlight initial native current part original lane) (same : other = lane) :
    InFlight initial native current part original other := by
  cases path with
  | ingress path produced => exact .ingress (path.reindex same) produced
  | ticket path produced => exact .ticket (path.reindex same) produced
  | link path produced => exact .link (path.reindex same) produced

theorem InFlight.not_done (path : InFlight initial native current part original lane) : lane.phase ≠ .done := by
  cases path with
  | ingress path _ => rw [path.phase]; decide
  | ticket path _ => rw [path.phase]; decide
  | link path _ => rw [path.phase]; decide

theorem InFlight.action (path : InFlight initial native current part original lane)
    (config : CampusTCPTwoProgressMonitor.Config) :
    ∃ action, CampusTCPGapProgressMonitor.nextAction config.toConfig current.report.final lane.toGap = some action := by
  cases path with
  | ingress path _ => exact ⟨_, path.action config⟩
  | ticket path _ => exact ⟨_, path.action config⟩
  | link path _ => exact ⟨_, path.action config⟩

theorem InFlight.demand (path : InFlight initial native current part original lane)
    (config : CampusTCPTwoProgressMonitor.Config) (monitor : M.Monitor) :
    (CampusTCPTwoProgressMonitor.laneDemand config current.report.final monitor lane).isSome = true := by
  obtain ⟨action, selected⟩ := path.action config
  simp only [CampusTCPTwoProgressMonitor.laneDemand, selected, bind, Option.bind]
  cases CampusTCPGapProgressMonitor.packetAt lane.toGap with
  | none => rfl
  | some value =>
    dsimp only
    split <;> rfl

variable {quantum allowance : Nat} {monitor : M.Monitor} {actual : Step input}
variable {sent : S.Stage initial} {received : CampusTCPTwoProgressReceiver.Stage} {timeouts : Nat}

theorem first_source {core : Core initial native quantum allowance current monitor .written .empty}
    (sent : CampusTCPTwoProgressPhaseSend.First core actual) :
    sent.path.output.produced = source sent.value.original := by
  have selected := congrArg (fun state : M.Monitor => state.lower.refs.dataOutput) sent.observed
  have index := Option.some.inj (sent.path.outputRef.symm.trans selected)
  have stored := sent.path.output.stored
  rw [index] at stored
  exact (Option.some.inj (stored.symm.trans sent.value.facts.source)).trans sent.value.production

def first {core : Core initial native quantum allowance current monitor .written .empty}
    (sent : CampusTCPTwoProgressPhaseSend.First core actual) :
    InFlight initial native sent.value.facts.move.after .lower sent.value.original
      (CampusTCPTwoProgressMonitor.observe (CampusTCPTwoProgressSetup.config initial native quantum allowance) monitor actual).lower :=
  .ingress sent.path (first_source sent)

theorem second_source {first : S.Original initial .lower}
    {core : Core initial native quantum allowance current monitor (.lower first) .empty}
    (sent : CampusTCPTwoProgressPhaseSend.Second core actual) :
    sent.path.output.produced = source sent.value.original := by
  have selected := congrArg (fun state : M.Monitor => state.upper.refs.dataOutput) sent.observed
  have index := Option.some.inj (sent.path.outputRef.symm.trans selected)
  have stored := sent.path.output.stored
  rw [index] at stored
  exact (Option.some.inj (stored.symm.trans sent.value.facts.source)).trans sent.value.production

def second {first : S.Original initial .lower}
    {core : Core initial native quantum allowance current monitor (.lower first) .empty}
    (sent : CampusTCPTwoProgressPhaseSend.Second core actual) :
    InFlight initial native sent.value.facts.move.after .upper sent.value.original
      (CampusTCPTwoProgressMonitor.observe (CampusTCPTwoProgressSetup.config initial native quantum allowance) monitor actual).upper :=
  .ingress sent.path (second_source sent)

def assigned {live : CampusTCPTwoProgressState.Live initial current sent timeouts received}
    {path : DataIngress initial current part lane} (produced : path.output.produced = source original)
    (value : CampusTCPTwoProgressPathsAssign.DataAssigned live path native actual) :
    InFlight initial native value.value.move.after part original value.nextLane :=
  .ticket value.ticket (value.ticketProduced.trans produced)

def served {live : CampusTCPTwoProgressState.Live initial current sent timeouts received}
    {path : DataTicket initial native current part lane} (produced : path.output.produced = source original)
    (value : CampusTCPTwoProgressPathsService.DataServed live path actual) :
    InFlight initial native value.value.move.after part original value.nextLane :=
  .link value.link (value.linkProduced.trans produced)

end Netlib.Check.CampusTCPTwoProgressOriginalPath
