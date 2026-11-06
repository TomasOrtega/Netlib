import Netlib.Check.CampusTCPTwoProgressReadWriter
import Netlib.Check.CampusTCPTwoProgressPhaseRetry
import Netlib.Check.CampusTCPTwoProgressOriginalPath
import Netlib.Check.CampusTCPTwoProgressPathsAssign
import Netlib.Check.CampusTCPTwoProgressPathsService

/-!
# Selected writer ancestry through actual packet paths

Original sends and head retries construct the source witness.
Assignment and service retain the same literal Produced value.
-/

namespace Netlib.Check.CampusTCPTwoProgressPhaseSources

open Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart
open CampusTCPTwoProgressPhaseBase (Core)
open CampusTCPTwoProgressReadWriter (SelectedOutput)

namespace S
export CampusTCPTwoProgressSender (Stage Part Original)
end S

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current : Cut input complete} {sender : Actor} {gateway : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {native : NativeEnv cut gateway initial.gatewayState.session.entry} {quantum allowance : Nat}
variable {monitor : CampusTCPTwoProgressMonitor.Monitor} {actual : Step input}
variable {first : S.Original initial .lower} {second : S.Original initial .upper}
variable {head : Recovery.Outstanding} {received : CampusTCPTwoProgressReceiver.Stage}

def first_source {core : Core initial native quantum allowance current monitor .written .empty}
    (value : CampusTCPTwoProgressPhaseSend.First core actual) :
    SelectedOutput initial value.value.facts.move.after value.path.output.produced :=
  (SelectedOutput.ofIssued value.next.originals).reindex (CampusTCPTwoProgressOriginalPath.first_source value).symm

def second_source {core : Core initial native quantum allowance current monitor (.lower first) .empty}
    (value : CampusTCPTwoProgressPhaseSend.Second core actual) :
    SelectedOutput initial value.value.facts.move.after value.path.output.produced :=
  (SelectedOutput.ofIssued value.next.originals.2).reindex (CampusTCPTwoProgressOriginalPath.second_source value).symm

theorem retry_source {sent : S.Stage initial} {core : Core initial native quantum allowance current monitor sent received}
    {part : S.Part} {rest : List Recovery.Outstanding} {position : Nat}
    (value : CampusTCPTwoProgressPhaseRetry.Retried core part head rest position actual) :
    value.path.output.produced = value.value.facts.produced := by
  have selected := congrArg (fun state : CampusTCPTwoProgressMonitor.Monitor => state.retry.refs.dataOutput) value.observed
  have index := Option.some.inj (value.path.outputRef.symm.trans selected)
  have stored := value.path.output.stored
  rw [index] at stored
  exact Option.some.inj (stored.symm.trans value.value.source)

def lower_retry_source {core : Core initial native quantum allowance current monitor (.both first second head) received}
    {position : Nat} (value : CampusTCPTwoProgressPhaseRetry.Retried core .lower head [second.entry] position actual) :
    SelectedOutput initial value.value.move.after value.path.output.produced :=
  (SelectedOutput.ofLowerRetry core value.value).reindex (retry_source value).symm

def upper_retry_source {core : Core initial native quantum allowance current monitor (.tail first second head) received}
    {position : Nat} (value : CampusTCPTwoProgressPhaseRetry.Retried core .upper head [] position actual) :
    SelectedOutput initial value.value.move.after value.path.output.produced :=
  (SelectedOutput.ofUpperRetry core value.value).reindex (retry_source value).symm

variable {sent : S.Stage initial} {timeouts : Nat} {part : S.Part} {lane : CampusTCPTwoProgressMonitor.Lane}

def assigned_source {live : CampusTCPTwoProgressState.Live initial current sent timeouts received}
    {path : CampusTCPTwoProgressPaths.DataIngress initial current part lane}
    (source : SelectedOutput initial current path.output.produced)
    (value : CampusTCPTwoProgressPathsAssign.DataAssigned live path native actual) :
    SelectedOutput initial value.value.move.after value.ticket.output.produced :=
  (source.retain_steps value.value.move.retained).reindex value.ticketProduced.symm

def served_source {live : CampusTCPTwoProgressState.Live initial current sent timeouts received}
    {path : CampusTCPTwoProgressPaths.DataTicket initial native current part lane}
    (source : SelectedOutput initial current path.output.produced)
    (value : CampusTCPTwoProgressPathsService.DataServed live path actual) :
    SelectedOutput initial value.value.move.after value.link.served.ticket.value.produced :=
  (source.retain_steps value.value.move.retained).reindex value.linkProduced.symm

end Netlib.Check.CampusTCPTwoProgressPhaseSources
