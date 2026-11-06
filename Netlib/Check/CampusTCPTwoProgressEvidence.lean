import Netlib.Check.CampusTCPTwoProgressPhaseState
import Netlib.Check.CampusTCPTwoProgressPhaseRead
import Netlib.Check.CampusTCPTwoProgressPhaseNormalize
import Netlib.Check.CampusTCPTwoProgressPreparationDrop

/-!
# Evidence from the accepted write through the final read

Each phase names the current cut and monitor.
The final read retains the actual loss and writer histories.
-/

namespace Netlib.Check.CampusTCPTwoProgressEvidence

open Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPRoundPhaseBase (Move)
open CampusTCPTwoProgressStart
open CampusTCPTwoProgressPhaseBase (Core)
open CampusTCPTwoProgressSetup (config)

namespace S
export CampusTCPTwoProgressSender (Stage Original)
end S
namespace R
export CampusTCPTwoProgressReceiver (Stage)
end R
namespace M
export CampusTCPTwoProgressMonitor (Monitor observe)
end M

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current : Cut input complete} {sender : Actor} {gateway : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {native : NativeEnv cut gateway initial.gatewayState.session.entry} {quantum allowance : Nat}
variable {monitor : M.Monitor} {sent : S.Stage initial} {received : R.Stage}

structure Ready (core : Core initial native quantum allowance current monitor sent received) where
  mode : monitor.mode = .needRead
  retired : sent.ledger = []
  preparing : sent.preparing = false
  sources : CampusTCPTwoProgressReceiptSources.History initial current

structure Complete (initial : TwoWriteInitial cut sender gateway lower upper)
    (native : NativeEnv cut gateway initial.gatewayState.session.entry) (quantum allowance : Nat)
    (current : Cut input complete) (monitor : M.Monitor) where
  first : S.Original initial .lower
  second : S.Original initial .upper
  timeouts : Nat
  completed : CampusTCPTwoProgressRead.Completed initial current first second timeouts
  retryCount : timeouts = monitor.retries
  losses : CampusTCPTwoProgressLossHistory.History initial (config initial native quantum allowance) current monitor
  lossBound : monitor.drops.length ≤ allowance
  sources : CampusTCPTwoProgressReceiptSources.History initial current
  mode : monitor.mode = .done
  stamp : monitor.readStamp = some completed.operation.stamp
  bytes : monitor.readBytes = lower ++ upper
  originals : CampusTCPTwoProgressSourceHistory.Originals initial current (.retired first second)
  originalTimes : CampusTCPTwoProgressPhaseBase.OriginalTimes initial (.retired first second)
  writer : CampusTCPTwoProgressWriteHistory.History initial current (lower ++ upper)

theorem Ready.read_at {core : Core initial native quantum allowance current monitor sent received} (ready : Ready core) :
    ∃ actual, ∃ move : Move current actual,
      Nonempty (Complete initial native quantum allowance move.after (M.observe (config initial native quantum allowance) monitor actual)) := by
  cases sent with
  | written | lower => cases ready.preparing
  | both first second head => cases ready.retired
  | tail first second head => cases ready.retired
  | retired first second =>
    have all := CampusTCPTwoProgressPhaseNormalize.retired_allReleased core
    cases all
    obtain ⟨actual, ⟨record⟩⟩ := CampusTCPTwoProgressPhaseRead.read_at core ready.mode
    exact ⟨actual, record.value.move, ⟨{
      first, second, timeouts := monitor.retries
      completed := record.completed
      retryCount := record.retries.symm
      losses := record.losses
      lossBound := record.lossBound
      sources := ready.sources.non_delivery record.value.move (by rw [record.value.event]; trivial)
      mode := record.mode
      stamp := by rw [record.completed_operation]; exact record.stamp
      bytes := record.bytes
      originals := record.originals
      originalTimes := record.originalTimes
      writer := record.writer }⟩⟩

theorem Complete.read_writer (value : Complete initial native quantum allowance current monitor)
    (index : Nat) (byte : UInt8) (selected : (lower ++ upper)[index]? = some byte) :
    ∃ origin : CampusTCPTwoProgressReadSuffix.SuffixReadOrigin value.completed index byte,
      Nonempty (CampusTCPTwoProgressWriteOrigins.SelectedWriteOrigin initial origin.attempt origin.read.origin.localIndex byte) :=
  value.sources.read_writer value.completed index byte selected

theorem Complete.retry_bound (value : Complete initial native quantum allowance current monitor) : value.timeouts ≤ allowance := by
  rw [value.retryCount]
  exact Nat.le_trans value.losses.count value.lossBound

inductive Evidence (initial : TwoWriteInitial cut sender gateway lower upper)
    (native : NativeEnv cut gateway initial.gatewayState.session.entry) (quantum allowance : Nat)
    (current : Cut input complete) (monitor : M.Monitor) where
  | written (value : CampusTCPTwoProgressPreparation.Written initial native quantum allowance current monitor)
      (sources : CampusTCPTwoProgressReceiptSources.History initial current)
  | upper (first : S.Original initial .lower)
      (value : CampusTCPTwoProgressPreparation.PendingUpper initial native quantum allowance current monitor first)
      (sources : CampusTCPTwoProgressReceiptSources.History initial current)
  | active {sent : S.Stage initial} {received : R.Stage}
      (core : Core initial native quantum allowance current monitor sent received)
      (value : CampusTCPTwoProgressPhaseState.Active core)
  | ready {sent : S.Stage initial} {received : R.Stage}
      (core : Core initial native quantum allowance current monitor sent received) (value : Ready core)
  | done (value : Complete initial native quantum allowance current monitor)

def Evidence.ofInitial (initial : TwoWriteInitial cut sender gateway lower upper)
    (native : NativeEnv cut gateway initial.gatewayState.session.entry) (quantum allowance : Nat) :
    Evidence initial native quantum allowance cut .initial :=
  .written (CampusTCPTwoProgressPreparation.Written.ofInitial initial native quantum allowance)
    (CampusTCPTwoProgressReceiptSources.History.ofInitial initial)

theorem Evidence.healthy (value : Evidence initial native quantum allowance current monitor) : monitor.mode ≠ .invalid := by
  cases value with
  | written value _ => rw [value.mode]; decide
  | upper first value _ => rw [value.mode]; decide
  | active core value => rcases value.mode with mode | mode <;> rw [mode] <;> decide
  | ready core value => rw [value.mode]; decide
  | done value => rw [value.mode]; decide

end Netlib.Check.CampusTCPTwoProgressEvidence
