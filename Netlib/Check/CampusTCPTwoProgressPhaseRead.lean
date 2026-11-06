import Netlib.Check.CampusTCPTwoProgressPhaseBase
import Netlib.Check.CampusTCPTwoProgressRead

/-!
# Actual terminal read from the joint phase

The final loss history includes the same read step.
Both literal originals retain their selected writer evidence.
-/

namespace Netlib.Check.CampusTCPTwoProgressPhaseRead

open Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart
open CampusTCPTwoProgressPhaseBase (Core OriginalTimes emitted)
open CampusTCPTwoProgressSetup (config)

namespace M
export CampusTCPTwoProgressMonitor (Monitor Allowed observe nextDemand)
end M
namespace S
export CampusTCPTwoProgressSender (Original)
end S
namespace Read
export CampusTCPTwoProgressRead (ReadMove Completed)
end Read
namespace F
export CampusTCPTwoProgressMonitorFacts (allowed_iff serves_operation observe_action)
end F

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current : Cut input complete} {sender : Actor} {gateway : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {native : NativeEnv cut gateway initial.gatewayState.session.entry} {quantum allowance : Nat}
variable {monitor : M.Monitor} {first : S.Original initial .lower} {second : S.Original initial .upper} {actual : Step input}

private theorem read_allowed (mode : monitor.mode = .needRead) :
    M.Allowed (config initial native quantum allowance) current.report.final monitor (.read sender.other (lower ++ upper).length) := by
  apply (F.allowed_iff _ _ _ _).mpr
  refine ⟨by rw [mode]; decide, .inl ⟨.single (.operation (.read sender.other (lower ++ upper).length)), ?_, ?_⟩, rfl⟩
  · rw [M.nextDemand, mode]
    rfl
  · exact (F.serves_operation _ _).mpr rfl

private theorem sender_steps (value : Read.ReadMove initial current first second timeouts actual) :
    applicationSteps value.move.after.endpoints sender = applicationSteps current.endpoints sender := by
  have steps := CampusTCPRoundPhaseHistory.Move.local_history value.move sender.other (.read (lower ++ upper).length)
    (by rw [value.event]; exact .read _) value.operation value.recorded sender
  have different : sender ≠ sender.other := by cases sender <;> decide
  simpa only [different, ite_false, List.append_nil] using steps

structure ReadDone (core : Core initial native quantum allowance current monitor (.retired first second) .allReleased)
    (actual : Step input) where
  value : Read.ReadMove initial current first second monitor.retries actual
  allowed : M.Allowed (config initial native quantum allowance) current.report.final monitor actual.event
  observed : M.observe (config initial native quantum allowance) monitor actual =
    { monitor with mode := .done, waiting := false, readStamp := some value.operation.stamp, readBytes := lower ++ upper }
  losses : CampusTCPTwoProgressLossHistory.History initial (config initial native quantum allowance) value.move.after
    (M.observe (config initial native quantum allowance) monitor actual)
  book : losses.book = core.losses.book
  suffix : losses.suffix = core.losses.suffix ++ [actual]
  lossBound : (M.observe (config initial native quantum allowance) monitor actual).drops.length ≤ allowance
  originals : CampusTCPTwoProgressSourceHistory.Originals initial value.move.after (.retired first second)
  originalTimes : OriginalTimes initial (.retired first second)
  writer : CampusTCPTwoProgressWriteHistory.History initial value.move.after (lower ++ upper)

theorem read_at (core : Core initial native quantum allowance current monitor (.retired first second) .allReleased)
    (mode : monitor.mode = .needRead) : ∃ actual, Nonempty (ReadDone core actual) := by
  obtain ⟨actual, ⟨value⟩⟩ := CampusTCPTwoProgressRead.read_at core.live
  have allowed : M.Allowed (config initial native quantum allowance) current.report.final monitor actual.event := by
    rw [value.event]
    exact read_allowed mode
  have observed : M.observe (config initial native quantum allowance) monitor actual =
      { monitor with mode := .done, waiting := false, readStamp := some value.operation.stamp, readBytes := lower ++ upper } := by
    rw [F.observe_action _ _ _ value.move.supported value.move.passed
      (by rw [value.move.beforeEq]; exact allowed) (.read sender.other (lower ++ upper).length) value.event]
    have actor : (sender.other == sender.other) = true := by cases sender <;> rfl
    have bytes : ((lower ++ upper) == (lower ++ upper)) = true := beq_self_eq_true _
    simp only [CampusTCPTwoProgressMonitor.observeOrdinary, mode, CampusTCPTwoProgressMonitor.observeRead,
      value.recorded, value.returned, config, actor, bytes, Bool.and_self, ite_true]
  let losses := core.losses.append value.move
    (by rw [CampusTCPTwoProgressLossHistory.isDrop, value.event])
    (by rw [CampusTCPTwoProgressLossHistory.isTimeout, value.event])
    (by rw [observed]) (by rw [observed])
  exact ⟨actual, ⟨{
    value, allowed, observed, losses, book := rfl, suffix := rfl
    lossBound := by rw [observed]; exact core.lossBound
    originals := core.originals.retain_steps value.move.retained
    originalTimes := core.originalTimes
    writer := core.writer.same (sender_steps value) }⟩⟩

variable {core : Core initial native quantum allowance current monitor (.retired first second) .allReleased}

def ReadDone.completed (record : ReadDone core actual) : Read.Completed initial record.value.move.after first second monitor.retries :=
  record.value.completed

theorem ReadDone.completed_reader (record : ReadDone core actual) : record.completed.reader = actual := record.value.completedReader

theorem ReadDone.completed_operation (record : ReadDone core actual) : record.completed.operation = record.value.operation :=
  record.value.completedOperation

theorem ReadDone.mode (record : ReadDone core actual) :
    (M.observe (config initial native quantum allowance) monitor actual).mode = .done := by rw [record.observed]

theorem ReadDone.stamp (record : ReadDone core actual) :
    (M.observe (config initial native quantum allowance) monitor actual).readStamp = some record.value.operation.stamp := by rw [record.observed]

theorem ReadDone.bytes (record : ReadDone core actual) :
    (M.observe (config initial native quantum allowance) monitor actual).readBytes = lower ++ upper := by rw [record.observed]

theorem ReadDone.retries (record : ReadDone core actual) :
    (M.observe (config initial native quantum allowance) monitor actual).retries = monitor.retries := by rw [record.observed]

theorem ReadDone.drops (record : ReadDone core actual) :
    (M.observe (config initial native quantum allowance) monitor actual).drops = monitor.drops := by rw [record.observed]

theorem ReadDone.read_slot (record : ReadDone core actual) : record.losses.suffix[core.losses.suffix.length]? = some actual := by
  rw [record.suffix]
  exact List.getElem?_concat_length

theorem ReadDone.read_member (record : ReadDone core actual) : actual ∈ record.losses.suffix := by
  rw [record.suffix]
  exact List.mem_append_right _ (List.mem_singleton_self _)

def ReadDone.lower_origin (record : ReadDone core actual) (index : Nat) (byte : UInt8)
    (selected : first.packet.packet.segment.payload[index]? = some byte) :
    CampusTCPTwoProgressWriteOrigins.SelectedWriteOrigin initial record.originals.1.sent.attempt index byte :=
  record.originals.1.packet_byte_origin index byte selected

def ReadDone.upper_origin (record : ReadDone core actual) (index : Nat) (byte : UInt8)
    (selected : second.packet.packet.segment.payload[index]? = some byte) :
    CampusTCPTwoProgressWriteOrigins.SelectedWriteOrigin initial record.originals.2.sent.attempt index byte :=
  record.originals.2.packet_byte_origin index byte selected

end Netlib.Check.CampusTCPTwoProgressPhaseRead
