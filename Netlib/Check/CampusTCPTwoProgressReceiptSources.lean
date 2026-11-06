import Netlib.Check.CampusTCPTwoProgressReadWriter
import Netlib.Check.CampusTCPTwoProgressReadSuffix
import Netlib.Check.CampusTCPTwoProgressReceiptFrames
import Netlib.Check.CampusTCPTwoProgressPathsFrames

/-!
# Selected writer sources for new actual data receipts

The ledger covers only steps after the selected cut.
Each data receipt retains the exact source of its delivered link.
-/

namespace Netlib.Check.CampusTCPTwoProgressReceiptSources

open Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPRoundPhaseBase (Move)
open CampusTCPTwoProgressStart
open CampusTCPTwoProgressReadWriter (SelectedOutput)

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current next : Cut input complete} {sender : Actor} {gateway : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}

structure History (initial : TwoWriteInitial cut sender gateway lower upper) (current : Cut input complete) where
  suffix : List (Step input)
  steps : current.report.steps = cut.report.steps ++ suffix
  sources : ∀ actual ∈ suffix, ∀ receipt, actual.result.receipt = some receipt → receipt.actor = sender.other →
    Nonempty (SelectedOutput initial current receipt.served.ticket.value.produced)

def History.ofInitial (initial : TwoWriteInitial cut sender gateway lower upper) : History initial cut :=
  ⟨[], by simp, by simp⟩

variable {actual : Step input}

private def append (history : History initial current) (move : Move current actual)
    (source : ∀ receipt, actual.result.receipt = some receipt → receipt.actor = sender.other →
      Nonempty (SelectedOutput initial move.after receipt.served.ticket.value.produced)) : History initial move.after := by
  refine ⟨history.suffix ++ [actual], ?_, ?_⟩
  · rw [move.history, history.steps, List.append_assoc]
  · intro chosen member receipt recorded receiver
    rcases List.mem_append.mp member with old | fresh
    · obtain ⟨prior⟩ := history.sources chosen old receipt recorded receiver
      exact ⟨prior.retain_steps move.retained⟩
    · have same := List.mem_singleton.mp fresh
      subst chosen
      exact source receipt recorded receiver

def History.no_receipt (history : History initial current) (move : Move current actual)
    (quiet : actual.result.receipt = none) : History initial move.after :=
  append history move (by intro receipt recorded; rw [quiet] at recorded; cases recorded)

def History.non_delivery (history : History initial current) (move : Move current actual)
    (event : CampusTCPTwoProgressReceiptFrames.NonDelivery actual.event) : History initial move.after :=
  history.no_receipt move (CampusTCPTwoProgressReceiptFrames.Step.receipt_none actual event)

def History.clock (history : History initial current) {cfg : CampusTCPTwoProgressMonitor.Config}
    {monitor : CampusTCPTwoProgressMonitor.Monitor} {actor : Actor} {millis : Nat}
    (clocked : CampusTCPTwoProgressClock.Clocked cut current cfg monitor actor millis actual) : History initial clocked.move.after :=
  history.no_receipt clocked.move (clocked.base.actualEq ▸ clocked.base.value.receipt)

def History.other_receipt (history : History initial current) (move : Move current actual)
    (receipt : Receipt input) (recorded : actual.result.receipt = some receipt) (other : receipt.actor ≠ sender.other) :
    History initial move.after :=
  append history move (by
    intro selected present actor
    have same := Option.some.inj (recorded.symm.trans present)
    subst selected
    exact False.elim (other actor))

variable {part : CampusTCPTwoProgressSender.Part} {lane : CampusTCPTwoProgressMonitor.Lane}
variable {beforeStage afterStage : CampusTCPTwoProgressReceiver.Stage} {chunk : List UInt8}

def History.data (history : History initial current) (path : CampusTCPTwoProgressPaths.DataLink initial current part lane)
    (source : SelectedOutput initial current path.served.ticket.value.produced)
    (received : CampusTCPTwoProgressReceive.Received initial current beforeStage afterStage chunk
      path.index path.served path.emission path.emitted) : History initial received.move.after :=
  append history received.move (by
    intro receipt recorded _
    have same := Option.some.inj (received.delivery.receiptAt.symm.trans recorded)
    subst receipt
    rw [received.delivery.receiptService]
    exact ⟨source.retain_steps received.move.retained⟩)

def History.ack (history : History initial current) {count : Nat}
    (path : CampusTCPTwoProgressPaths.AckLink initial current count lane)
    (delivery : CampusTCPRoundDelivery.Delivery current.report complete current.endpoints
      path.index path.served path.emission path.emitted) (move : Move current delivery.step) : History initial move.after := by
  apply history.other_receipt move delivery.receipt delivery.receiptAt
  have actor : delivery.receipt.actor = sender := by
    rw [delivery.receipt.receiver, delivery.receiptService, path.actor]
    cases sender <;> rfl
  rw [actor]
  cases sender <;> decide

theorem History.suffix_exact (history : History initial current) :
    history.suffix = current.report.steps.drop cut.report.steps.length := by
  rw [history.steps, List.drop_append_length]

theorem History.source_at (history : History initial current) (actual : Step input)
    (member : actual ∈ current.report.steps.drop cut.report.steps.length) (receipt : Receipt input)
    (recorded : actual.result.receipt = some receipt) (receiver : receipt.actor = sender.other) :
    Nonempty (SelectedOutput initial current receipt.served.ticket.value.produced) := by
  rw [← history.suffix_exact] at member
  exact history.sources actual member receipt recorded receiver

theorem History.read_writer (history : History initial current)
    {first : CampusTCPTwoProgressSender.Original initial .lower}
    {second : CampusTCPTwoProgressSender.Original initial .upper} {timeouts : Nat}
    (done : CampusTCPTwoProgressRead.Completed initial current first second timeouts)
    (index : Nat) (byte : UInt8) (selected : (lower ++ upper)[index]? = some byte) :
    ∃ origin : CampusTCPTwoProgressReadSuffix.SuffixReadOrigin done index byte,
      Nonempty (CampusTCPTwoProgressWriteOrigins.SelectedWriteOrigin initial origin.attempt origin.read.origin.localIndex byte) := by
  obtain ⟨origin⟩ := CampusTCPTwoProgressReadSuffix.Completed.suffix_read_origin done index byte selected
  obtain ⟨source⟩ := history.source_at origin.delivery.receive.joint.step origin.joint_suffix
    origin.delivery.receive.receipt origin.delivery.receive.recorded origin.delivery.receive.receiver
  exact ⟨origin, ⟨origin.selected_writer source⟩⟩

end Netlib.Check.CampusTCPTwoProgressReceiptSources
