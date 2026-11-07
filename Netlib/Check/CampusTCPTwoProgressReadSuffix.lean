import Netlib.Check.CampusTCPTwoProgressReadOrigins
import Netlib.Check.CampusTCPTwoProgressReadWriter

/-!
# Read origins in the actual new receiver suffix

The selected cut has no unread or held bytes.
Each final read byte therefore has an issuer in the new suffix.
-/

namespace Netlib.Check.CampusTCPTwoProgressReadSuffix

open Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart
open CampusTCPTwoProgressRead (Completed)
open CampusTCPGapProgressStart (seed endpoint_chain)
open CampusTCPGapProgressOrigins (seed_empty_sent seed_empty_pending endpoint_order)

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current : Cut input complete} {sender : Actor} {gateway : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {first : CampusTCPTwoProgressSender.Original initial .lower}
variable {second : CampusTCPTwoProgressSender.Original initial .upper} {timeouts : Nat}

private def chain_end (state : Endpoint.State) : List T.Step → Endpoint.State
  | [] => state
  | head :: rest => chain_end head.result.state rest

private theorem chain_end_eq (chain : ApplicationTrace.Chain initialState steps final) :
    chain_end initialState steps = final := by
  induction chain with
  | nil state => rfl
  | cons head rest ih => exact ih

private theorem chain_drop (whole : ApplicationTrace.Chain initialState (prior ++ later) final) :
    ApplicationTrace.Chain (chain_end initialState prior) later final := by
  induction prior generalizing initialState with
  | nil => exact whole
  | cons head prior ih =>
    cases whole with
    | cons head wholeTail => exact ih wholeTail

private theorem chain_suffix (before : ApplicationTrace.Chain initialState prior middle)
    (whole : ApplicationTrace.Chain initialState (prior ++ later) final) : ApplicationTrace.Chain middle later final := by
  rw [← chain_end_eq before]
  exact chain_drop whole

private theorem receives_suffix {input : Input} {events : List Event} {report : Report input events}
    {peer : List T.Step} {actor : Actor} (prior later : List T.Step)
    (history : CampusTCPReceiveHistory.PayloadReceives report peer actor (prior ++ later)) :
    CampusTCPReceiveHistory.PayloadReceives report peer actor later :=
  fun operation member => history operation (List.mem_append_right prior member)

theorem Completed.suffix_chain (done : Completed initial current first second timeouts) :
    ApplicationTrace.Chain (endpoint cut.endpoints sender.other) done.history.operations
      (endpoint current.endpoints sender.other) := by
  have whole := endpoint_chain current sender.other
  rw [done.history.steps] at whole
  exact chain_suffix (endpoint_chain cut sender.other) whole

theorem Completed.suffix_receives (done : Completed initial current first second timeouts) :
    CampusTCPReceiveHistory.PayloadReceives current.report (applicationSteps current.endpoints sender) sender.other done.history.operations := by
  have receives := done.receives
  rw [done.history.steps] at receives
  exact receives_suffix (applicationSteps cut.endpoints sender.other) done.history.operations receives

theorem Completed.suffix_order (done : Completed initial current first second timeouts) :
    ApplicationTrace.Chronological done.history.operations := by
  have ordered := endpoint_order current sender.other
  rw [done.history.steps] at ordered
  exact (List.pairwise_append.mp ordered).2.1

theorem Completed.reader_suffix (done : Completed initial current first second timeouts) :
    done.operation ∈ done.history.operations :=
  (List.mem_filter.mp (by rw [done.history.streams.reads]; exact List.mem_singleton_self _)).1

abbrev SuffixReadOrigin (done : Completed initial current first second timeouts) (index : Nat) (byte : UInt8) :=
  CampusTCPGapFacts.ReadOrigin current.report (seed complete sender) (applicationSteps current.endpoints sender)
    sender.other done.history.operations done.operation index byte

theorem Completed.suffix_read_origin (done : Completed initial current first second timeouts)
    (index : Nat) (byte : UInt8) (selected : (lower ++ upper)[index]? = some byte) :
    Nonempty (SuffixReadOrigin done index byte) := by
  have receives := Completed.suffix_receives done
  have history := CampusTCPGapFacts.payload_delivery_history receives
    (endpoint_order current sender) (Completed.suffix_order done)
  apply CampusTCPGapFacts.payload_read_origin (Completed.suffix_chain done) (endpoint_chain current sender) history receives
    initial.receiverState.unread initial.receiverState.held (seed_empty_sent complete sender) (seed_empty_pending complete sender)
    done.operation (Completed.reader_suffix done) (lower ++ upper).length done.history.streams.readEvent index byte
  rw [done.history.streams.readBytes]
  exact selected

variable {done : Completed initial current first second timeouts} {index : Nat} {byte : UInt8}

def SuffixReadOrigin.issuer (origin : SuffixReadOrigin done index byte) : T.Step := origin.read.origin.origin.issuer

theorem SuffixReadOrigin.issuer_member (origin : SuffixReadOrigin done index byte) :
    origin.issuer ∈ done.history.operations := origin.read.origin.origin.issuer_member

theorem SuffixReadOrigin.release_member (origin : SuffixReadOrigin done index byte) :
    origin.read.release ∈ done.history.operations := by
  have before : origin.read.release ∈ origin.read.prior :=
    Eq.mp (congrArg (fun steps => origin.read.release ∈ steps) origin.read.releaseSplit.symm)
      (List.mem_append_right _ List.mem_cons_self)
  have retained : origin.read.prior <+: done.history.operations := ⟨_, origin.read.split.symm⟩
  exact retained.subset before

theorem SuffixReadOrigin.issuer_current (origin : SuffixReadOrigin done index byte) :
    origin.issuer ∈ applicationSteps current.endpoints sender.other := by
  rw [done.history.steps]
  exact List.mem_append_right _ origin.issuer_member

theorem SuffixReadOrigin.source_byte (origin : SuffixReadOrigin done index byte) :
    origin.attempt.output.packet.segment.payload[origin.read.origin.localIndex]? = some byte := by
  rw [← origin.path.fields.1]
  exact origin.read.origin.input_byte

theorem SuffixReadOrigin.joint_not_initial (origin : SuffixReadOrigin done index byte) :
    origin.delivery.receive.joint.step ∉ cut.report.steps := by
  intro past
  have old := CampusTCPRecoveryRoundOrigins.Report.application_member cut.report origin.delivery.receive.joint.step past
    sender.other origin.issuer origin.delivery.receive.applied
  have oldMember : origin.issuer ∈ applicationSteps cut.endpoints sender.other := by
    simpa only [cut.connection, CampusTCPRoundPhaseHistory.connectionSteps] using old
  have ordered := endpoint_order current sender.other
  rw [done.history.steps] at ordered
  exact Nat.lt_irrefl _ ((List.pairwise_append.mp ordered).2.2 origin.issuer oldMember origin.issuer origin.issuer_member)

theorem SuffixReadOrigin.joint_suffix (origin : SuffixReadOrigin done index byte) :
    origin.delivery.receive.joint.step ∈ current.report.steps.drop cut.report.steps.length := by
  let actual := origin.delivery.receive.joint.step
  obtain ⟨extra, history⟩ := done.anchor.retained
  have member : actual ∈ cut.report.steps ++ extra :=
    Eq.mp (congrArg (fun steps => actual ∈ steps) history.symm) origin.delivery.receive.joint.member
  rcases List.mem_append.mp member with old | fresh
  · exact False.elim (origin.joint_not_initial old)
  · rw [← history, List.drop_append_length]
    exact fresh

def SuffixReadOrigin.selected_writer (origin : SuffixReadOrigin done index byte)
    (source : CampusTCPTwoProgressReadWriter.SelectedOutput initial current origin.delivery.receive.receipt.served.ticket.value.produced) :
    CampusTCPTwoProgressWriteOrigins.SelectedWriteOrigin initial origin.attempt origin.read.origin.localIndex byte := by
  have selected : origin.attempt.step = source.attempt.step ∧ origin.attempt.output = source.attempt.output := by
    obtain ⟨actor, operation, packet, outputOrigin, production, receiver, step, output⟩ := origin.delivery.applicationSource
    have actorEq : actor = sender := by cases sender <;> exact receiver
    rw [actorEq] at production
    have same := Produced.application.inj (source.production.symm.trans production)
    exact ⟨(congrArg (fun attempt => attempt.step) origin.actualSource).trans (step.trans same.2.1.symm),
      (congrArg (fun attempt => attempt.output) origin.actualSource).trans (output.trans same.2.2.symm)⟩
  exact source.attempt_origin origin.attempt selected.1 selected.2 _ _ origin.source_byte

end Netlib.Check.CampusTCPTwoProgressReadSuffix
