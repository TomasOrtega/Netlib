import Netlib.Check.CampusTCPTwoTransferLocatedRead
import Netlib.Check.CampusTCPTwoProgressReadWriter
import Netlib.Check.CampusTCPRoundOrigins

/-!
# Actual read suffix and selected writer evidence after transfer

The healthy stored prefix provides compliance only with its actual prior report.
Read origins use the same receiver suffix and retained receipt-source ledger.
-/

namespace Netlib.Check.CampusTCPTwoTransferLocatedRead

open Protocol Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart
open CampusTCPTwoTransferNative (Checks Routing)
open CampusTCPTwoTransferLocatedCore (Core config)

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current : Cut input complete} {sender : Actor} {gateway location : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {checks : Checks cut initial.gatewayState.session.entry} {routing : Routing cut gateway}
variable {quantum allowance : Nat} {reverseLower reverseUpper : List UInt8} {monitor : W.Monitor}
variable {first : S.Original initial .lower} {second : S.Original initial .upper} {actual : Step input}
variable {core : Core initial checks routing quantum allowance reverseLower reverseUpper
  current monitor location (.retired first second) .allReleased}

local notation "cfg" => config initial checks routing quantum allowance reverseLower reverseUpper

def Complete.finalCut (done : Complete core actual) : Cut input complete := done.value.move.after

def Complete.gatewayState (done : Complete core actual) : CampusTCPTwoProgressGatewayAt.ViewAt initial done.finalCut location :=
  core.live.gatewayState.reframe (done.value.gateway location)

theorem Complete.needWrite (done : Complete core actual) : (W.observe cfg monitor actual).exchange.mode = .needWrite := by
  rw [done.observed]
  rfl

theorem Complete.read_slot (done : Complete core actual) : done.losses.suffix[core.losses.suffix.length]? = some actual := by
  rw [done.suffix]
  exact List.getElem?_concat_length

theorem Complete.read_member (done : Complete core actual) : actual ∈ done.losses.suffix := by
  rw [done.suffix]
  exact List.mem_append_right _ (List.mem_singleton_self _)

theorem Complete.global_read_slot (done : Complete core actual) :
    (W.observe cfg monitor actual).exchange.forwardReadSlot = some monitor.exchange.slots := by rw [done.observed]; rfl

theorem Complete.counter_fields (done : Complete core actual) :
    (W.observe cfg monitor actual).exchange.forward.retries = monitor.exchange.forward.retries ∧
      (W.observe cfg monitor actual).exchange.forward.drops = monitor.exchange.forward.drops ∧
      (W.observe cfg monitor actual).exchange.drops = monitor.exchange.drops ∧
      (W.observe cfg monitor actual).exchange.timeouts = monitor.exchange.timeouts ∧
      (W.observe cfg monitor actual).exchange.slots = monitor.exchange.slots + 1 := by
  rw [done.observed]
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

private theorem passed_of_healthy_fold (config : CampusTCPTwoTransferMonitor.Config) (monitor : W.Monitor)
    (steps : List (Step input)) (healthy : (steps.foldl (W.observe config) monitor).mode ≠ .invalid) :
    ∀ chosen ∈ steps, chosen.result.passed = true := by
  induction steps generalizing monitor with
  | nil => intro _ member; cases member
  | cons actual rest ih =>
    have nextHealthy := CampusTCPTwoTransferAccounting.fold_healthy config (W.observe config monitor actual) rest healthy
    have passed := (CampusTCPTwoTransferAccounting.observe_checked config monitor actual nextHealthy).2.2.1
    intro chosen member
    rcases List.mem_cons.mp member with same | later
    · exact same ▸ passed
    · exact ih (W.observe config monitor actual) healthy chosen later

theorem Complete.suffix_passed (done : Complete core actual) :
    ∀ chosen ∈ done.losses.suffix, chosen.result.passed = true :=
  passed_of_healthy_fold cfg .initial done.losses.suffix (by rw [done.losses.observed]; exact done.healthy)

theorem Complete.compliant (done : Complete core actual) (prior : cut.report.compliant = true) :
    done.finalCut.report.compliant = true :=
  CampusTCPRecoveryRoundOrigins.compliant_of_suffix cut.report done.finalCut.report done.finalCut.supported prior
    done.losses.suffix done.losses.steps done.suffix_passed

theorem Complete.actual_budget (done : Complete core actual) :
    (done.losses.suffix.filter CampusTCPTwoExchangeLoss.isTimeoutOutput).length ≤
        (done.losses.suffix.filter CampusTCPTwoProgressLossHistory.isDrop).length ∧
      (done.losses.suffix.filter CampusTCPTwoProgressLossHistory.isDrop).length ≤ allowance := by
  apply done.losses.actual_budget
  rw [done.losses.wholeDropIDs, ← done.losses.dropIDs]
  exact done.lossBound

def Complete.lower_origin (done : Complete core actual) (index : Nat) (byte : UInt8)
    (selected : first.packet.packet.segment.payload[index]? = some byte) :
    CampusTCPTwoProgressWriteOrigins.SelectedWriteOrigin initial done.originals.1.sent.attempt index byte :=
  done.originals.1.packet_byte_origin index byte selected

def Complete.upper_origin (done : Complete core actual) (index : Nat) (byte : UInt8)
    (selected : second.packet.packet.segment.payload[index]? = some byte) :
    CampusTCPTwoProgressWriteOrigins.SelectedWriteOrigin initial done.originals.2.sent.attempt index byte :=
  done.originals.2.packet_byte_origin index byte selected


open CampusTCPGapProgressStart (seed endpoint_chain)
open CampusTCPGapProgressOrigins (seed_empty_sent seed_empty_pending endpoint_order)

private def suffix_chain_end (state : Endpoint.State) : List T.Step → Endpoint.State
  | [] => state
  | head :: rest => suffix_chain_end head.result.state rest

private theorem suffix_chain_end_eq (chain : ApplicationTrace.Chain initialState steps final) :
    suffix_chain_end initialState steps = final := by
  induction chain with
  | nil state => rfl
  | cons head rest ih => exact ih

private theorem suffix_chain_drop (whole : ApplicationTrace.Chain initialState (prior ++ later) final) :
    ApplicationTrace.Chain (suffix_chain_end initialState prior) later final := by
  induction prior generalizing initialState with
  | nil => exact whole
  | cons head prior ih =>
    cases whole with
    | cons head wholeTail => exact ih wholeTail

private theorem chain_suffix_from (before : ApplicationTrace.Chain initialState prior middle)
    (whole : ApplicationTrace.Chain initialState (prior ++ later) final) : ApplicationTrace.Chain middle later final := by
  rw [← suffix_chain_end_eq before]
  exact suffix_chain_drop whole

private theorem receives_suffix_from {input : Input} {events : List CampusTCPModel.Event} {report : Report input events}
    {peer : List T.Step} {actor : Actor} (prior later : List T.Step)
    (history : CampusTCPReceiveHistory.PayloadReceives report peer actor (prior ++ later)) :
    CampusTCPReceiveHistory.PayloadReceives report peer actor later :=
  fun operation member => history operation (List.mem_append_right prior member)

theorem Complete.suffix_chain (done : Complete core actual) :
    ApplicationTrace.Chain (endpoint cut.endpoints sender.other) done.value.history.operations
      (endpoint done.value.move.after.endpoints sender.other) := by
  have whole := endpoint_chain done.value.move.after sender.other
  rw [done.value.history.steps] at whole
  exact chain_suffix_from (endpoint_chain cut sender.other) whole

theorem Complete.suffix_receives (done : Complete core actual) :
    CampusTCPReceiveHistory.PayloadReceives done.value.move.after.report
      (applicationSteps done.value.move.after.endpoints sender) sender.other done.value.history.operations := by
  have full := CampusTCPRecoveryRoundOrigins.Report.receives done.value.move.after.report complete
    done.value.move.after.endpoints done.value.move.after.connection sender.other
  have receives : CampusTCPReceiveHistory.PayloadReceives done.value.move.after.report
      (applicationSteps done.value.move.after.endpoints sender) sender.other
      (applicationSteps done.value.move.after.endpoints sender.other) := by
    cases sender <;> exact full
  rw [done.value.history.steps] at receives
  exact receives_suffix_from (applicationSteps cut.endpoints sender.other) done.value.history.operations receives

theorem Complete.suffix_order (done : Complete core actual) :
    ApplicationTrace.Chronological done.value.history.operations := by
  have ordered := endpoint_order done.value.move.after sender.other
  rw [done.value.history.steps] at ordered
  exact (List.pairwise_append.mp ordered).2.1

theorem Complete.reader_suffix (done : Complete core actual) :
    done.value.operation ∈ done.value.history.operations :=
  (List.mem_filter.mp (by rw [done.value.history.streams.reads]; exact List.mem_singleton_self _)).1

abbrev SuffixReadOrigin (done : Complete core actual) (index : Nat) (byte : UInt8) :=
  CampusTCPGapFacts.ReadOrigin done.value.move.after.report (seed complete sender)
    (applicationSteps done.value.move.after.endpoints sender) sender.other done.value.history.operations
    done.value.operation index byte

theorem Complete.suffix_read_origin (done : Complete core actual)
    (index : Nat) (byte : UInt8) (selected : (lower ++ upper)[index]? = some byte) :
    Nonempty (SuffixReadOrigin done index byte) := by
  have receives := done.suffix_receives
  have history := CampusTCPGapFacts.payload_delivery_history receives
    (endpoint_order done.value.move.after sender) done.suffix_order
  apply CampusTCPGapFacts.payload_read_origin done.suffix_chain (endpoint_chain done.value.move.after sender) history receives
    initial.receiverState.unread initial.receiverState.held (seed_empty_sent complete sender) (seed_empty_pending complete sender)
    done.value.operation done.reader_suffix (lower ++ upper).length done.value.history.streams.readEvent index byte
  rw [done.value.history.streams.readBytes]
  exact selected

variable {done : Complete core actual} {index : Nat} {byte : UInt8}

def SuffixReadOrigin.issuer (origin : SuffixReadOrigin done index byte) : T.Step := origin.read.origin.origin.issuer

theorem SuffixReadOrigin.issuer_member (origin : SuffixReadOrigin done index byte) :
    origin.issuer ∈ done.value.history.operations := origin.read.origin.origin.issuer_member

theorem SuffixReadOrigin.issuer_current (origin : SuffixReadOrigin done index byte) :
    origin.issuer ∈ applicationSteps done.value.move.after.endpoints sender.other := by
  rw [done.value.history.steps]
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
  have ordered := endpoint_order done.value.move.after sender.other
  rw [done.value.history.steps] at ordered
  exact Nat.lt_irrefl _ ((List.pairwise_append.mp ordered).2.2 origin.issuer oldMember origin.issuer origin.issuer_member)

theorem SuffixReadOrigin.joint_suffix (origin : SuffixReadOrigin done index byte) :
    origin.delivery.receive.joint.step ∈ done.value.move.after.report.steps.drop cut.report.steps.length := by
  let joint := origin.delivery.receive.joint.step
  obtain ⟨extra, history⟩ := done.value.anchor.retained
  have member : joint ∈ cut.report.steps ++ extra :=
    Eq.mp (congrArg (fun steps => joint ∈ steps) history.symm) origin.delivery.receive.joint.member
  rcases List.mem_append.mp member with old | fresh
  · exact False.elim (origin.joint_not_initial old)
  · rw [← history, List.drop_append_length]
    exact fresh

def SuffixReadOrigin.selected_writer (origin : SuffixReadOrigin done index byte)
    (source : CampusTCPTwoProgressReadWriter.SelectedOutput initial done.value.move.after
      origin.delivery.receive.receipt.served.ticket.value.produced) :
    CampusTCPTwoProgressWriteOrigins.SelectedWriteOrigin initial origin.attempt origin.read.origin.localIndex byte := by
  have selected : origin.attempt.step = source.attempt.step ∧ origin.attempt.output = source.attempt.output := by
    obtain ⟨actor, operation, packet, outputOrigin, production, receiver, step, output⟩ := origin.delivery.applicationSource
    have actorEq : actor = sender := by cases sender <;> exact receiver
    rw [actorEq] at production
    have same := Produced.application.inj (source.production.symm.trans production)
    exact ⟨(congrArg (fun attempt => attempt.step) origin.actualSource).trans (step.trans same.2.1.symm),
      (congrArg (fun attempt => attempt.output) origin.actualSource).trans (output.trans same.2.2.symm)⟩
  exact source.attempt_origin origin.attempt selected.1 selected.2 _ _ origin.source_byte

theorem SuffixReadOrigin.permissions (origin : SuffixReadOrigin done index byte) (prior : cut.report.compliant = true) :
    CampusTCPRoundOrigins.ServicePermissions origin.delivery.service.joint.step origin.delivery.receive.receipt.served :=
  CampusTCPRoundOrigins.service_permissions done.value.move.after.report (done.compliant prior)
    origin.delivery.service.joint.step origin.delivery.service.joint.member origin.delivery.receive.receipt.served
    origin.delivery.service.present origin.delivery.receive.receipt.emission origin.delivery.receive.receipt.emitted

structure ReadByte (done : Complete core actual) (index : Nat) (byte : UInt8) where
  origin : SuffixReadOrigin done index byte
  writer : CampusTCPTwoProgressWriteOrigins.SelectedWriteOrigin initial origin.attempt origin.read.origin.localIndex byte

theorem Complete.read_origin_selected (done : Complete core actual) (index : Nat) (byte : UInt8)
    (selected : (lower ++ upper)[index]? = some byte) : Nonempty (ReadByte done index byte) := by
  obtain ⟨origin⟩ := done.suffix_read_origin index byte selected
  obtain ⟨source⟩ := done.sources.source_at origin.delivery.receive.joint.step origin.joint_suffix
    origin.delivery.receive.receipt origin.delivery.receive.recorded origin.delivery.receive.receiver
  exact ⟨⟨origin, origin.selected_writer source⟩⟩

theorem Complete.read_permissions (done : Complete core actual) (prior : cut.report.compliant = true)
    (index : Nat) (byte : UInt8) (selected : (lower ++ upper)[index]? = some byte) :
    ∃ value : ReadByte done index byte,
      CampusTCPRoundOrigins.ServicePermissions value.origin.delivery.service.joint.step
        value.origin.delivery.receive.receipt.served := by
  obtain ⟨value⟩ := done.read_origin_selected index byte selected
  exact ⟨value, value.origin.permissions prior⟩

end Netlib.Check.CampusTCPTwoTransferLocatedRead
