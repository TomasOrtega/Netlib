import Netlib.Check.TCPHandshakeRecoveryAckTemplates
import Netlib.Check.TCPHandshakeRecoveryPhaseOrder
import Netlib.Check.TCPHandshakeRecoveryReceiveConditions
import Netlib.Check.TCPHandshakeRecoveryPreDataEnabled
import Netlib.Check.TCPHandshakeRecoveryOutputTTL
import Netlib.Check.TCPHandshakeRecoveryAvailability
import Netlib.Check.TCPHandshakeRecoveryClockBounds
import Netlib.Check.TCPHandshakeRecoveryPhaseWindows
import Netlib.Check.TCPHandshakeRecoveryTimerBounds
import Netlib.Check.TCPHandshakeRecoveryOutputShape
import Netlib.Check.TCPHandshakeRecoveryPacketInventory
import Netlib.Check.TCPHandshakeRecoveryAdvancingOrigins
import Netlib.Check.TCPHandshakeRecovery
import Netlib.Check.TCPHandshakeRecoveryInvariantCore
import Netlib.Protocol.TCP.EndpointEmptyAckFrame

/-!
# Checked startup recovery operations

Each receive selects an earlier occurrence.
ACK processing retains the actual endpoint result and both timers.
-/

namespace Netlib.Check.TCPHandshakeRecovery

open Protocol.TCP

private theorem input_eq_of_bytes (first second : H.Input) (same : first.bytes = second.bytes) : first = second := by
  cases first with
  | mk bytes packet checked =>
    cases second with
    | mk other decoded verified =>
      dsimp only at same
      subst other
      have equal : packet = decoded := Except.ok.inj (checked.symm.trans verified)
      subst decoded
      rfl

private def source_packet (receipt : Receipt) (packet : H.Input) : Except String { _value : Unit // receipt.source.packet = packet } :=
  if same : receipt.source.packet.bytes = packet.bytes then .ok ⟨(), input_eq_of_bytes _ _ same⟩
  else .error "The selected occurrence is not a copy of this connection's retained control."

private def duplicate_input (packet original : H.Input) : Except String Unit :=
  if packet.packet.header = original.packet.header ∧ packet.packet.segment = original.packet.segment then .ok ()
  else .error "The duplicate control changes the selected tuple, control fields, window, or options."

private def receivePacket (state : State active passive) (index source : Nat) (bytes : List UInt8) (path : O.Path) :
    Except String Receipt := do
  let some selected := state.source source | throw "The selected startup occurrence is absent."
  if earlier : selected.index < index then
    let candidate ← EstablishedReceive.input bytes
    let spec := TCPHandshake.spec candidate path
    let delivery ← spec.check selected.packet
    return ⟨index, selected, spec, delivery, earlier⟩
  else throw "The selected startup occurrence must precede its receipt."

private def armTimer (state : State active passive) (actor : Side) (kind : T.Kind) (source : Nat) :
    Except String (State active passive) :=
  match computed : HandshakeTimer.arm (state.timer actor) kind source with
  | .error _ => .error "The selected SYN timer is already armed."
  | .ok after => .ok (state.withTimer actor after (HandshakeTimer.arm_valid (state.timer_valid actor) computed))

private def ackTimer (state : State active passive) (actor : Side) (kind : T.Kind) (source : Nat) :
    Except String (State active passive) := do
  match (state.timer actor).status with
  | .pending flight =>
    if flight.kind = kind ∧ flight.source = source then
      match computed : HandshakeTimer.acknowledge (state.timer actor) with
      | .error _ => throw "The selected SYN acknowledgment has no outstanding timer."
      | .ok after => return state.withTimer actor after (HandshakeTimer.acknowledge_valid (state.timer_valid actor) computed)
    else throw "The SYN acknowledgment names a different outstanding control."
  | _ => throw "The selected SYN acknowledgment has no outstanding timer."

private def current_ack (current : PreData seed) :
    HandshakeDuplicate.BareAck (Output.reverse current.current.core.inbound)
      current.current.core.sendNext current.current.core.receiveNext current.current.core.window current.current.ipSendLimit :=
  HandshakeDuplicate.BareAck.make _ _ _ _ _ current.valid.1.1
    (EstablishedReceive.State.window_bound _ current.valid.1)
    (Nat.le_trans (Nat.le_add_right 40 _) current.valid.2.2.2.2.2.1)

private def respond (state : State active passive) (receipt : Receipt) (actor : Side) (kind : Kind)
    (packet : H.Input) (cause : Cause) : Effect active passive :=
  publish state ⟨receipt.index, actor, kind, packet, cause⟩

private def onSyn (state : State active passive) (receipt : Receipt) (policy : Bool) :
    Except String (Effect active passive) := do
  match state.phase with
  | .idle => throw "Receive the selected SYN only after active OPEN."
  | .opened opened =>
    let same ← source_packet receipt opened.pending.output
    let delivery : X.Delivery opened.pending.output receipt.spec := same.property ▸ receipt.delivery
    match computed : Handshake.listenSyn passive delivery.input policy with
    | .error reason => throw reason.message
    | .ok pending =>
      let answered : O.Answered active passive := ⟨opened, policy, receipt.index, receipt.spec, delivery, pending, computed⟩
      let next ← armTimer state .passive .synAck receipt.index
      return respond { next with phase := .answered answered } receipt .passive .synAck pending.output
        (.response receipt.source.index)
  | .answered answered =>
    let _ ← source_packet receipt answered.opened.pending.output
    let _ ← duplicate_input receipt.delivery.input answered.delivery.input
    let ack := HandshakeDuplicate.syn_received_ack answered.pending
    return respond state receipt .passive .synReplyAck ack.output (.duplicateSyn receipt.source.index)
  | .acknowledged acknowledged _ =>
    let _ ← source_packet receipt acknowledged.answered.opened.pending.output
    let _ ← duplicate_input receipt.delivery.input acknowledged.answered.delivery.input
    let ack := HandshakeDuplicate.syn_received_ack acknowledged.answered.pending
    return respond state receipt .passive .synReplyAck ack.output (.duplicateSyn receipt.source.index)
  | .complete complete _ server =>
    let _ ← source_packet receipt complete.certificate.activePending.output
    let _ ← duplicate_input receipt.delivery.input complete.certificate.syn.input
    return respond state receipt .passive .synReplyAck (current_ack server).output (.duplicateSyn receipt.source.index)

private def onSynAck (state : State active passive) (receipt : Receipt) (policy : Bool) :
    Except String (Effect active passive) := do
  match state.phase with
  | .idle | .opened _ => throw "The selected SYN,ACK requires an earlier passive SYN receipt."
  | .answered answered =>
    let same ← source_packet receipt answered.pending.output
    let delivery : X.Delivery answered.pending.output receipt.spec := same.property ▸ receipt.delivery
    match computed : Handshake.synSentSynAck answered.opened.pending delivery.input policy with
    | .error reason => throw reason.message
    | .ok ready =>
      let acknowledged : O.Acknowledged active passive :=
        ⟨answered, policy, receipt.index, receipt.spec, delivery, ready, computed⟩
      let next ← ackTimer state .active .syn answered.opened.index
      return respond { next with phase := .acknowledged acknowledged (PreData.initial ready.seed ready.valid) }
        receipt .active .finalAck ready.output (.response receipt.source.index)
  | .acknowledged acknowledged client =>
    let _ ← source_packet receipt acknowledged.answered.pending.output
    let _ ← duplicate_input receipt.delivery.input acknowledged.delivery.input
    return respond state receipt .active .finalAck (current_ack client).output (.duplicateSynAck receipt.source.index)
  | .complete complete client _ =>
    let _ ← source_packet receipt complete.certificate.passivePending.output
    let _ ← duplicate_input receipt.delivery.input complete.certificate.synAck.input
    return respond state receipt .active .finalAck (current_ack client).output (.duplicateSynAck receipt.source.index)

private def onFinalAck (state : State active passive) (receipt : Receipt) : Except String (Effect active passive) := do
  match state.phase with
  | .idle | .opened _ | .answered _ => throw "The selected final ACK requires an earlier active SYN,ACK receipt."
  | .acknowledged acknowledged client =>
    let same ← source_packet receipt acknowledged.ready.output
    let delivery : X.Delivery acknowledged.ready.output receipt.spec := same.property ▸ receipt.delivery
    match computed : Handshake.synReceivedAck acknowledged.answered.pending delivery.input with
    | .error reason => throw reason.message
    | .ok ready =>
      if ordered : acknowledged.answered.opened.index < acknowledged.answered.index ∧
          acknowledged.answered.index < acknowledged.index ∧ acknowledged.index < receipt.index then
        let complete := finish acknowledged receipt.index receipt.spec delivery ready computed ordered
        let next ← ackTimer state .passive .synAck acknowledged.answered.index
        return { state := { next with phase := .complete complete client (PreData.initial ready.seed ready.valid) } }
      else throw "The advancing startup receipts must follow OPEN, SYN, and SYN,ACK in order."
  | .complete complete client server =>
    let applied ← server.receiveAck receipt.delivery.input receipt.index
    return { state := { state with phase := .complete complete client applied.after }, application := some (.passive, applied.operation) }

private def discardBareAck (opened : O.Opened active) (receipt : Receipt) : Except String Unit :=
  if Handshake.Profile receipt.delivery.input 16 ∧
      receipt.delivery.input.packet.header = Handshake.inbound active opened.remote ∧
      receipt.delivery.input.packet.segment.acknowledgment = active.iss.add 1 then .ok ()
  else .error "The SYN-SENT discard requires a bare ACK of the selected active SYN and tuple."

private def onSynReplyAck (state : State active passive) (receipt : Receipt) : Except String (Effect active passive) := do
  match state.phase with
  | .idle => throw "An old-SYN ACK requires an earlier active OPEN."
  | .opened opened =>
    let _ ← discardBareAck opened receipt
    return { state, decision := .discarded }
  | .answered answered =>
    let _ ← discardBareAck answered.opened receipt
    return { state, decision := .discarded }
  | .acknowledged acknowledged client =>
    let applied ← client.receiveAck receipt.delivery.input receipt.index
    return { state := { state with phase := .acknowledged acknowledged applied.after }, application := some (.active, applied.operation) }
  | .complete complete client server =>
    let applied ← client.receiveAck receipt.delivery.input receipt.index
    return { state := { state with phase := .complete complete applied.after server }, application := some (.active, applied.operation) }

private def receive (state : State active passive) (index source : Nat) (bytes : List UInt8)
    (path : O.Path) (policy : Bool) : Except String (Effect active passive) := do
  if !policy then throw "The policy does not permit this startup receipt or response."
  let receipt ← receivePacket state index source bytes path
  let effect ← match receipt.source.kind, receipt.source.actor with
    | .syn, .active => onSyn state receipt policy
    | .synAck, .passive => onSynAck state receipt policy
    | .finalAck, .active => onFinalAck state receipt
    | .synReplyAck, .passive => onSynReplyAck state receipt
    | _, _ => throw "The selected startup occurrence has a different control actor."
  return retainReceipt effect receipt

private def canRetry : Side → Phase active passive → Bool
  | .active, .opened _ | .active, .answered _ => true
  | .passive, .answered _ | .passive, .acknowledged .. => true
  | _, _ => false

private def timerKind : Side → T.Kind
  | .active => .syn
  | .passive => .synAck

private def outputKind : Side → Kind
  | .active => .syn
  | .passive => .synAck

private def timeout (state : State active passive) (index : Nat) (actor : Side) (generation : Nat) (policy : Bool) :
    Except String (Effect active passive) := do
  match (state.timer actor).status with
  | .idle => throw "The selected endpoint has no startup timer generation."
  | .acknowledged _ _ => return { state, decision := .obsolete }
  | .pending flight =>
    if generation ≠ flight.retries then return { state, decision := .obsolete }
    if !policy then throw "The policy does not permit this startup retry."
    if !canRetry actor state.phase then throw "The selected endpoint no longer awaits its SYN acknowledgment."
    if flight.kind ≠ timerKind actor then throw "The startup timer names a different control kind."
    let some source := state.source flight.source | throw "The startup timer source occurrence is absent."
    if source.actor ≠ actor ∨ source.kind ≠ outputKind actor then
      throw "The startup timer source has a different actor or control kind."
    match computed : HandshakeTimer.expire (state.timer actor) generation with
    | .error _ => throw "The selected startup timer has not reached its current deadline."
    | .ok timer =>
      let next := state.withTimer actor timer (HandshakeTimer.expire_valid (state.timer_valid actor) computed)
      return publish next ⟨index, actor, source.kind, source.packet, .timeout source.index generation⟩

private def openConnection (state : State active passive) (index : Nat) (remote : H.Socket) (policy : Bool) :
    Except String (Effect active passive) := do
  match state.phase with
  | .idle =>
    match computed : Handshake.activeOpen active remote policy with
    | .error reason => throw reason.message
    | .ok pending =>
      let opened : O.Opened active := ⟨remote, policy, index, pending, computed⟩
      let next ← armTimer state .active .syn index
      return publish { next with phase := .opened opened } ⟨index, .active, .syn, pending.output, .open⟩
  | _ => throw "The selected connection has already processed active OPEN."

def evaluate (state : State active passive) (index : Nat) (event : Event) : Except String (Effect active passive) := do
  if !(state.last.isNone || decide (state.last.getD 0 < index)) then
    throw "Startup event indices must increase."
  let effect ← match event with
    | .activeOpen remote policy => openConnection state index remote policy
    | .receive source bytes path policy => receive state index source bytes path policy
    | .timeout actor generation policy => timeout state index actor generation policy
    | .advanceClock actor millis =>
      match computed : HandshakeTimer.advance (state.timer actor) millis with
      | .error _ => throw "A startup endpoint clock cannot move backward."
      | .ok timer => pure { state := state.withTimer actor timer (HandshakeTimer.advance_valid (state.timer_valid actor) computed) }
  return { effect with state := { effect.state with last := some index } }

structure Step (active passive : H.Local) where
  before : State active passive
  index : Nat
  event : Event
  result : Effect active passive
  computed : evaluate before index event = .ok result

private theorem armTimer_logs (computed : armTimer before actor kind source = .ok after) :
    after.emissions = before.emissions ∧ after.receipts = before.receipts := by
  unfold armTimer at computed
  split at computed
  · cases computed
  · simp only [Except.ok.injEq] at computed
    subst after
    cases actor <;> exact ⟨rfl, rfl⟩

private theorem ackTimer_logs (computed : ackTimer before actor kind source = .ok after) :
    after.emissions = before.emissions ∧ after.receipts = before.receipts := by
  unfold ackTimer at computed
  repeat' first
    | (solve | cases computed)
    | (split at computed)
    | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)
  all_goals
    simp only [Except.ok.injEq] at computed
    subst after
    cases actor <;> exact ⟨rfl, rfl⟩

private def OutputLog (before : State active passive) (index : Nat) (effect : Effect active passive) : Prop :=
  effect.state.emissions = before.emissions ++ effect.output.toList ∧
    effect.state.receipts = before.receipts ∧
    (∀ output, effect.output = some output → output.index = index) ∧
    (∀ actor operation, effect.application = some (actor, operation) → operation.stamp = index)

private theorem onSyn_log (computed : onSyn before receipt policy = .ok effect) :
    OutputLog before receipt.index effect := by
  unfold onSyn at computed
  repeat' first
    | (solve | cases computed)
    | (split at computed)
    | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)
  all_goals
    simp only [Except.ok.injEq] at computed
    subst effect
    dsimp only [OutputLog, respond, publish]
    all_goals first
      | exact ⟨rfl, rfl, by intro output selected; cases selected; rfl,
          by intro actor operation selected; cases selected⟩
      | (
        obtain ⟨emissions, receipts⟩ := armTimer_logs (by assumption)
        exact ⟨by rw [emissions]; rfl, receipts, by intro output selected; cases selected; rfl,
          by intro actor operation selected; cases selected⟩)

private theorem onSynAck_log (computed : onSynAck before receipt policy = .ok effect) :
    OutputLog before receipt.index effect := by
  unfold onSynAck at computed
  repeat' first
    | (solve | cases computed)
    | (split at computed)
    | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)
  all_goals
    simp only [Except.ok.injEq] at computed
    subst effect
    dsimp only [OutputLog, respond, publish]
    all_goals first
      | exact ⟨rfl, rfl, by intro output selected; cases selected; rfl,
          by intro actor operation selected; cases selected⟩
      | (
        obtain ⟨emissions, receipts⟩ := ackTimer_logs (by assumption)
        exact ⟨by rw [emissions]; rfl, receipts, by intro output selected; cases selected; rfl,
          by intro actor operation selected; cases selected⟩)

private theorem onFinalAck_log (computed : onFinalAck before receipt = .ok effect) :
    OutputLog before receipt.index effect := by
  unfold onFinalAck at computed
  repeat' first
    | (solve | cases computed)
    | (split at computed)
    | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)
  all_goals
    simp only [Except.ok.injEq] at computed
    subst effect
    dsimp only [OutputLog]
    all_goals first
      | (
        obtain ⟨emissions, receipts⟩ := ackTimer_logs (by assumption)
        refine ⟨?_, receipts, ?_, ?_⟩
        · simpa only [Option.toList_none, List.append_nil] using emissions
        · intro output selected; cases selected
        · intro actor operation selected; cases selected)
      | (
        refine ⟨by simp, rfl, ?_, ?_⟩
        · intro output selected; cases selected
        · intro actor operation selected
          cases selected
          exact ReceivedAck.stamp _)

private theorem onSynReplyAck_log (computed : onSynReplyAck before receipt = .ok effect) :
    OutputLog before receipt.index effect := by
  unfold onSynReplyAck at computed
  repeat' first
    | (solve | cases computed)
    | (split at computed)
    | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)
  all_goals
    simp only [Except.ok.injEq] at computed
    subst effect
    dsimp only [OutputLog]
    refine ⟨by simp, rfl, ?_, ?_⟩
    · intro output selected; cases selected
    · intro actor operation selected
      first
        | (solve | cases selected)
        | (cases selected; exact ReceivedAck.stamp _)

private theorem openConnection_log (computed : openConnection before index remote policy = .ok effect) :
    OutputLog before index effect := by
  unfold openConnection at computed
  repeat' first
    | (solve | cases computed)
    | (split at computed)
    | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)
  all_goals
    simp only [Except.ok.injEq] at computed
    subst effect
    obtain ⟨emissions, receipts⟩ := armTimer_logs (by assumption)
    dsimp only [OutputLog, publish]
    exact ⟨by rw [emissions]; rfl, receipts, by intro output selected; cases selected; rfl,
      by intro actor operation selected; cases selected⟩

private theorem timeout_log (computed : timeout before index actor generation policy = .ok effect) :
    OutputLog before index effect := by
  cases actor <;> unfold timeout at computed
  all_goals
    repeat' first
      | (solve | cases computed)
      | (split at computed)
      | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)
  all_goals
    simp only [Except.ok.injEq] at computed
    subst effect
    dsimp only [OutputLog, publish, State.withTimer]
    refine ⟨by simp, rfl, ?_, ?_⟩
    · intro output selected
      cases selected <;> rfl
    · intro selected operation present
      cases present

private theorem source_self {before : State active passive} {index : Nat} {output : Emission}
    (found : before.source index = some output) : before.source output.index = some output := by
  have selected := List.find?_some found
  have same : output.index = index := by simpa only [beq_iff_eq] using selected
  rw [same]
  exact found

private theorem receivePacket_fields (computed : receivePacket before index source bytes path = .ok receipt) :
    receipt.index = index ∧ before.source receipt.source.index = some receipt.source := by
  unfold receivePacket at computed
  repeat' first
    | (solve | cases computed)
    | (split at computed)
    | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)
  all_goals
    simp only [Except.ok.injEq] at computed
    subst receipt
    exact ⟨rfl, source_self (by assumption)⟩

structure Records (before : State active passive) (index : Nat) (effect : Effect active passive) : Prop where
  emissions : effect.state.emissions = before.emissions ++ effect.output.toList
  receipts : effect.state.receipts = before.receipts ++ effect.receipt.toList
  outputIndex : ∀ output, effect.output = some output → output.index = index
  receiptIndex : ∀ receipt, effect.receipt = some receipt → receipt.index = index
  source : ∀ receipt, effect.receipt = some receipt → before.source receipt.source.index = some receipt.source
  applicationIndex : ∀ actor operation, effect.application = some (actor, operation) → operation.stamp = index

private theorem retain_records
    (fields : receipt.index = index ∧ before.source receipt.source.index = some receipt.source)
    (log : OutputLog before receipt.index effect) : Records before index (retainReceipt effect receipt) := by
  refine ⟨log.1, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp only [retainReceipt]
    rw [log.2.1]
    rfl
  · intro output selected
    exact (log.2.2.1 output selected).trans fields.1
  · intro selected present
    cases present
    exact fields.1
  · intro selected present
    cases present
    exact fields.2
  · intro actor operation selected
    exact (log.2.2.2 actor operation selected).trans fields.1

private theorem receive_records (computed : receive before index source bytes path policy = .ok effect) :
    Records before index effect := by
  unfold receive at computed
  repeat' first
    | (solve | cases computed)
    | (split at computed)
    | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)
  all_goals
    simp only [Except.ok.injEq] at computed
    subst effect
    first
      | (solve | exact retain_records (receivePacket_fields (by assumption)) (onSyn_log (by assumption)))
      | (solve | exact retain_records (receivePacket_fields (by assumption)) (onSynAck_log (by assumption)))
      | (solve | exact retain_records (receivePacket_fields (by assumption)) (onFinalAck_log (by assumption)))
      | (solve | exact retain_records (receivePacket_fields (by assumption)) (onSynReplyAck_log (by assumption)))

private theorem openConnection_receipt (computed : openConnection before index remote policy = .ok effect) :
    effect.receipt = none := by
  unfold openConnection at computed
  repeat' first
    | (solve | cases computed)
    | (split at computed)
    | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)
  all_goals
    simp only [Except.ok.injEq] at computed
    subst effect
    rfl

private theorem timeout_receipt (computed : timeout before index actor generation policy = .ok effect) :
    effect.receipt = none := by
  unfold timeout at computed
  repeat' first
    | (solve | cases computed)
    | (split at computed)
    | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)
  all_goals
    simp only [Except.ok.injEq] at computed
    subst effect
    rfl

private theorem quiet_records (log : OutputLog before index effect) (absent : effect.receipt = none) :
    Records before index effect := by
  refine ⟨log.1, ?_, log.2.2.1, ?_, ?_, log.2.2.2⟩
  · simpa only [absent, Option.toList_none, List.append_nil] using log.2.1
  · intro receipt selected; rw [absent] at selected; cases selected
  · intro receipt selected; rw [absent] at selected; cases selected

private theorem Records.last (records : Records before index effect) :
    Records before index { effect with state := { effect.state with last := some index } } :=
  ⟨records.emissions, records.receipts, records.outputIndex, records.receiptIndex, records.source, records.applicationIndex⟩

private theorem clock_records (before : State active passive) (actor : Side) (timer : T.State)
    (valid : timer.Valid) (index : Nat) : Records before index { state := before.withTimer actor timer valid } := by
  cases actor <;> refine ⟨by simp [State.withTimer], by simp [State.withTimer], ?_, ?_, ?_, ?_⟩
  all_goals intros <;> contradiction

theorem evaluate_records (computed : evaluate before index event = .ok effect) : Records before index effect := by
  unfold evaluate at computed
  dsimp only at computed
  cases event <;>
    repeat' first
      | (solve | cases computed)
      | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)
      | (split at computed)
  all_goals
    simp only [Except.ok.injEq] at computed
    subst effect
    first
      | (solve | exact Records.last (receive_records (by assumption)))
      | (solve | exact Records.last (quiet_records (openConnection_log (by assumption)) (openConnection_receipt (by assumption))))
      | (solve | exact Records.last (quiet_records (timeout_log (by assumption)) (timeout_receipt (by assumption))))
      | (solve |
        rename_i actor millis legal timer advanced
        exact Records.last (clock_records before actor timer
          (HandshakeTimer.advance_valid (before.timer_valid actor) advanced) index))

theorem evaluate_last (computed : evaluate before index event = .ok effect) : effect.state.last = some index := by
  unfold evaluate at computed
  dsimp only at computed
  cases event <;>
    repeat' first
      | (solve | cases computed)
      | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)
      | (split at computed)
  all_goals simp only [Except.ok.injEq] at computed; subst effect; rfl

theorem evaluate_order (computed : evaluate before index event = .ok effect)
    (prior : before.last = some earlier) : earlier < index := by
  have guard : (before.last.isNone || decide (before.last.getD 0 < index)) = true := by
    cases valid : (before.last.isNone || decide (before.last.getD 0 < index)) with
    | true => rfl
    | false =>
      simp only [evaluate, valid, Bool.not_false, ite_true, bind, Except.bind] at computed
      cases computed
  simpa only [prior, Option.isNone_some, Option.getD_some, Bool.false_or, decide_eq_true_eq] using guard

theorem Step.records (actual : Step active passive) : Records actual.before actual.index actual.result :=
  evaluate_records actual.computed

theorem Step.last (actual : Step active passive) : actual.result.state.last = some actual.index :=
  evaluate_last actual.computed

theorem Step.after_prior (actual : Step active passive) (prior : actual.before.last = some earlier) : earlier < actual.index :=
  evaluate_order actual.computed prior

private theorem template_sources_frame (prior : TemplateSources before) (phase : after.phase = before.phase)
    (retained : before.emissions <+: after.emissions) : TemplateSources after := by
  unfold TemplateSources at prior ⊢
  rw [phase]
  cases current : before.phase with
  | idle => trivial
  | opened value =>
    simp only [current] at prior ⊢
    exact prior.retain retained
  | answered value | acknowledged value _ | complete value _ _ =>
    simp only [current] at prior ⊢
    exact ⟨prior.1.retain retained, prior.2.retain retained⟩

private theorem phase_timers_frame (prior : PhaseTimers before) (phase : after.phase = before.phase)
    (activeStatus : after.activeTimer.status = before.activeTimer.status)
    (passiveStatus : after.passiveTimer.status = before.passiveTimer.status) : PhaseTimers after := by
  unfold PhaseTimers at prior ⊢
  rw [phase]
  cases current : before.phase <;>
    simpa only [current, TimerPending, TimerClosed, activeStatus, passiveStatus] using prior

private theorem invariant_frame (prior : PhaseInvariant before) (phase : after.phase = before.phase)
    (activeStatus : after.activeTimer.status = before.activeTimer.status)
    (passiveStatus : after.passiveTimer.status = before.passiveTimer.status)
    (retained : before.emissions <+: after.emissions) : PhaseInvariant after := by
  refine ⟨phase_timers_frame prior.1 phase activeStatus passiveStatus, ?_, template_sources_frame prior.2.2 phase retained⟩
  unfold PreDataFrames at *
  rw [phase]
  exact prior.2.1

private theorem invariant_publish (prior : PhaseInvariant before) (output : Emission) : PhaseInvariant (publish before output).state :=
  invariant_frame prior rfl rfl rfl (List.prefix_append _ _)

private theorem invariant_clock (prior : PhaseInvariant before)
    (computed : HandshakeTimer.advance (before.timer actor) now = .ok timer) :
    PhaseInvariant (before.withTimer actor timer (HandshakeTimer.advance_valid (before.timer_valid actor) computed)) := by
  obtain ⟨_, rfl⟩ := HandshakeTimer.advance_eq computed
  cases actor <;> exact invariant_frame prior rfl rfl rfl (List.prefix_refl _)

private theorem invariant_expire (prior : PhaseInvariant before) (selected : canRetry actor before.phase = true)
    (computed : HandshakeTimer.expire (before.timer actor) generation = .ok timer) :
    PhaseInvariant (before.withTimer actor timer (HandshakeTimer.expire_valid (before.timer_valid actor) computed)) := by
  cases actor <;> cases phase : before.phase <;> simp only [canRetry, phase, Bool.false_eq_true] at selected
  all_goals
    have timers := prior.1
    simp only [PhaseTimers, phase] at timers
    refine ⟨?_, ?_, ?_⟩
    · simp only [PhaseTimers, State.withTimer, phase]
      first
        | exact ⟨timers.1.expire computed, timers.2⟩
        | exact ⟨timers.1, timers.2.expire computed⟩
    · exact prior.2.1
    · simpa only [TemplateSources, Template, State.withTimer, phase] using prior.2.2

private theorem armTimer_eq (computed : armTimer before actor kind source = .ok after) :
    ∃ timer, ∃ armed : HandshakeTimer.arm (before.timer actor) kind source = .ok timer,
      after = before.withTimer actor timer (HandshakeTimer.arm_valid (before.timer_valid actor) armed) := by
  unfold armTimer at computed
  split at computed
  · cases computed
  · simp only [Except.ok.injEq] at computed
    subst after
    exact ⟨_, by assumption, rfl⟩

private theorem ackTimer_eq (computed : ackTimer before actor kind source = .ok after) :
    ∃ timer, ∃ acknowledged : HandshakeTimer.acknowledge (before.timer actor) = .ok timer,
      after = before.withTimer actor timer (HandshakeTimer.acknowledge_valid (before.timer_valid actor) acknowledged) := by
  unfold ackTimer at computed
  repeat' first
    | (solve | cases computed)
    | (split at computed)
    | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)
  all_goals
    simp only [Except.ok.injEq] at computed
    subst after
    exact ⟨_, by assumption, rfl⟩

private theorem openConnection_invariant (prior : PhaseInvariant before)
    (computed : openConnection before index remote policy = .ok effect) : PhaseInvariant effect.state := by
  unfold openConnection at computed
  repeat' first
    | (solve | cases computed)
    | (split at computed)
    | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)
  all_goals
    simp only [Except.ok.injEq] at computed
    subst effect
    obtain ⟨timer, armed, rfl⟩ := armTimer_eq (by assumption)
    have phase : before.phase = .idle := by assumption
    have old := prior
    simp only [PhaseInvariant, PhaseTimers, PreDataFrames, TemplateSources, phase] at old
    dsimp only [PhaseInvariant, PhaseTimers, PreDataFrames, TemplateSources, publish, State.withTimer, State.timer]
    refine ⟨⟨TimerPending.arm armed, old.1.2⟩, trivial, ?_⟩
    exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), rfl, rfl, rfl, rfl⟩

private theorem onSyn_invariant (prior : PhaseInvariant before)
    (computed : onSyn before receipt policy = .ok effect) : PhaseInvariant effect.state := by
  unfold onSyn at computed
  repeat' first
    | (solve | cases computed)
    | (split at computed)
    | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)
  all_goals
    simp only [Except.ok.injEq] at computed
    subst effect
    first
      | (solve | exact invariant_publish prior _)
      | (solve |
        obtain ⟨timer, armed, rfl⟩ := armTimer_eq (by assumption)
        have old := prior
        simp only [PhaseInvariant, PhaseTimers, PreDataFrames, TemplateSources, *] at old
        dsimp only [PhaseInvariant, PhaseTimers, PreDataFrames, TemplateSources, respond, publish, State.withTimer, State.timer]
        refine ⟨⟨old.1.1, TimerPending.arm armed⟩, trivial, ?_, ?_⟩
        · exact old.2.2.retain (List.prefix_append _ _)
        · exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), rfl, rfl, rfl, rfl⟩)

private theorem onSynAck_invariant (prior : PhaseInvariant before)
    (computed : onSynAck before receipt policy = .ok effect) : PhaseInvariant effect.state := by
  unfold onSynAck at computed
  repeat' first
    | (solve | cases computed)
    | (split at computed)
    | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)
  all_goals
    simp only [Except.ok.injEq] at computed
    subst effect
    first
      | (solve | exact invariant_publish prior _)
      | (solve |
        obtain ⟨timer, acknowledged, rfl⟩ := ackTimer_eq (by assumption)
        have old := prior
        simp only [PhaseInvariant, PhaseTimers, PreDataFrames, TemplateSources, *] at old
        dsimp only [PhaseInvariant, PhaseTimers, PreDataFrames, TemplateSources, respond, publish, State.withTimer, State.timer]
        refine ⟨⟨TimerClosed.acknowledge old.1.1 acknowledged, old.1.2⟩, PreDataClean.active _ _ _, ?_, ?_⟩
        · exact old.2.2.1.retain (List.prefix_append _ _)
        · exact old.2.2.2.retain (List.prefix_append _ _))

private theorem timeout_invariant (prior : PhaseInvariant before)
    (computed : timeout before index actor generation policy = .ok effect) : PhaseInvariant effect.state := by
  unfold timeout at computed
  repeat' first
    | (solve | cases computed)
    | (split at computed)
    | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)
  all_goals
    simp only [Except.ok.injEq] at computed
    subst effect
    first
      | (solve | exact prior)
      | (solve |
        apply invariant_publish
        apply invariant_expire prior _ (by assumption)
        simpa using (by assumption : ¬ (!canRetry actor before.phase) = true))

private theorem received_ack_clean (prior : PreDataClean seed before)
    (applied : ReceivedAck before packet index) : PreDataClean seed applied.after := by
  have fields := prior.fields
  have received := Endpoint.receive_empty_ack_initial before.current packet before.valid
    fields.1 fields.2.1 fields.2.2.1 applied.tuple applied.profile.1
    (by simpa only [Handshake.optionProfile, ite_true] using applied.profile.2.1)
    applied.profile.2.2 applied.coordinates.1 applied.coordinates.2
  have result := applied.operation.computed
  rw [applied.event, ApplicationTrace.evaluate, applied.beforeEq, received] at result
  refine ⟨prior.1.trans ?_, prior.2⟩
  rw [applied.state, result]
  exact WindowFrame.windowState _ _

private theorem onFinalAck_invariant (prior : PhaseInvariant before)
    (computed : onFinalAck before receipt = .ok effect) : PhaseInvariant effect.state := by
  unfold onFinalAck at computed
  repeat' first
    | (solve | cases computed)
    | (split at computed)
    | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)
  all_goals
    simp only [Except.ok.injEq] at computed
    subst effect
    first
      | (solve |
        obtain ⟨timer, acknowledged, rfl⟩ := ackTimer_eq (by assumption)
        have old := prior
        simp only [PhaseInvariant, PhaseTimers, PreDataFrames, TemplateSources, *] at old
        dsimp only [PhaseInvariant, PhaseTimers, PreDataFrames, TemplateSources, finish, State.withTimer, State.timer]
        exact ⟨⟨old.1.1, TimerClosed.acknowledge old.1.2 acknowledged⟩,
          ⟨old.2.1, PreDataClean.passive _ _ _⟩, old.2.2⟩)
      | (solve |
        have old := prior
        simp only [PhaseInvariant, PhaseTimers, PreDataFrames, TemplateSources, *] at old
        dsimp only [PhaseInvariant, PhaseTimers, PreDataFrames, TemplateSources]
        exact ⟨old.1, ⟨old.2.1.1, received_ack_clean old.2.1.2 _⟩, old.2.2⟩)

private theorem onSynReplyAck_invariant (prior : PhaseInvariant before)
    (computed : onSynReplyAck before receipt = .ok effect) : PhaseInvariant effect.state := by
  unfold onSynReplyAck at computed
  repeat' first
    | (solve | cases computed)
    | (split at computed)
    | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)
  all_goals
    simp only [Except.ok.injEq] at computed
    subst effect
    first
      | (solve | exact prior)
      | (solve |
        have old := prior
        simp only [PhaseInvariant, PhaseTimers, PreDataFrames, TemplateSources, *] at old
        dsimp only [PhaseInvariant, PhaseTimers, PreDataFrames, TemplateSources]
        exact ⟨old.1, received_ack_clean old.2.1 _, old.2.2⟩)
      | (solve |
        have old := prior
        simp only [PhaseInvariant, PhaseTimers, PreDataFrames, TemplateSources, *] at old
        dsimp only [PhaseInvariant, PhaseTimers, PreDataFrames, TemplateSources]
        exact ⟨old.1, ⟨received_ack_clean old.2.1.1 _, old.2.1.2⟩, old.2.2⟩)

private theorem invariant_retain (prior : PhaseInvariant effect.state) (receipt : Receipt) :
    PhaseInvariant (retainReceipt effect receipt).state :=
  invariant_frame prior rfl rfl rfl (List.prefix_refl _)

private theorem receive_invariant (prior : PhaseInvariant before)
    (computed : receive before index source bytes path policy = .ok effect) : PhaseInvariant effect.state := by
  unfold receive at computed
  repeat' first
    | (solve | cases computed)
    | (split at computed)
    | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)
  all_goals
    simp only [Except.ok.injEq] at computed
    subst effect
    apply invariant_retain
    first
      | exact onSyn_invariant prior (by assumption)
      | exact onSynAck_invariant prior (by assumption)
      | exact onFinalAck_invariant prior (by assumption)
      | exact onSynReplyAck_invariant prior (by assumption)

theorem evaluate_invariant (prior : PhaseInvariant before)
    (computed : evaluate before index event = .ok effect) : PhaseInvariant effect.state := by
  unfold evaluate at computed
  dsimp only at computed
  cases event <;>
    repeat' first
      | (solve | cases computed)
      | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)
      | (split at computed)
  all_goals
    simp only [Except.ok.injEq] at computed
    subst effect
    first
      | (solve | exact (openConnection_invariant prior (by assumption)).last)
      | (solve | exact (receive_invariant prior (by assumption)).last)
      | (solve | exact (timeout_invariant prior (by assumption)).last)
      | (solve | exact (invariant_clock prior (by assumption)).last)

theorem Step.phase_invariant (actual : Step active passive) (prior : PhaseInvariant actual.before) :
    PhaseInvariant actual.result.state := evaluate_invariant prior actual.computed

private def ApplicationLog (before : State active passive) (effect : Effect active passive) : Prop :=
  ∀ actor, effect.state.applicationSteps actor =
    before.applicationSteps actor ++ (applicationFor actor effect.application).toList

private theorem ApplicationLog.retain (log : ApplicationLog before effect) (receipt : Receipt) :
    ApplicationLog before (retainReceipt effect receipt) := log

private theorem ApplicationLog.last (log : ApplicationLog before effect) :
    ApplicationLog before { effect with state := { effect.state with last := some index } } := log

private theorem application_receipt_last (prior : ApplicationReceipt effect index actor operation) :
    ApplicationReceipt { effect with state := { effect.state with last := some index } } index actor operation := prior

private theorem armTimer_steps (computed : armTimer before actor kind source = .ok after) :
    ∀ selected, after.applicationSteps selected = before.applicationSteps selected := by
  obtain ⟨timer, armed, rfl⟩ := armTimer_eq computed
  cases actor <;> intro selected <;> rfl

private theorem ackTimer_steps (computed : ackTimer before actor kind source = .ok after) :
    ∀ selected, after.applicationSteps selected = before.applicationSteps selected := by
  obtain ⟨timer, acknowledged, rfl⟩ := ackTimer_eq computed
  cases actor <;> intro selected <;> rfl

private theorem openConnection_applications (computed : openConnection before index remote policy = .ok effect) :
    ApplicationLog before effect := by
  unfold openConnection at computed
  repeat' first
    | (solve | cases computed)
    | (split at computed)
    | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)
  all_goals
    simp only [Except.ok.injEq] at computed
    subst effect
    intro actor
    cases actor <;> simp [State.applicationSteps, applicationFor, publish, *]
    all_goals rfl

private theorem onSyn_applications (computed : onSyn before receipt policy = .ok effect) :
    ApplicationLog before effect := by
  unfold onSyn at computed
  repeat' first
    | (solve | cases computed)
    | (split at computed)
    | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)
  all_goals
    simp only [Except.ok.injEq] at computed
    subst effect
    intro actor
    cases actor <;> simp [State.applicationSteps, applicationFor, respond, publish, *]
    all_goals rfl

private theorem onSynAck_applications (computed : onSynAck before receipt policy = .ok effect) :
    ApplicationLog before effect := by
  unfold onSynAck at computed
  repeat' first
    | (solve | cases computed)
    | (split at computed)
    | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)
  all_goals
    simp only [Except.ok.injEq] at computed
    subst effect
    intro actor
    cases actor <;> simp [State.applicationSteps, applicationFor, respond, publish, PreData.initial, *]
    all_goals rfl

private theorem onFinalAck_applications (computed : onFinalAck before receipt = .ok effect) :
    ApplicationLog before effect := by
  unfold onFinalAck at computed
  repeat' first
    | (solve | cases computed)
    | (split at computed)
    | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)
  all_goals
    simp only [Except.ok.injEq] at computed
    subst effect
    first
      | (solve |
        obtain ⟨timer, acknowledged, rfl⟩ := ackTimer_eq (by assumption)
        intro actor
        cases actor <;> simp [State.applicationSteps, applicationFor, PreData.initial, *]
        all_goals rfl)
      | (solve |
        intro actor
        cases actor <;> simp [State.applicationSteps, applicationFor, ReceivedAck.history, *]
        all_goals rfl)

private theorem onSynReplyAck_applications (computed : onSynReplyAck before receipt = .ok effect) :
    ApplicationLog before effect := by
  unfold onSynReplyAck at computed
  repeat' first
    | (solve | cases computed)
    | (split at computed)
    | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)
  all_goals
    simp only [Except.ok.injEq] at computed
    subst effect
    intro actor
    cases actor <;> simp [State.applicationSteps, applicationFor, ReceivedAck.history, *]
    all_goals rfl

private theorem received_ack_operation (applied : ReceivedAck before packet index) :
    AckOperation packet index applied.operation := by
  refine ⟨applied.profile, applied.event, ?_, ?_, ?_, applied.accepted, applied.quiet, applied.read, applied.stamp⟩
  all_goals rw [applied.beforeEq]
  · exact applied.tuple
  · exact applied.coordinates.1
  · exact applied.coordinates.2

private theorem onSyn_no_application (computed : onSyn before receipt policy = .ok effect) : effect.application = none := by
  unfold onSyn at computed
  repeat' first
    | (solve | cases computed)
    | (split at computed)
    | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)
  all_goals simp only [Except.ok.injEq] at computed; subst effect; rfl

private theorem onSynAck_no_application (computed : onSynAck before receipt policy = .ok effect) : effect.application = none := by
  unfold onSynAck at computed
  repeat' first
    | (solve | cases computed)
    | (split at computed)
    | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)
  all_goals simp only [Except.ok.injEq] at computed; subst effect; rfl

private theorem onFinalAck_operation (computed : onFinalAck before receipt = .ok effect)
    (selected : effect.application = some (actor, operation)) :
    actor = .passive ∧ AckOperation receipt.delivery.input receipt.index operation := by
  unfold onFinalAck at computed
  repeat' first
    | (solve | cases computed)
    | (split at computed)
    | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)
  all_goals
    simp only [Except.ok.injEq] at computed
    subst effect
    cases selected <;> exact ⟨rfl, received_ack_operation _⟩

private theorem onSynReplyAck_operation (computed : onSynReplyAck before receipt = .ok effect)
    (selected : effect.application = some (actor, operation)) :
    actor = .active ∧ AckOperation receipt.delivery.input receipt.index operation := by
  unfold onSynReplyAck at computed
  repeat' first
    | (solve | cases computed)
    | (split at computed)
    | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)
  all_goals
    simp only [Except.ok.injEq] at computed
    subst effect
    cases selected <;> exact ⟨rfl, received_ack_operation _⟩

private theorem receive_application (computed : receive before index source bytes path policy = .ok effect)
    (selected : effect.application = some (actor, operation)) : ApplicationReceipt effect index actor operation := by
  unfold receive at computed
  repeat' first
    | (solve | cases computed)
    | (split at computed)
    | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)
  all_goals
    simp only [Except.ok.injEq] at computed
    subst effect
    dsimp only [retainReceipt] at selected
    first
      | (solve | have absent := onSyn_no_application (before := before) (policy := policy) (by assumption); rw [absent] at selected; cases selected)
      | (solve | have absent := onSynAck_no_application (before := before) (policy := policy) (by assumption); rw [absent] at selected; cases selected)
      | (solve |
        obtain ⟨side, ack⟩ := onFinalAck_operation (by assumption) selected
        have fields := receivePacket_fields (before := before) (index := index) (source := source) (bytes := bytes) (path := path) (by assumption)
        refine ⟨_, rfl, ?_, ?_⟩
        · simp only [Receipt.actor, Side.other, *]
        · simpa only [fields.1] using ack)
      | (solve |
        obtain ⟨side, ack⟩ := onSynReplyAck_operation (by assumption) selected
        have fields := receivePacket_fields (before := before) (index := index) (source := source) (bytes := bytes) (path := path) (by assumption)
        refine ⟨_, rfl, ?_, ?_⟩
        · simp only [Receipt.actor, Side.other, *]
        · simpa only [fields.1] using ack)

private theorem receive_applications (computed : receive before index source bytes path policy = .ok effect) :
    ApplicationLog before effect := by
  unfold receive at computed
  repeat' first
    | (solve | cases computed)
    | (split at computed)
    | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)
  all_goals
    simp only [Except.ok.injEq] at computed
    subst effect
    first
      | (solve | exact ApplicationLog.retain (onSyn_applications (by assumption)) _)
      | (solve | exact ApplicationLog.retain (onSynAck_applications (by assumption)) _)
      | (solve | exact ApplicationLog.retain (onFinalAck_applications (by assumption)) _)
      | (solve | exact ApplicationLog.retain (onSynReplyAck_applications (by assumption)) _)

private theorem timeout_applications (computed : timeout before index actor generation policy = .ok effect) :
    ApplicationLog before effect := by
  unfold timeout at computed
  repeat' first
    | (solve | cases computed)
    | (split at computed)
    | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)
  all_goals
    simp only [Except.ok.injEq] at computed
    subst effect
    intro selected
    cases actor <;> simp [State.applicationSteps, State.withTimer, applicationFor, publish]

private theorem openConnection_no_application (computed : openConnection before index remote policy = .ok effect) :
    effect.application = none := by
  unfold openConnection at computed
  repeat' first
    | (solve | cases computed)
    | (split at computed)
    | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)
  all_goals simp only [Except.ok.injEq] at computed; subst effect; rfl

private theorem timeout_no_application (computed : timeout before index actor generation policy = .ok effect) :
    effect.application = none := by
  unfold timeout at computed
  repeat' first
    | (solve | cases computed)
    | (split at computed)
    | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)
  all_goals simp only [Except.ok.injEq] at computed; subst effect; rfl

private theorem clock_applications (before : State active passive) (actor : Side) (timer : T.State) (valid : timer.Valid) :
    ApplicationLog before { state := before.withTimer actor timer valid } := by
  intro selected
  cases actor <;> simp [State.applicationSteps, State.withTimer, applicationFor]

theorem evaluate_application_steps (computed : evaluate before index event = .ok effect) :
    ∀ actor, effect.state.applicationSteps actor =
      before.applicationSteps actor ++ (applicationFor actor effect.application).toList := by
  unfold evaluate at computed
  dsimp only at computed
  cases event <;>
    repeat' first
      | (solve | cases computed)
      | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)
      | (split at computed)
  all_goals
    simp only [Except.ok.injEq] at computed
    subst effect
    first
      | (solve | exact ApplicationLog.last (openConnection_applications (by assumption)))
      | (solve | exact ApplicationLog.last (receive_applications (by assumption)))
      | (solve | exact ApplicationLog.last (timeout_applications (by assumption)))
      | (solve |
        rename_i actor millis legal timer advanced
        exact ApplicationLog.last (clock_applications before actor timer (HandshakeTimer.advance_valid (before.timer_valid actor) advanced)))

theorem evaluate_application_receipt (computed : evaluate before index event = .ok effect)
    (selected : effect.application = some (actor, operation)) : ApplicationReceipt effect index actor operation := by
  unfold evaluate at computed
  dsimp only at computed
  cases event <;>
    repeat' first
      | (solve | cases computed)
      | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)
      | (split at computed)
  all_goals
    simp only [Except.ok.injEq] at computed
    subst effect
    dsimp only at selected
    first
      | (solve | exact application_receipt_last (receive_application (by assumption) selected))
      | (solve | have absent := openConnection_no_application (before := before) (index := index) (by assumption); rw [absent] at selected; cases selected)
      | (solve | have absent := timeout_no_application (before := before) (index := index) (by assumption); rw [absent] at selected; cases selected)
      | (solve | cases selected)

theorem Step.application_steps (actual : Step active passive) (actor : Side) :
    actual.result.state.applicationSteps actor = actual.before.applicationSteps actor ++
      (applicationFor actor actual.result.application).toList := evaluate_application_steps actual.computed actor

theorem Step.application_receipt (actual : Step active passive)
    (selected : actual.result.application = some (actor, operation)) : ApplicationReceipt actual.result actual.index actor operation :=
  evaluate_application_receipt actual.computed selected

private theorem recovery_input_bytes (computed : EstablishedReceive.input bytes = .ok packet) : packet.bytes = bytes := by
  unfold EstablishedReceive.input at computed
  split at computed <;> cases computed
  rfl

private theorem receivePacket_details (computed : receivePacket before index source bytes path = .ok receipt) :
    receipt.index = index ∧ before.source source = some receipt.source ∧
      receipt.source.index = source ∧ receipt.delivery.input.bytes = bytes := by
  unfold receivePacket at computed
  repeat' first
    | (solve | cases computed)
    | (split at computed)
    | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)
  all_goals
    simp only [Except.ok.injEq] at computed
    subst receipt
    rename_i selectedOption selected found earlier candidateResult candidate decoded deliveryResult delivery checked
    refine ⟨rfl, found, ?_, ?_⟩
    · simpa only [beq_iff_eq] using List.find?_some found
    · rw [HandshakeExchange.Delivery.bytes]
      have raw := recovery_input_bytes decoded
      cases path <;> exact raw

private theorem receive_details (computed : receive before index source bytes path policy = .ok effect) :
    ∃ receipt, effect.receipt = some receipt ∧ before.source source = some receipt.source ∧
      receipt.source.index = source ∧ receipt.delivery.input.bytes = bytes := by
  unfold receive at computed
  repeat' first
    | (solve | cases computed)
    | (split at computed)
    | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)
  all_goals
    simp only [Except.ok.injEq] at computed
    subst effect
    have fields := receivePacket_details (before := before) (index := index) (source := source)
      (bytes := bytes) (path := path) (by assumption)
    exact ⟨_, rfl, fields.2.1, fields.2.2⟩

theorem evaluate_receive_receipt_details (computed : evaluate before index (.receive source bytes path policy) = .ok effect) :
    ∃ receipt, effect.receipt = some receipt ∧ before.source source = some receipt.source ∧
      receipt.source.index = source ∧ receipt.delivery.input.bytes = bytes := by
  unfold evaluate at computed
  dsimp only at computed
  repeat' first
    | (solve | cases computed)
    | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)
    | (split at computed)
  all_goals
    simp only [Except.ok.injEq] at computed
    subst effect
    rename_i legal intermediate selected received
    exact receive_details (effect := selected) received

theorem evaluate_application_event (computed : evaluate before index event = .ok effect)
    (selected : effect.application = some (actor, operation)) :
    ∃ source bytes path policy, event = .receive source bytes path policy := by
  cases event with
  | receive source bytes path policy => exact ⟨source, bytes, path, policy, rfl⟩
  | activeOpen remote policy | timeout side generation policy | advanceClock side millis =>
    unfold evaluate at computed
    dsimp only at computed
    repeat' first
      | (solve | cases computed)
      | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)
      | (split at computed)
    all_goals
      simp only [Except.ok.injEq] at computed
      subst effect
      dsimp only at selected
      first
        | (solve | have absent := openConnection_no_application (before := before) (index := index) (by assumption); rw [absent] at selected; cases selected)
        | (solve | have absent := timeout_no_application (before := before) (index := index) (by assumption); rw [absent] at selected; cases selected)
        | (solve | cases selected)

theorem Step.application_event (actual : Step active passive)
    (selected : actual.result.application = some (actor, operation)) :
    ∃ source bytes path policy, actual.event = .receive source bytes path policy :=
  evaluate_application_event actual.computed selected

variable {active passive : H.Local} {before : State active passive} {effect : Effect active passive} {output : Emission}

private theorem onSyn_output_shape (prior : PhaseInvariant before)
    (computed : onSyn before receipt policy = .ok effect) (emitted : effect.output = some output) :
    OutputShape active passive output := by
  cases phase : before.phase with
  | idle => simp [onSyn, phase] at computed
  | opened opened =>
    simp only [onSyn, phase] at computed
    repeat' first
      | (solve | cases computed)
      | (split at computed)
      | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)
    rename_i same sourceEq pending listened result next timerEq
    simp only [Except.ok.injEq] at computed
    subst effect
    cases emitted
    exact Answered.output_shape ⟨opened, policy, receipt.index, receipt.spec,
      same.property ▸ receipt.delivery, pending, listened⟩
  | answered answered =>
    simp only [onSyn, phase] at computed
    repeat' first
      | (solve | cases computed)
      | (split at computed)
      | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)
    simp only [Except.ok.injEq] at computed
    subst effect
    cases emitted
    exact Answered.reply_shape answered
  | acknowledged acknowledged client =>
    simp only [onSyn, phase] at computed
    repeat' first
      | (solve | cases computed)
      | (split at computed)
      | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)
    simp only [Except.ok.injEq] at computed
    subst effect
    cases emitted
    exact Answered.reply_shape acknowledged.answered
  | complete complete client server =>
    simp only [onSyn, phase] at computed
    repeat' first
      | (solve | cases computed)
      | (split at computed)
      | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)
    simp only [Except.ok.injEq] at computed
    subst effect
    cases emitted
    have clean := prior.2.1
    simp only [PreDataFrames, phase] at clean
    exact Completed.current_passive_ack_shape complete clean.2 _

private theorem onSynAck_output_shape (prior : PhaseInvariant before)
    (computed : onSynAck before receipt policy = .ok effect) (emitted : effect.output = some output) :
    OutputShape active passive output := by
  cases phase : before.phase with
  | idle | opened opened => simp [onSynAck, phase] at computed
  | answered answered =>
    simp only [onSynAck, phase] at computed
    repeat' first
      | (solve | cases computed)
      | (split at computed)
      | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)
    rename_i same sourceEq ready received result next timerEq
    simp only [Except.ok.injEq] at computed
    subst effect
    cases emitted
    exact Acknowledged.output_shape ⟨answered, policy, receipt.index, receipt.spec,
      same.property ▸ receipt.delivery, ready, received⟩
  | acknowledged acknowledged client =>
    simp only [onSynAck, phase] at computed
    repeat' first
      | (solve | cases computed)
      | (split at computed)
      | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)
    simp only [Except.ok.injEq] at computed
    subst effect
    cases emitted
    have clean := prior.2.1
    simp only [PreDataFrames, phase] at clean
    exact Acknowledged.current_ack_shape acknowledged clean _
  | complete complete client server =>
    simp only [onSynAck, phase] at computed
    repeat' first
      | (solve | cases computed)
      | (split at computed)
      | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)
    simp only [Except.ok.injEq] at computed
    subst effect
    cases emitted
    have clean := prior.2.1
    simp only [PreDataFrames, phase] at clean
    exact Completed.current_active_ack_shape complete clean.1 _

private theorem onFinalAck_no_output (computed : onFinalAck before receipt = .ok effect) : effect.output = none := by
  unfold onFinalAck at computed
  repeat' first
    | (solve | cases computed)
    | (split at computed)
    | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)
  all_goals simp only [Except.ok.injEq] at computed; subst effect; rfl

private theorem onSynReplyAck_no_output (computed : onSynReplyAck before receipt = .ok effect) : effect.output = none := by
  unfold onSynReplyAck at computed
  repeat' first
    | (solve | cases computed)
    | (split at computed)
    | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)
  all_goals simp only [Except.ok.injEq] at computed; subst effect; rfl

private theorem receive_output_shape (prior : PhaseInvariant before)
    (computed : receive before index source bytes path policy = .ok effect) (emitted : effect.output = some output) :
    OutputShape active passive output := by
  unfold receive at computed
  repeat' first
    | (solve | cases computed)
    | (split at computed)
    | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)
  all_goals
    simp only [Except.ok.injEq] at computed
    subst effect
    dsimp only [retainReceipt] at emitted
    first
      | (solve | exact onSyn_output_shape prior (by assumption) emitted)
      | (solve | exact onSynAck_output_shape prior (by assumption) emitted)
      | (solve | have quiet := onFinalAck_no_output (by assumption); rw [quiet] at emitted; cases emitted)
      | (solve | have quiet := onSynReplyAck_no_output (by assumption); rw [quiet] at emitted; cases emitted)

private theorem openConnection_output_shape (computed : openConnection before index remote policy = .ok effect)
    (emitted : effect.output = some output) : OutputShape active passive output := by
  unfold openConnection at computed
  repeat' first
    | (solve | cases computed)
    | (split at computed)
    | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)
  all_goals
    simp only [Except.ok.injEq] at computed
    subst effect
    cases emitted
    rename_i pending opened result next armed
    exact Opened.output_shape (passive := passive) ⟨remote, policy, index, pending, opened⟩

private theorem timeout_output_shape (inventory : OutputInventory before)
    (computed : timeout before index actor generation policy = .ok effect) (emitted : effect.output = some output) :
    OutputShape active passive output := by
  unfold timeout at computed
  repeat' first
    | (solve | cases computed)
    | (split at computed)
    | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)
  all_goals
    simp only [Except.ok.injEq] at computed
    subst effect
    first
      | (solve | cases emitted)
      | (
        cases emitted
        have shape := inventory.source_shape (by assumption)
        exact { shape with
          actorEq := by
            have coordinate := shape.actorEq
            simp_all only [not_or, ne_eq, Decidable.not_not]
            cases actor <;> rfl })

theorem evaluate_output_shape (prior : PhaseInvariant before) (inventory : OutputInventory before)
    (computed : evaluate before index event = .ok effect) (emitted : effect.output = some output) :
    OutputShape active passive output := by
  unfold evaluate at computed
  dsimp only at computed
  cases event <;>
    repeat' first
      | (solve | cases computed)
      | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)
      | (split at computed)
  all_goals
    simp only [Except.ok.injEq] at computed
    subst effect
    rename_i result operation
    first
      | (solve |
        have core := operation
        change openConnection before index _ _ = .ok _ at core
        exact openConnection_output_shape (output := output) core emitted)
      | (solve |
        have core := operation
        change receive before index _ _ _ _ = .ok _ at core
        exact receive_output_shape (output := output) prior core emitted)
      | (solve |
        have core := operation
        change timeout before index _ _ _ = .ok _ at core
        exact timeout_output_shape (output := output) inventory core emitted)
      | (solve | cases emitted)

private theorem onSyn_packet_inventory (prior : PhaseInvariant before) (inventory : PacketInventory before)
    (computed : onSyn before receipt policy = .ok effect) : PacketInventory effect.state := by
  cases phase : before.phase with
  | idle => simp [onSyn, phase] at computed
  | opened opened =>
    simp only [onSyn, phase] at computed
    repeat' first
      | (solve | cases computed)
      | (split at computed)
      | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)
    rename_i same sourceEq pending listened result next timerEq
    simp only [Except.ok.injEq] at computed
    subst effect
    apply PacketInventory.publish
    · apply inventory.reframe
      · rw [phase]
        exact Phase.PacketFrame.answered ⟨opened, policy, receipt.index, receipt.spec,
          same.property ▸ receipt.delivery, pending, listened⟩
      · exact (armTimer_logs timerEq).1
    · rfl
    · intro control; rfl
  | answered answered =>
    simp only [onSyn, phase] at computed
    repeat' first
      | (solve | cases computed)
      | (split at computed)
      | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)
    simp only [Except.ok.injEq] at computed
    subst effect
    apply PacketInventory.publish inventory
    · simp only [phase, Phase.sourceHeader]
      exact congrArg some (Answered.reply_header answered).symm
    · intro control; rcases control with impossible | impossible <;> cases impossible
  | acknowledged acknowledged client =>
    simp only [onSyn, phase] at computed
    repeat' first
      | (solve | cases computed)
      | (split at computed)
      | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)
    simp only [Except.ok.injEq] at computed
    subst effect
    apply PacketInventory.publish inventory
    · simp only [phase, Phase.sourceHeader]
      exact congrArg some (Answered.reply_header acknowledged.answered).symm
    · intro control; rcases control with impossible | impossible <;> cases impossible
  | complete complete client server =>
    simp only [onSyn, phase] at computed
    repeat' first
      | (solve | cases computed)
      | (split at computed)
      | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)
    simp only [Except.ok.injEq] at computed
    subst effect
    have clean := prior.2.1
    simp only [PreDataFrames, phase] at clean
    apply PacketInventory.publish inventory
    · simp only [phase, Phase.sourceHeader]
      exact congrArg some (Completed.current_passive_ack_header complete clean.2 _).symm
    · intro control; rcases control with impossible | impossible <;> cases impossible

private theorem onSynAck_packet_inventory (prior : PhaseInvariant before) (inventory : PacketInventory before)
    (computed : onSynAck before receipt policy = .ok effect) : PacketInventory effect.state := by
  cases phase : before.phase with
  | idle | opened opened => simp [onSynAck, phase] at computed
  | answered answered =>
    simp only [onSynAck, phase] at computed
    repeat' first
      | (solve | cases computed)
      | (split at computed)
      | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)
    rename_i same sourceEq ready received result next timerEq
    simp only [Except.ok.injEq] at computed
    subst effect
    let acknowledged : O.Acknowledged active passive := ⟨answered, policy, receipt.index, receipt.spec,
      same.property ▸ receipt.delivery, ready, received⟩
    apply PacketInventory.publish
    · apply inventory.reframe
      · rw [phase]
        exact Phase.PacketFrame.acknowledged acknowledged _
      · exact (ackTimer_logs timerEq).1
    · exact congrArg some (Acknowledged.output_header acknowledged).symm
    · intro control; rcases control with impossible | impossible <;> cases impossible
  | acknowledged acknowledged client =>
    simp only [onSynAck, phase] at computed
    repeat' first
      | (solve | cases computed)
      | (split at computed)
      | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)
    simp only [Except.ok.injEq] at computed
    subst effect
    have clean := prior.2.1
    simp only [PreDataFrames, phase] at clean
    apply PacketInventory.publish inventory
    · simp only [phase, Phase.sourceHeader]
      exact congrArg some (Acknowledged.current_ack_header acknowledged clean _).symm
    · intro control; rcases control with impossible | impossible <;> cases impossible
  | complete complete client server =>
    simp only [onSynAck, phase] at computed
    repeat' first
      | (solve | cases computed)
      | (split at computed)
      | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)
    simp only [Except.ok.injEq] at computed
    subst effect
    have clean := prior.2.1
    simp only [PreDataFrames, phase] at clean
    apply PacketInventory.publish inventory
    · simp only [phase, Phase.sourceHeader]
      exact congrArg some (Completed.current_active_ack_header complete clean.1 _).symm
    · intro control; rcases control with impossible | impossible <;> cases impossible

private theorem openConnection_packet_inventory (inventory : PacketInventory before)
    (computed : openConnection before index remote policy = .ok effect) : PacketInventory effect.state := by
  unfold openConnection at computed
  repeat' first
    | (solve | cases computed)
    | (split at computed)
    | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)
  all_goals
    simp only [Except.ok.injEq] at computed
    subst effect
    rename_i pending opened result next timerEq
    apply PacketInventory.publish
    · apply inventory.reframe
      · rw [show before.phase = .idle by assumption]
        exact Phase.PacketFrame.initial _
      · exact (armTimer_logs timerEq).1
    · rfl
    · intro control; rfl

private theorem onFinalAck_packet_inventory (inventory : PacketInventory before)
    (computed : onFinalAck before receipt = .ok effect) : PacketInventory effect.state := by
  cases phase : before.phase with
  | idle | opened opened | answered answered => simp [onFinalAck, phase] at computed
  | acknowledged acknowledged client =>
    simp only [onFinalAck, phase] at computed
    repeat' first
      | (solve | cases computed)
      | (split at computed)
      | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)
    simp only [Except.ok.injEq] at computed
    subst effect
    rename_i next timerEq
    apply inventory.reframe
    · rw [phase]
      exact Phase.PacketFrame.finish acknowledged receipt.index receipt.spec _ _ _ _ client
    · exact (ackTimer_logs (after := next) timerEq).1
  | complete complete client server =>
    simp only [onFinalAck, phase] at computed
    repeat' first
      | (solve | cases computed)
      | (split at computed)
      | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)
    simp only [Except.ok.injEq] at computed
    subst effect
    apply inventory.reframe
    · rw [phase]
      exact Phase.PacketFrame.complete_current complete _ _ _ _
    · rfl

private theorem onSynReplyAck_packet_inventory (inventory : PacketInventory before)
    (computed : onSynReplyAck before receipt = .ok effect) : PacketInventory effect.state := by
  cases phase : before.phase with
  | idle => simp [onSynReplyAck, phase] at computed
  | opened opened | answered opened =>
    simp only [onSynReplyAck, phase] at computed
    repeat' first
      | (solve | cases computed)
      | (split at computed)
      | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)
    cases computed
    exact inventory
  | acknowledged acknowledged client =>
    simp only [onSynReplyAck, phase] at computed
    repeat' first
      | (solve | cases computed)
      | (split at computed)
      | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)
    simp only [Except.ok.injEq] at computed
    subst effect
    apply inventory.reframe
    · rw [phase]
      exact Phase.PacketFrame.acknowledged_current acknowledged _ _
    · rfl
  | complete complete client server =>
    simp only [onSynReplyAck, phase] at computed
    repeat' first
      | (solve | cases computed)
      | (split at computed)
      | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)
    simp only [Except.ok.injEq] at computed
    subst effect
    apply inventory.reframe
    · rw [phase]
      exact Phase.PacketFrame.complete_current complete _ _ _ _
    · rfl

private theorem packet_inventory_same (inventory : PacketInventory before)
    (phase : after.phase = before.phase) (emissions : after.emissions = before.emissions) : PacketInventory after :=
  inventory.reframe (by rw [phase]; exact Phase.PacketFrame.refl _) emissions

private theorem timeout_packet_inventory (inventory : PacketInventory before)
    (computed : timeout before index actor generation policy = .ok effect) : PacketInventory effect.state := by
  unfold timeout at computed
  repeat' first
    | (solve | cases computed)
    | (split at computed)
    | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)
  all_goals
    simp only [Except.ok.injEq] at computed
    subst effect
    first
      | (solve | exact inventory)
      | (
        rename_i original sourceEq timer expired correct kind retry permitted
        apply PacketInventory.publish
        · cases actor <;> exact packet_inventory_same inventory rfl rfl
        · have header := inventory.headers original (List.mem_of_find?_eq_some sourceEq)
          cases actor <;> simp_all only [State.withTimer, not_or, ne_eq, Decidable.not_not]
        · intro control
          have template := inventory.templates original (List.mem_of_find?_eq_some sourceEq) control
          cases actor <;> exact template)

private theorem packet_inventory_retain (inventory : PacketInventory effect.state) (receipt : Receipt) :
    PacketInventory (retainReceipt effect receipt).state := ⟨inventory.headers, inventory.templates⟩

private theorem packet_inventory_last (inventory : PacketInventory before) (index : Nat) :
    PacketInventory { before with last := some index } := ⟨inventory.headers, inventory.templates⟩

private theorem packet_inventory_clock (inventory : PacketInventory before)
    (computed : HandshakeTimer.advance (before.timer actor) now = .ok timer) :
    PacketInventory (before.withTimer actor timer (HandshakeTimer.advance_valid (before.timer_valid actor) computed)) := by
  cases actor <;> exact ⟨inventory.headers, inventory.templates⟩

private theorem receive_packet_inventory (prior : PhaseInvariant before) (inventory : PacketInventory before)
    (computed : receive before index source bytes path policy = .ok effect) : PacketInventory effect.state := by
  unfold receive at computed
  repeat' first
    | (solve | cases computed)
    | (split at computed)
    | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)
  all_goals
    simp only [Except.ok.injEq] at computed
    subst effect
    apply packet_inventory_retain
    first
      | exact onSyn_packet_inventory prior inventory (by assumption)
      | exact onSynAck_packet_inventory prior inventory (by assumption)
      | exact onFinalAck_packet_inventory inventory (by assumption)
      | exact onSynReplyAck_packet_inventory inventory (by assumption)

theorem evaluate_packet_inventory (prior : PhaseInvariant before) (inventory : PacketInventory before)
    (computed : evaluate before index event = .ok effect) : PacketInventory effect.state := by
  unfold evaluate at computed
  dsimp only at computed
  cases event <;>
    repeat' first
      | (solve | cases computed)
      | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)
      | (split at computed)
  all_goals
    simp only [Except.ok.injEq] at computed
    subst effect
    first
      | (solve | exact packet_inventory_last (openConnection_packet_inventory inventory (by assumption)) index)
      | (solve | exact packet_inventory_last (receive_packet_inventory prior inventory (by assumption)) index)
      | (solve | exact packet_inventory_last (timeout_packet_inventory inventory (by assumption)) index)
      | (solve | exact packet_inventory_last (packet_inventory_clock inventory (by assumption)) index)

private theorem onSyn_advancing_origins (prior : AdvancingOrigins before)
    (actorEq : receipt.source.actor = .active) (kindEq : receipt.source.kind = .syn)
    (computed : onSyn before receipt policy = .ok effect) : AdvancingOrigins (retainReceipt effect receipt).state := by
  cases phase : before.phase with
  | idle => simp [onSyn, phase] at computed
  | opened opened =>
    simp only [onSyn, phase] at computed
    repeat' first
      | (solve | cases computed)
      | (split at computed)
      | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)
    rename_i same sourceEq pending listened result next timerEq
    simp only [Except.ok.injEq] at computed
    subst effect
    exact AdvancingReceipt.fresh_cast receipt same.property actorEq kindEq
  | answered answered | acknowledged answered client | complete answered client server =>
    simp only [onSyn, phase] at computed
    repeat' first
      | (solve | cases computed)
      | (split at computed)
      | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)
    simp only [Except.ok.injEq] at computed
    subst effect
    exact prior.frame rfl (List.prefix_append _ _)

private theorem onSynAck_advancing_origins (prior : AdvancingOrigins before)
    (actorEq : receipt.source.actor = .passive) (kindEq : receipt.source.kind = .synAck)
    (computed : onSynAck before receipt policy = .ok effect) : AdvancingOrigins (retainReceipt effect receipt).state := by
  cases phase : before.phase with
  | idle | opened opened => simp [onSynAck, phase] at computed
  | answered answered =>
    simp only [onSynAck, phase] at computed
    repeat' first
      | (solve | cases computed)
      | (split at computed)
      | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)
    rename_i same sourceEq ready received result next timerEq
    simp only [Except.ok.injEq] at computed
    subst effect
    have old : AnsweredMilestones before.receipts answered := by simpa only [AdvancingOrigins, phase] using prior
    constructor
    · rw [(ackTimer_logs timerEq).2]
      exact old.mono (List.prefix_append _ _)
    · exact AdvancingReceipt.fresh_cast receipt same.property actorEq kindEq
  | acknowledged acknowledged client | complete acknowledged client server =>
    simp only [onSynAck, phase] at computed
    repeat' first
      | (solve | cases computed)
      | (split at computed)
      | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)
    simp only [Except.ok.injEq] at computed
    subst effect
    exact prior.frame rfl (List.prefix_append _ _)

private theorem onFinalAck_advancing_origins (prior : AdvancingOrigins before)
    (actorEq : receipt.source.actor = .active) (kindEq : receipt.source.kind = .finalAck)
    (computed : onFinalAck before receipt = .ok effect) : AdvancingOrigins (retainReceipt effect receipt).state := by
  cases phase : before.phase with
  | idle | opened opened | answered answered => simp [onFinalAck, phase] at computed
  | acknowledged acknowledged client =>
    simp only [onFinalAck, phase] at computed
    repeat' first
      | (solve | cases computed)
      | (split at computed)
      | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)
    rename_i ordered sourceResult same sourceEq ready received timerResult next timerEq
    simp only [Except.ok.injEq] at computed
    subst effect
    have old : AcknowledgedMilestones before.receipts acknowledged := by simpa only [AdvancingOrigins, phase] using prior
    apply AcknowledgedMilestones.finish acknowledged receipt.index receipt.spec _ _ _ _ old
    · rw [(ackTimer_logs (after := next) timerEq).2]
      exact List.prefix_append _ _
    · exact AdvancingReceipt.fresh_cast receipt same.property actorEq kindEq
  | complete complete client server =>
    simp only [onFinalAck, phase] at computed
    repeat' first
      | (solve | cases computed)
      | (split at computed)
      | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)
    simp only [Except.ok.injEq] at computed
    subst effect
    have old : CompleteMilestones before.receipts complete := by simpa only [AdvancingOrigins, phase] using prior
    exact old.mono (List.prefix_append _ _)

private theorem onSynReplyAck_advancing_origins (prior : AdvancingOrigins before)
    (computed : onSynReplyAck before receipt = .ok effect) : AdvancingOrigins (retainReceipt effect receipt).state := by
  cases phase : before.phase with
  | idle => simp [onSynReplyAck, phase] at computed
  | opened opened | answered opened =>
    simp only [onSynReplyAck, phase] at computed
    repeat' first
      | (solve | cases computed)
      | (split at computed)
      | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)
    cases computed
    exact prior.frame rfl (List.prefix_append _ _)
  | acknowledged acknowledged client =>
    simp only [onSynReplyAck, phase] at computed
    repeat' first
      | (solve | cases computed)
      | (split at computed)
      | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)
    simp only [Except.ok.injEq] at computed
    subst effect
    have old : AcknowledgedMilestones before.receipts acknowledged := by simpa only [AdvancingOrigins, phase] using prior
    exact old.mono (List.prefix_append _ _)
  | complete complete client server =>
    simp only [onSynReplyAck, phase] at computed
    repeat' first
      | (solve | cases computed)
      | (split at computed)
      | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)
    simp only [Except.ok.injEq] at computed
    subst effect
    have old : CompleteMilestones before.receipts complete := by simpa only [AdvancingOrigins, phase] using prior
    exact old.mono (List.prefix_append _ _)

private theorem receive_advancing_origins (prior : AdvancingOrigins before)
    (computed : receive before index source bytes path policy = .ok effect) : AdvancingOrigins effect.state := by
  unfold receive at computed
  repeat' first
    | (solve | cases computed)
    | (split at computed)
    | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)
  all_goals
    simp only [Except.ok.injEq] at computed
    subst effect
    first
      | exact onSyn_advancing_origins prior (by assumption) (by assumption) (by assumption)
      | exact onSynAck_advancing_origins prior (by assumption) (by assumption) (by assumption)
      | exact onFinalAck_advancing_origins prior (by assumption) (by assumption) (by assumption)
      | exact onSynReplyAck_advancing_origins prior (by assumption)

private theorem openConnection_advancing_origins (computed : openConnection before index remote policy = .ok effect) :
    AdvancingOrigins effect.state := by
  unfold openConnection at computed
  repeat' first
    | (solve | cases computed)
    | (solve | cases computed; trivial)
    | (split at computed)
    | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)

private theorem timeout_advancing_origins (prior : AdvancingOrigins before)
    (computed : timeout before index actor generation policy = .ok effect) : AdvancingOrigins effect.state := by
  unfold timeout at computed
  repeat' first
    | (solve | cases computed)
    | (split at computed)
    | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)
  all_goals
    simp only [Except.ok.injEq] at computed
    subst effect
    first
      | exact prior
      | cases actor <;> exact prior.frame rfl (List.prefix_refl _)

private theorem advancing_origins_clock (prior : AdvancingOrigins before)
    (computed : HandshakeTimer.advance (before.timer actor) now = .ok timer) :
    AdvancingOrigins (before.withTimer actor timer (HandshakeTimer.advance_valid (before.timer_valid actor) computed)) := by
  cases actor <;> exact prior.frame rfl (List.prefix_refl _)

theorem evaluate_advancing_origins (prior : AdvancingOrigins before)
    (computed : evaluate before index event = .ok effect) : AdvancingOrigins effect.state := by
  unfold evaluate at computed
  dsimp only at computed
  cases event with
  | activeOpen remote policy =>
    repeat' first
      | (solve | cases computed)
      | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)
      | (split at computed)
    all_goals
      simp only [Except.ok.injEq] at computed
      subst effect
      rename_i result operation
      have core := operation
      change openConnection before index remote policy = .ok result at core
      have inherited := openConnection_advancing_origins core
      exact inherited.frame rfl (List.prefix_refl _)
  | receive source bytes path policy =>
    repeat' first
      | (solve | cases computed)
      | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)
      | (split at computed)
    all_goals
      simp only [Except.ok.injEq] at computed
      subst effect
      rename_i result operation
      have core := operation
      change receive before index source bytes path policy = .ok result at core
      have inherited := receive_advancing_origins prior core
      exact inherited.frame rfl (List.prefix_refl _)
  | timeout actor generation policy =>
    repeat' first
      | (solve | cases computed)
      | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)
      | (split at computed)
    all_goals
      simp only [Except.ok.injEq] at computed
      subst effect
      rename_i result operation
      have core := operation
      change timeout before index actor generation policy = .ok result at core
      have inherited := timeout_advancing_origins prior core
      exact inherited.frame rfl (List.prefix_refl _)
  | advanceClock actor millis =>
    repeat' first
      | (solve | cases computed)
      | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)
      | (split at computed)
    all_goals
      simp only [Except.ok.injEq] at computed
      subst effect
      rename_i result operation
      have core := operation
      change HandshakeTimer.advance (before.timer actor) millis = .ok result at core
      have inherited := advancing_origins_clock prior core
      exact inherited.frame rfl (List.prefix_refl _)

private theorem openConnection_no_receipt (computed : openConnection before index remote policy = .ok effect) :
    effect.receipt = none := by
  unfold openConnection at computed
  repeat' first
    | (solve | cases computed; rfl)
    | (solve | cases computed)
    | (split at computed)
    | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)

private theorem timeout_no_receipt (computed : timeout before index actor generation policy = .ok effect) :
    effect.receipt = none := by
  unfold timeout at computed
  repeat' first
    | (solve | cases computed; rfl)
    | (solve | cases computed)
    | (split at computed)
    | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)

theorem evaluate_receipt_event (computed : evaluate before index event = .ok effect)
    (recorded : effect.receipt = some receipt) :
    ∃ source bytes path policy, event = .receive source bytes path policy ∧
      before.source source = some receipt.source ∧ receipt.source.index = source ∧ receipt.delivery.input.bytes = bytes := by
  cases event with
  | receive source bytes path policy =>
    obtain ⟨selected, present, found, sourceIndex, raw⟩ := evaluate_receive_receipt_details computed
    have same : selected = receipt := Option.some.inj (present.symm.trans recorded)
    subst selected
    exact ⟨source, bytes, path, policy, rfl, found, sourceIndex, raw⟩
  | activeOpen remote policy =>
    unfold evaluate at computed
    dsimp only at computed
    repeat' first
      | (solve | cases computed)
      | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)
      | (split at computed)
    all_goals
      simp only [Except.ok.injEq] at computed
      subst effect
      rename_i result operation
      have core := operation
      change openConnection before index remote policy = .ok result at core
      have quiet := openConnection_no_receipt core
      rw [show result.receipt = none from quiet] at recorded
      cases recorded
  | timeout actor generation policy =>
    unfold evaluate at computed
    dsimp only at computed
    repeat' first
      | (solve | cases computed)
      | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)
      | (split at computed)
    all_goals
      simp only [Except.ok.injEq] at computed
      subst effect
      rename_i result operation
      have core := operation
      change timeout before index actor generation policy = .ok result at core
      have quiet := timeout_no_receipt core
      rw [show result.receipt = none from quiet] at recorded
      cases recorded
  | advanceClock actor millis =>
    unfold evaluate at computed
    dsimp only at computed
    repeat' first
      | (solve | cases computed; cases recorded)
      | (solve | cases computed)
      | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)
      | (split at computed)

end Netlib.Check.TCPHandshakeRecovery

namespace Netlib.Check.TCPHandshakeRecovery

open Protocol.TCP

private theorem timers_arm (prior : TimersBounded before)
    (computed : armTimer before actor kind source = .ok after) : TimersBounded after := by
  obtain ⟨timer, armed, rfl⟩ := armTimer_eq computed
  exact TimersBounded.withTimer prior actor timer _
    (HandshakeTimer.arm_bounded_startup (prior actor) armed)

private theorem timers_ack (prior : TimersBounded before)
    (computed : ackTimer before actor kind source = .ok after) : TimersBounded after := by
  obtain ⟨timer, acknowledged, rfl⟩ := ackTimer_eq computed
  exact TimersBounded.withTimer prior actor timer _
    (HandshakeTimer.acknowledge_bounded_startup (before.timer_valid actor) (prior actor) acknowledged)

private theorem onSyn_timers (prior : TimersBounded before)
    (computed : onSyn before receipt policy = .ok effect) : TimersBounded effect.state := by
  unfold onSyn at computed
  repeat' first
    | (solve | cases computed)
    | (split at computed)
    | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)
  all_goals
    simp only [Except.ok.injEq] at computed
    subst effect
    first
      | exact prior
      | rename_i next armed
        exact TimersBounded.frame (timers_arm prior armed) rfl rfl

private theorem onSynAck_timers (prior : TimersBounded before)
    (computed : onSynAck before receipt policy = .ok effect) : TimersBounded effect.state := by
  unfold onSynAck at computed
  repeat' first
    | (solve | cases computed)
    | (split at computed)
    | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)
  all_goals
    simp only [Except.ok.injEq] at computed
    subst effect
    first
      | exact prior
      | rename_i next acknowledged
        exact TimersBounded.frame (timers_ack prior acknowledged) rfl rfl

private theorem onFinalAck_timers (prior : TimersBounded before)
    (computed : onFinalAck before receipt = .ok effect) : TimersBounded effect.state := by
  unfold onFinalAck at computed
  repeat' first
    | (solve | cases computed)
    | (split at computed)
    | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)
  all_goals
    simp only [Except.ok.injEq] at computed
    subst effect
    first
      | exact prior
      | rename_i next acknowledged
        exact TimersBounded.frame (timers_ack prior acknowledged) rfl rfl

private theorem onSynReplyAck_timers (prior : TimersBounded before)
    (computed : onSynReplyAck before receipt = .ok effect) : TimersBounded effect.state := by
  unfold onSynReplyAck at computed
  repeat' first
    | (solve | cases computed)
    | (split at computed)
    | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)
  all_goals
    simp only [Except.ok.injEq] at computed
    subst effect
    exact prior

private theorem receive_timers (prior : TimersBounded before)
    (computed : receive before index source bytes path policy = .ok effect) : TimersBounded effect.state := by
  unfold receive at computed
  repeat' first
    | (solve | cases computed)
    | (split at computed)
    | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)
  all_goals
    simp only [Except.ok.injEq] at computed
    subst effect
    apply TimersBounded.retainReceipt
    first
      | exact onSyn_timers prior (by assumption)
      | exact onSynAck_timers prior (by assumption)
      | exact onFinalAck_timers prior (by assumption)
      | exact onSynReplyAck_timers prior (by assumption)

private theorem openConnection_timers (prior : TimersBounded before)
    (computed : openConnection before index remote policy = .ok effect) : TimersBounded effect.state := by
  unfold openConnection at computed
  repeat' first
    | (solve | cases computed)
    | (split at computed)
    | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)
  all_goals
    simp only [Except.ok.injEq] at computed
    subst effect
    rename_i next armed
    exact TimersBounded.frame (timers_arm prior armed) rfl rfl

private theorem timeout_timers (prior : TimersBounded before)
    (computed : timeout before index actor generation policy = .ok effect) : TimersBounded effect.state := by
  unfold timeout at computed
  repeat' first
    | (solve | cases computed)
    | (split at computed)
    | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)
  all_goals
    simp only [Except.ok.injEq] at computed
    subst effect
    first
      | exact prior
      | apply TimersBounded.withTimer prior actor
        exact HandshakeTimer.expire_bounded_startup (before.timer_valid actor) (prior actor) (by assumption)

private theorem timers_clock (prior : TimersBounded before)
    (computed : HandshakeTimer.advance (before.timer actor) millis = .ok timer) :
    TimersBounded (before.withTimer actor timer (HandshakeTimer.advance_valid (before.timer_valid actor) computed)) :=
  TimersBounded.withTimer prior actor timer _ (HandshakeTimer.advance_bounded_startup (prior actor) computed)

theorem evaluate_timer_bounds (prior : TimersBounded before)
    (computed : evaluate before index event = .ok effect) : TimersBounded effect.state := by
  unfold evaluate at computed
  dsimp only at computed
  cases event <;>
    repeat' first
      | (solve | cases computed)
      | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)
      | (split at computed)
  all_goals
    simp only [Except.ok.injEq] at computed
    subst effect
    rename_i next evaluated
    first
      | exact TimersBounded.frame (openConnection_timers prior evaluated) rfl rfl
      | exact TimersBounded.frame (receive_timers prior evaluated) rfl rfl
      | exact TimersBounded.frame (timeout_timers prior evaluated) rfl rfl
      | exact TimersBounded.frame (timers_clock prior evaluated) rfl rfl

variable {active passive : H.Local} {before : State active passive} {effect : Effect active passive}

private theorem onSyn_windows (prior : PhaseWindows before)
    (computed : onSyn before receipt policy = .ok effect) : PhaseWindows effect.state := by
  cases phase : before.phase with
  | idle => simp [onSyn, phase] at computed
  | opened opened =>
    simp only [onSyn, phase] at computed
    repeat' first
      | (solve | cases computed)
      | (split at computed)
      | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)
    simp only [Except.ok.injEq] at computed
    subst effect
    trivial
  | answered answered | acknowledged answered client | complete answered client server =>
    simp only [onSyn, phase] at computed
    repeat' first
      | (solve | cases computed)
      | (split at computed)
      | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)
    simp only [Except.ok.injEq] at computed
    subst effect
    exact prior.frame rfl

private theorem onSynAck_windows (prior : PhaseWindows before)
    (computed : onSynAck before receipt policy = .ok effect) : PhaseWindows effect.state := by
  cases phase : before.phase with
  | idle | opened opened => simp [onSynAck, phase] at computed
  | answered answered =>
    simp only [onSynAck, phase] at computed
    repeat' first
      | (solve | cases computed)
      | (split at computed)
      | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)
    rename_i same sourceEq ready received result next timerEq
    simp only [Except.ok.injEq] at computed
    subst effect
    exact Acknowledged.peer_window ⟨answered, policy, receipt.index, receipt.spec,
      same.property ▸ receipt.delivery, ready, received⟩
  | acknowledged acknowledged client | complete acknowledged client server =>
    simp only [onSynAck, phase] at computed
    repeat' first
      | (solve | cases computed)
      | (split at computed)
      | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)
    simp only [Except.ok.injEq] at computed
    subst effect
    exact prior.frame rfl

private theorem onFinalAck_windows (invariant : PhaseInvariant before) (prior : PhaseWindows before)
    (computed : onFinalAck before receipt = .ok effect)
    (incoming : receipt.delivery.input.packet.segment.window.val = active.capacity) : PhaseWindows effect.state := by
  cases phase : before.phase with
  | idle | opened opened | answered answered => simp [onFinalAck, phase] at computed
  | acknowledged acknowledged client =>
    simp only [onFinalAck, phase] at computed
    repeat' first
      | (solve | cases computed)
      | (split at computed)
      | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)
    rename_i ordered sourceResult same sourceEq ready received timerResult next timerEq
    simp only [Except.ok.injEq] at computed
    subst effect
    have old : client.current.sendWindow = passive.capacity := by simpa only [PhaseWindows, phase] using prior
    exact ⟨old, (Completed.peer_windows (finish acknowledged receipt.index receipt.spec
      (same.property ▸ receipt.delivery) ready received ordered)).2⟩
  | complete complete client server =>
    simp only [onFinalAck, phase] at computed
    repeat' first
      | (solve | cases computed)
      | (split at computed)
      | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)
    simp only [Except.ok.injEq] at computed
    subst effect
    have old : client.current.sendWindow = passive.capacity ∧ server.current.sendWindow = active.capacity := by
      simpa only [PhaseWindows, phase] using prior
    have clean := invariant.2.1
    simp only [PreDataFrames, phase] at clean
    exact ⟨old.1, ReceivedAck.send_window _ clean.2 old.2 incoming⟩

private theorem onSynReplyAck_windows (invariant : PhaseInvariant before) (prior : PhaseWindows before)
    (computed : onSynReplyAck before receipt = .ok effect)
    (incoming : receipt.delivery.input.packet.segment.window.val = passive.capacity) : PhaseWindows effect.state := by
  cases phase : before.phase with
  | idle => simp [onSynReplyAck, phase] at computed
  | opened opened | answered opened =>
    simp only [onSynReplyAck, phase] at computed
    repeat' first
      | (solve | cases computed)
      | (split at computed)
      | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)
    cases computed
    exact prior
  | acknowledged acknowledged client =>
    simp only [onSynReplyAck, phase] at computed
    repeat' first
      | (solve | cases computed)
      | (split at computed)
      | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)
    simp only [Except.ok.injEq] at computed
    subst effect
    have old : client.current.sendWindow = passive.capacity := by simpa only [PhaseWindows, phase] using prior
    have clean := invariant.2.1
    simp only [PreDataFrames, phase] at clean
    exact ReceivedAck.send_window _ clean old incoming
  | complete complete client server =>
    simp only [onSynReplyAck, phase] at computed
    repeat' first
      | (solve | cases computed)
      | (split at computed)
      | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)
    simp only [Except.ok.injEq] at computed
    subst effect
    have old : client.current.sendWindow = passive.capacity ∧ server.current.sendWindow = active.capacity := by
      simpa only [PhaseWindows, phase] using prior
    have clean := invariant.2.1
    simp only [PreDataFrames, phase] at clean
    exact ⟨ReceivedAck.send_window _ clean.1 old.1 incoming, old.2⟩

private theorem receive_windows (invariant : PhaseInvariant before) (inventory : OutputInventory before)
    (prior : PhaseWindows before) (computed : receive before index source bytes path policy = .ok effect) :
    PhaseWindows effect.state := by
  unfold receive at computed
  repeat' first
    | (solve | cases computed)
    | (split at computed)
    | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)
  all_goals
    simp only [Except.ok.injEq] at computed
    subst effect
    rename_i result operated
    change PhaseWindows result.state
    have fields := receivePacket_fields (before := before) (index := index) (source := source)
      (bytes := bytes) (path := path) (by assumption)
    have window := Receipt.input_window _ (inventory.source_shape fields.2)
    first
      | exact onSyn_windows prior (by assumption)
      | exact onSynAck_windows prior (by assumption)
      | exact onFinalAck_windows invariant prior operated (by simp only [*, Kind.capacity])
      | exact onSynReplyAck_windows invariant prior operated (by simp only [*, Kind.capacity])

private theorem openConnection_windows (computed : openConnection before index remote policy = .ok effect) :
    PhaseWindows effect.state := by
  unfold openConnection at computed
  repeat' first
    | (solve | cases computed)
    | (split at computed)
    | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)
  simp only [Except.ok.injEq] at computed
  subst effect
  trivial

private theorem timeout_windows (prior : PhaseWindows before)
    (computed : timeout before index actor generation policy = .ok effect) : PhaseWindows effect.state := by
  unfold timeout at computed
  repeat' first
    | (solve | cases computed)
    | (split at computed)
    | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)
  all_goals
    simp only [Except.ok.injEq] at computed
    subst effect
    first
      | exact prior
      | cases actor <;> exact prior.frame rfl

private theorem windows_clock (prior : PhaseWindows before)
    (computed : HandshakeTimer.advance (before.timer actor) now = .ok timer) :
    PhaseWindows (before.withTimer actor timer (HandshakeTimer.advance_valid (before.timer_valid actor) computed)) :=
  prior.withTimer _ _ _

theorem evaluate_phase_windows (invariant : PhaseInvariant before) (inventory : OutputInventory before)
    (prior : PhaseWindows before) (computed : evaluate before index event = .ok effect) : PhaseWindows effect.state := by
  unfold evaluate at computed
  dsimp only at computed
  cases event <;>
    repeat' first
      | (solve | cases computed)
      | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)
      | (split at computed)
  all_goals
    simp only [Except.ok.injEq] at computed
    subst effect
    rename_i result operation
    first
      | (solve |
        have core := operation
        change openConnection before index _ _ = .ok result at core
        exact PhaseWindows.frame (openConnection_windows core) rfl)
      | (solve |
        have core := operation
        change receive before index _ _ _ _ = .ok result at core
        exact PhaseWindows.frame (receive_windows invariant inventory prior core) rfl)
      | (solve |
        have core := operation
        change timeout before index _ _ _ = .ok result at core
        exact PhaseWindows.frame (timeout_windows prior core) rfl)
      | (solve |
        have core := operation
        change HandshakeTimer.advance (before.timer _) _ = .ok result at core
        exact PhaseWindows.frame (windows_clock prior core) rfl)

end Netlib.Check.TCPHandshakeRecovery

namespace Netlib.Check.TCPHandshakeRecovery

open Protocol.TCP

private theorem clock_frame_fields (prior : ClockFrame before state)
    (active : after.activeTimer.now = state.activeTimer.now) (passive : after.passiveTimer.now = state.passiveTimer.now) :
    ClockFrame before after := by
  intro actor
  cases actor
  · exact active.trans (prior .active)
  · exact passive.trans (prior .passive)

private theorem armTimer_clock_frame (computed : armTimer before actor kind source = .ok after) : ClockFrame before after := by
  obtain ⟨timer, armed, rfl⟩ := armTimer_eq computed
  apply ClockFrame.withTimer
  rw [(HandshakeTimer.arm_eq armed).2]

private theorem ackTimer_clock_frame (computed : ackTimer before actor kind source = .ok after) : ClockFrame before after := by
  obtain ⟨timer, acknowledged, rfl⟩ := ackTimer_eq computed
  apply ClockFrame.withTimer
  obtain ⟨_, _, rfl⟩ := HandshakeTimer.acknowledge_eq acknowledged
  rfl

private theorem onSyn_clock_frame (computed : onSyn before receipt policy = .ok effect) : ClockFrame before effect.state := by
  unfold onSyn at computed
  repeat' first
    | (solve | cases computed)
    | (split at computed)
    | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)
  all_goals
    simp only [Except.ok.injEq] at computed
    subst effect
    first
      | exact ClockFrame.refl before
      | rename_i next armed
        have frame : ClockFrame before next := armTimer_clock_frame armed
        exact clock_frame_fields frame rfl rfl

private theorem onSynAck_clock_frame (computed : onSynAck before receipt policy = .ok effect) : ClockFrame before effect.state := by
  unfold onSynAck at computed
  repeat' first
    | (solve | cases computed)
    | (split at computed)
    | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)
  all_goals
    simp only [Except.ok.injEq] at computed
    subst effect
    first
      | exact ClockFrame.refl before
      | rename_i next acknowledged
        have frame : ClockFrame before next := ackTimer_clock_frame acknowledged
        exact clock_frame_fields frame rfl rfl

private theorem onFinalAck_clock_frame (computed : onFinalAck before receipt = .ok effect) : ClockFrame before effect.state := by
  unfold onFinalAck at computed
  repeat' first
    | (solve | cases computed)
    | (split at computed)
    | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)
  all_goals
    simp only [Except.ok.injEq] at computed
    subst effect
    first
      | exact ClockFrame.refl before
      | rename_i next acknowledged
        have frame : ClockFrame before next := ackTimer_clock_frame acknowledged
        exact clock_frame_fields frame rfl rfl

private theorem onSynReplyAck_clock_frame (computed : onSynReplyAck before receipt = .ok effect) : ClockFrame before effect.state := by
  unfold onSynReplyAck at computed
  repeat' first
    | (solve | cases computed)
    | (split at computed)
    | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)
  all_goals
    simp only [Except.ok.injEq] at computed
    subst effect
    exact ClockFrame.refl before

private theorem receive_clock_frame (computed : receive before index source bytes path policy = .ok effect) : ClockFrame before effect.state := by
  unfold receive at computed
  repeat' first
    | (solve | cases computed)
    | (split at computed)
    | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)
  all_goals
    simp only [Except.ok.injEq] at computed
    subst effect
    apply ClockFrame.retainReceipt
    first
      | exact onSyn_clock_frame (by assumption)
      | exact onSynAck_clock_frame (by assumption)
      | exact onFinalAck_clock_frame (by assumption)
      | exact onSynReplyAck_clock_frame (by assumption)

private theorem openConnection_clock_frame (computed : openConnection before index remote policy = .ok effect) :
    ClockFrame before effect.state := by
  unfold openConnection at computed
  repeat' first
    | (solve | cases computed)
    | (split at computed)
    | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)
  simp only [Except.ok.injEq] at computed
  subst effect
  rename_i next armed
  have frame : ClockFrame before next := armTimer_clock_frame armed
  exact clock_frame_fields frame rfl rfl

private theorem timeout_clock_frame (computed : timeout before index actor generation policy = .ok effect) :
    ClockFrame before effect.state := by
  unfold timeout at computed
  repeat' first
    | (solve | cases computed)
    | (split at computed)
    | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)
  all_goals
    simp only [Except.ok.injEq] at computed
    subst effect
    first
      | exact ClockFrame.refl before
      | apply ClockFrame.publish
        apply ClockFrame.withTimer
        exact (HandshakeTimer.expire_fields (by assumption)).1

private theorem advance_clock_effect (computed : HandshakeTimer.advance (before.timer actor) millis = .ok timer) :
    ClockEffect before (.advanceClock actor millis)
      (before.withTimer actor timer (HandshakeTimer.advance_valid (before.timer_valid actor) computed)) := by
  have now := congrArg HandshakeTimer.State.now (HandshakeTimer.advance_eq computed).2
  cases actor <;> exact ⟨now, rfl⟩

theorem evaluate_clock_effect (computed : evaluate before index event = .ok effect) : ClockEffect before event effect.state := by
  unfold evaluate at computed
  dsimp only at computed
  cases event <;>
    repeat' first
      | (solve | cases computed)
      | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)
      | (split at computed)
  all_goals
    simp only [Except.ok.injEq] at computed
    subst effect
    rename_i next evaluated
    first
      | exact clock_frame_fields (openConnection_clock_frame evaluated) rfl rfl
      | exact clock_frame_fields (receive_clock_frame evaluated) rfl rfl
      | exact clock_frame_fields (timeout_clock_frame evaluated) rfl rfl
      | exact advance_clock_effect evaluated

end Netlib.Check.TCPHandshakeRecovery


namespace Netlib.Check.TCPHandshakeRecovery

open Protocol.TCP

variable {before : State active passive} {effect : Effect active passive}

theorem evaluate_clock_no_output
    (computed : evaluate before index (.advanceClock actor millis) = .ok effect) : effect.output = none := by
  simp only [evaluate] at computed
  repeat' first
    | (solve | exact (congrArg Effect.output (Except.ok.inj computed)).symm)
    | cases computed
    | split at computed
    | dsimp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at computed

private theorem timeout_closed_no_output
    (closed : (before.timer actor).status = .acknowledged flight acknowledgedAt)
    (computed : timeout before index actor generation policy = .ok effect) : effect.output = none := by
  simp only [timeout, closed, pure, Except.pure, Except.ok.injEq] at computed
  exact (congrArg Effect.output computed).symm

theorem evaluate_complete_timeout_no_output (timers : PhaseTimers before)
    (phase : before.phase = .complete complete client server)
    (computed : evaluate before index (.timeout actor generation policy) = .ok effect) : effect.output = none := by
  have closed : ∃ flight acknowledgedAt, (before.timer actor).status = .acknowledged flight acknowledgedAt := by
    rw [PhaseTimers, phase] at timers
    cases actor
    · obtain ⟨flight, atTime, status, _, _⟩ := timers.1
      exact ⟨flight, atTime, status⟩
    · obtain ⟨flight, atTime, status, _, _⟩ := timers.2
      exact ⟨flight, atTime, status⟩
  obtain ⟨flight, acknowledgedAt, status⟩ := closed
  simp only [evaluate] at computed
  split at computed
  · cases computed
  · cases timed : timeout before index actor generation policy with
    | error reason => simp only [timed, bind, Except.bind] at computed; cases computed
    | ok after =>
      have quiet := timeout_closed_no_output status timed
      simp only [timed, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at computed
      exact (congrArg Effect.output computed).symm.trans quiet

private theorem onSyn_complete_response (phase : before.phase = .complete complete client server)
    (computed : onSyn before receipt policy = .ok effect) (recorded : effect.output = some output) :
    output.kind = .synReplyAck := by
  simp only [onSyn, phase] at computed
  repeat' first
    | (solve | cases computed; cases recorded; rfl)
    | cases computed
    | split at computed
    | dsimp only [bind, Except.bind, pure, Except.pure] at computed

private theorem onSynAck_complete_response (phase : before.phase = .complete complete client server)
    (computed : onSynAck before receipt policy = .ok effect) (recorded : effect.output = some output) :
    output.kind = .finalAck := by
  simp only [onSynAck, phase] at computed
  repeat' first
    | (solve | cases computed; cases recorded; rfl)
    | cases computed
    | split at computed
    | dsimp only [bind, Except.bind, pure, Except.pure] at computed

private theorem onFinalAck_complete_quiet (phase : before.phase = .complete complete client server)
    (computed : onFinalAck before receipt = .ok effect) : effect.output = none := by
  simp only [onFinalAck, phase] at computed
  repeat' first
    | (solve | cases computed; rfl)
    | cases computed
    | split at computed
    | dsimp only [bind, Except.bind, pure, Except.pure] at computed

private theorem onSynReplyAck_complete_quiet (phase : before.phase = .complete complete client server)
    (computed : onSynReplyAck before receipt = .ok effect) : effect.output = none := by
  simp only [onSynReplyAck, phase] at computed
  repeat' first
    | (solve | cases computed; rfl)
    | cases computed
    | split at computed
    | dsimp only [bind, Except.bind, pure, Except.pure] at computed

private theorem receive_complete_response (phase : before.phase = .complete complete client server)
    (computed : receive before index source bytes path policy = .ok effect) (recorded : effect.output = some output) :
    ∃ receipt, effect.receipt = some receipt ∧
      ((receipt.source.kind = .syn ∧ output.kind = .synReplyAck) ∨
        (receipt.source.kind = .synAck ∧ output.kind = .finalAck)) := by
  unfold receive at computed
  repeat' first
    | (solve | cases computed)
    | split at computed
    | dsimp only [bind, Except.bind, pure, Except.pure] at computed
  all_goals
    simp only [Except.ok.injEq] at computed
    subst effect
    rename_i result operation
    simp only [retainReceipt] at recorded ⊢
    first
    | (solve | have kind := onSyn_complete_response phase operation recorded
               exact ⟨_, rfl, Or.inl ⟨by assumption, kind⟩⟩)
    | (solve | have kind := onSynAck_complete_response phase operation recorded
               exact ⟨_, rfl, Or.inr ⟨by assumption, kind⟩⟩)
    | (solve | have quiet := onFinalAck_complete_quiet phase operation
               rw [quiet] at recorded
               cases recorded)
    | (solve | have quiet := onSynReplyAck_complete_quiet phase operation
               rw [quiet] at recorded
               cases recorded)

theorem evaluate_complete_response (phase : before.phase = .complete complete client server)
    (computed : evaluate before index (.receive source bytes path policy) = .ok effect)
    (recorded : effect.output = some output) :
    ∃ receipt, effect.receipt = some receipt ∧
      ((receipt.source.kind = .syn ∧ output.kind = .synReplyAck) ∨
        (receipt.source.kind = .synAck ∧ output.kind = .finalAck)) := by
  simp only [evaluate] at computed
  split at computed
  · cases computed
  · cases received : receive before index source bytes path policy with
    | error reason => simp only [received, bind, Except.bind] at computed; cases computed
    | ok after =>
      simp only [received, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at computed
      subst effect
      exact receive_complete_response (effect := after) phase received recorded

theorem evaluate_complete_ack_no_output (phase : before.phase = .complete complete client server)
    (selected : before.source source = some original)
    (ack : original.kind = .finalAck ∨ original.kind = .synReplyAck)
    (computed : evaluate before index (.receive source bytes path policy) = .ok effect) : effect.output = none := by
  cases recorded : effect.output with
  | none => rfl
  | some output =>
    obtain ⟨receipt, present, kinds⟩ := evaluate_complete_response phase computed recorded
    obtain ⟨actual, actualAt, lookup, _, _⟩ := evaluate_receive_receipt_details computed
    have same : actual = receipt := Option.some.inj (actualAt.symm.trans present)
    subst actual
    have sourceEq : original = receipt.source := Option.some.inj (selected.symm.trans lookup)
    rw [sourceEq] at ack
    rcases kinds with ⟨syn, _⟩ | ⟨synAck, _⟩
    · rw [syn] at ack
      rcases ack with impossible | impossible <;> cases impossible
    · rw [synAck] at ack
      rcases ack with impossible | impossible <;> cases impossible

end Netlib.Check.TCPHandshakeRecovery

namespace Netlib.Check.TCPHandshakeRecovery

open Protocol.TCP

variable {active passive : H.Local} {before : State active passive} {effect : Effect active passive} {output : Emission}

private theorem onSyn_phase_level (computed : onSyn before receipt policy = .ok effect) :
    phaseLevel before.phase ≤ phaseLevel effect.state.phase := by
  unfold onSyn at computed
  repeat' first
    | (solve | cases computed)
    | (split at computed)
    | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)
  all_goals
    simp only [Except.ok.injEq] at computed
    subst effect
    simp_all only [respond, publish, phaseLevel] <;> decide

private theorem onSynAck_phase_level (computed : onSynAck before receipt policy = .ok effect) :
    phaseLevel before.phase ≤ phaseLevel effect.state.phase := by
  unfold onSynAck at computed
  repeat' first
    | (solve | cases computed)
    | (split at computed)
    | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)
  all_goals
    simp only [Except.ok.injEq] at computed
    subst effect
    simp_all only [respond, publish, phaseLevel] <;> decide

private theorem onFinalAck_phase_level (computed : onFinalAck before receipt = .ok effect) :
    phaseLevel before.phase ≤ phaseLevel effect.state.phase := by
  unfold onFinalAck at computed
  repeat' first
    | (solve | cases computed)
    | (split at computed)
    | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)
  all_goals
    simp only [Except.ok.injEq] at computed
    subst effect
    simp_all only [phaseLevel] <;> decide

private theorem onSynReplyAck_phase_level (computed : onSynReplyAck before receipt = .ok effect) :
    phaseLevel before.phase ≤ phaseLevel effect.state.phase := by
  unfold onSynReplyAck at computed
  repeat' first
    | (solve | cases computed)
    | (split at computed)
    | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)
  all_goals
    simp only [Except.ok.injEq] at computed
    subst effect
    simp_all only [phaseLevel] <;> decide

private theorem receive_phase_level (computed : receive before index source bytes path policy = .ok effect) :
    phaseLevel before.phase ≤ phaseLevel effect.state.phase := by
  unfold receive at computed
  repeat' first
    | (solve | cases computed)
    | (split at computed)
    | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)
  all_goals
    simp only [Except.ok.injEq] at computed
    subst effect
    rename_i result operated
    first
      | (solve | have bound := onSyn_phase_level operated; exact bound)
      | (solve | have bound := onSynAck_phase_level operated; exact bound)
      | (solve | have bound := onFinalAck_phase_level operated; exact bound)
      | (solve | have bound := onSynReplyAck_phase_level operated; exact bound)

private theorem openConnection_phase_level (computed : openConnection before index remote policy = .ok effect) :
    phaseLevel before.phase ≤ phaseLevel effect.state.phase := by
  unfold openConnection at computed
  repeat' first
    | (solve | cases computed)
    | (split at computed)
    | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)
  simp only [Except.ok.injEq] at computed
  subst effect
  simp_all only [publish, phaseLevel] <;> decide

private theorem timeout_phase_level (computed : timeout before index actor generation policy = .ok effect) :
    phaseLevel before.phase ≤ phaseLevel effect.state.phase := by
  unfold timeout at computed
  repeat' first
    | (solve | cases computed)
    | (split at computed)
    | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)
  all_goals
    simp only [Except.ok.injEq] at computed
    subst effect
    first
      | exact Nat.le_refl _
      | cases actor <;> exact Nat.le_refl _

theorem evaluate_phase_level (computed : evaluate before index event = .ok effect) :
    phaseLevel before.phase ≤ phaseLevel effect.state.phase := by
  unfold evaluate at computed
  dsimp only at computed
  cases event <;>
    repeat' first
      | (solve | cases computed)
      | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)
      | (split at computed)
  all_goals
    simp only [Except.ok.injEq] at computed
    subst effect
    rename_i next evaluated
    first
      | (solve | have bound := openConnection_phase_level evaluated; exact bound)
      | (solve | have bound := receive_phase_level evaluated; exact bound)
      | (solve | have bound := timeout_phase_level evaluated; exact bound)
      | (solve | cases ‹Side› <;> exact Nat.le_refl _)

private theorem onSyn_output_floor (computed : onSyn before receipt policy = .ok effect)
    (emitted : effect.output = some output) : output.kind.phaseFloor ≤ phaseLevel effect.state.phase := by
  unfold onSyn at computed
  repeat' first
    | (solve | cases computed)
    | (split at computed)
    | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)
  all_goals
    simp only [Except.ok.injEq] at computed
    subst effect
    dsimp only [respond, publish] at emitted
    cases emitted
    simp_all only [respond, publish, Kind.phaseFloor, phaseLevel] <;> decide

private theorem onSynAck_output_floor (computed : onSynAck before receipt policy = .ok effect)
    (emitted : effect.output = some output) : output.kind.phaseFloor ≤ phaseLevel effect.state.phase := by
  unfold onSynAck at computed
  repeat' first
    | (solve | cases computed)
    | (split at computed)
    | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)
  all_goals
    simp only [Except.ok.injEq] at computed
    subst effect
    dsimp only [respond, publish] at emitted
    cases emitted
    simp_all only [respond, publish, Kind.phaseFloor, phaseLevel] <;> decide

private theorem receive_output_floor (computed : receive before index source bytes path policy = .ok effect)
    (emitted : effect.output = some output) : output.kind.phaseFloor ≤ phaseLevel effect.state.phase := by
  unfold receive at computed
  repeat' first
    | (solve | cases computed)
    | (split at computed)
    | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)
  all_goals
    simp only [Except.ok.injEq] at computed
    subst effect
    rename_i result operated
    change result.output = some output at emitted
    first
      | (solve | have bound := onSyn_output_floor operated emitted; exact bound)
      | (solve | have bound := onSynAck_output_floor operated emitted; exact bound)
      | (solve | have quiet := onFinalAck_no_output operated; rw [quiet] at emitted; cases emitted)
      | (solve | have quiet := onSynReplyAck_no_output operated; rw [quiet] at emitted; cases emitted)

private theorem openConnection_output_floor (computed : openConnection before index remote policy = .ok effect)
    (emitted : effect.output = some output) : output.kind.phaseFloor ≤ phaseLevel effect.state.phase := by
  unfold openConnection at computed
  repeat' first
    | (solve | cases computed)
    | (split at computed)
    | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)
  simp only [Except.ok.injEq] at computed
  subst effect
  cases emitted
  change (1 : Nat) ≤ 1
  decide

private theorem timeout_output_floor (prior : Availability before)
    (computed : timeout before index actor generation policy = .ok effect)
    (emitted : effect.output = some output) : output.kind.phaseFloor ≤ phaseLevel effect.state.phase := by
  unfold timeout at computed
  repeat' first
    | (solve | cases computed)
    | (split at computed)
    | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)
  all_goals
    simp only [Except.ok.injEq] at computed
    subst effect
    first
      | (solve | cases emitted)
      | (cases emitted
         have bound := prior.source (by assumption)
         cases actor <;> exact bound)

private theorem availability_output (prior : Availability before)
    (level : phaseLevel before.phase ≤ phaseLevel effect.state.phase)
    (emissions : effect.state.emissions = before.emissions ++ effect.output.toList)
    (floor : ∀ output, effect.output = some output → output.kind.phaseFloor ≤ phaseLevel effect.state.phase) :
    Availability effect.state := by
  intro output member
  rw [emissions] at member
  rcases List.mem_append.mp member with old | fresh
  · exact Nat.le_trans (prior output old) level
  · exact floor output (by simpa only [Option.mem_toList] using fresh)

theorem evaluate_availability (prior : Availability before)
    (computed : evaluate before index event = .ok effect) : Availability effect.state := by
  apply availability_output prior (evaluate_phase_level computed) (evaluate_records computed).emissions
  intro output emitted
  unfold evaluate at computed
  dsimp only at computed
  cases event <;>
    repeat' first
      | (solve | cases computed)
      | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)
      | (split at computed)
  all_goals
    simp only [Except.ok.injEq] at computed
    subst effect
    rename_i next evaluated
    first
      | (solve | have bound := openConnection_output_floor evaluated emitted; exact bound)
      | (solve | have bound := receive_output_floor evaluated emitted; exact bound)
      | (solve | have bound := timeout_output_floor prior evaluated emitted; exact bound)
      | (solve | cases emitted)

end Netlib.Check.TCPHandshakeRecovery

namespace Netlib.Check.TCPHandshakeRecovery

open Protocol.TCP

variable {active passive : H.Local} {before : State active passive} {effect : Effect active passive}

private theorem openConnection_opened (computed : openConnection before index remote policy = .ok effect) :
    ∃ opened : O.Opened active, before.phase = .idle ∧ effect.state.phase = .opened opened ∧
      opened.remote = remote ∧ opened.policy = policy ∧ opened.index = index ∧
      effect.output = some ⟨index, .active, .syn, opened.pending.output, .open⟩ := by
  unfold openConnection at computed
  repeat' first
    | (solve | cases computed)
    | (split at computed)
    | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)
  simp only [Except.ok.injEq] at computed
  subst effect
  exact ⟨⟨remote, policy, index, _, by assumption⟩, by assumption, rfl, rfl, rfl, rfl, rfl⟩

theorem evaluate_opened (computed : evaluate before index (.activeOpen remote policy) = .ok effect) :
    ∃ opened : O.Opened active, before.phase = .idle ∧ effect.state.phase = .opened opened ∧
      opened.remote = remote ∧ opened.policy = policy ∧ opened.index = index ∧
      effect.output = some ⟨index, .active, .syn, opened.pending.output, .open⟩ := by
  unfold evaluate at computed
  dsimp only at computed
  repeat' first
    | (solve | cases computed)
    | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)
    | (split at computed)
  simp only [Except.ok.injEq] at computed
  subst effect
  rename_i result operated
  obtain ⟨opened, beforePhase, afterPhase, remoteEq, policyEq, indexEq, emitted⟩ := openConnection_opened operated
  exact ⟨opened, beforePhase, afterPhase, remoteEq, policyEq, indexEq, emitted⟩

theorem evaluate_clock_timers (computed : evaluate before index (.advanceClock actor millis) = .ok effect) :
    effect.state.timer actor = { before.timer actor with now := millis } ∧
      effect.state.timer actor.other = before.timer actor.other ∧
      effect.state.phase = before.phase ∧ effect.output = none := by
  unfold evaluate at computed
  dsimp only at computed
  repeat' first
    | (solve | cases computed)
    | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)
    | (split at computed)
  simp only [Except.ok.injEq] at computed
  subst effect
  rename_i timer advanced
  have same := (HandshakeTimer.advance_eq advanced).2
  subst timer
  cases actor <;> exact ⟨rfl, rfl, rfl, rfl⟩

end Netlib.Check.TCPHandshakeRecovery

namespace Netlib.Check.TCPHandshakeRecovery

open Protocol.TCP

variable {active passive : H.Local} {before : State active passive} {flight : HandshakeTimer.Flight}

private theorem pending_timeout_template (invariant : PhaseInvariant before)
    (pending : (before.timer actor).status = .pending flight) :
    ∃ packet, canRetry actor before.phase = true ∧ flight.kind = timerKind actor ∧
      Template before flight.source actor (outputKind actor) packet := by
  have timers := invariant.1
  have templates := invariant.2.2
  cases phase : before.phase with
  | idle =>
    simp only [PhaseTimers, phase] at timers
    cases actor
    · have impossible := pending.symm.trans timers.1; cases impossible
    · have impossible := pending.symm.trans timers.2; cases impossible
  | opened value =>
    simp only [PhaseTimers, TemplateSources, phase] at timers templates
    cases actor
    · obtain ⟨selected, status, kind, source⟩ := timers.1
      have same : selected = flight := HandshakeTimer.Status.pending.inj (status.symm.trans pending)
      subst selected
      refine ⟨value.pending.output, by simp only [canRetry], kind, ?_⟩
      rw [source]
      exact templates
    · have impossible := pending.symm.trans timers.2; cases impossible
  | answered value =>
    simp only [PhaseTimers, TemplateSources, phase] at timers templates
    cases actor
    · obtain ⟨selected, status, kind, source⟩ := timers.1
      have same : selected = flight := HandshakeTimer.Status.pending.inj (status.symm.trans pending)
      subst selected
      refine ⟨value.opened.pending.output, by simp only [canRetry], kind, ?_⟩
      rw [source]
      exact templates.1
    · obtain ⟨selected, status, kind, source⟩ := timers.2
      have same : selected = flight := HandshakeTimer.Status.pending.inj (status.symm.trans pending)
      subst selected
      refine ⟨value.pending.output, by simp only [canRetry], kind, ?_⟩
      rw [source]
      exact templates.2
  | acknowledged value client =>
    simp only [PhaseTimers, TemplateSources, phase] at timers templates
    cases actor
    · obtain ⟨selected, atTime, status, _, _⟩ := timers.1
      have impossible := pending.symm.trans status; cases impossible
    · obtain ⟨selected, status, kind, source⟩ := timers.2
      have same : selected = flight := HandshakeTimer.Status.pending.inj (status.symm.trans pending)
      subst selected
      refine ⟨value.answered.pending.output, by simp only [canRetry], kind, ?_⟩
      rw [source]
      exact templates.2
  | complete value client server =>
    simp only [PhaseTimers, phase] at timers
    cases actor
    · obtain ⟨selected, atTime, status, _, _⟩ := timers.1
      have impossible := pending.symm.trans status; cases impossible
    · obtain ⟨selected, atTime, status, _, _⟩ := timers.2
      have impossible := pending.symm.trans status; cases impossible

private theorem timeout_index_unique {outputs : List Emission} {left right : Emission}
    (ordered : outputs.Pairwise (fun a b : Emission => a.index < b.index))
    (first : left ∈ outputs) (second : right ∈ outputs) (same : left.index = right.index) : left = right := by
  induction outputs with
  | nil => cases first
  | cons head tail ih =>
    obtain ⟨before, ordered⟩ := List.pairwise_cons.mp ordered
    rcases List.mem_cons.mp first with firstEq | firstTail
    · subst left
      rcases List.mem_cons.mp second with secondEq | secondTail
      · exact secondEq.symm
      · have newer := before right secondTail
        omega
    · rcases List.mem_cons.mp second with secondEq | secondTail
      · subst right
        have newer := before left firstTail
        omega
      · exact ih ordered firstTail secondTail

private theorem timeout_source_of_member
    (ordered : before.emissions.Pairwise (fun a b : Emission => a.index < b.index))
    (member : output ∈ before.emissions) : before.source output.index = some output := by
  cases found : before.source output.index with
  | none =>
    have absent := List.find?_eq_none.mp found output member
    exact False.elim (absent (beq_self_eq_true _))
  | some selected =>
    have retained := List.mem_of_find?_eq_some found
    have equal : selected.index = output.index := by simpa only [beq_iff_eq] using List.find?_some found
    have same := timeout_index_unique ordered retained member equal
    subst selected
    rfl

theorem evaluate_timeout_enabled (invariant : PhaseInvariant before)
    (emissionOrder : before.emissions.Pairwise (fun a b : Emission => a.index < b.index))
    (pending : (before.timer actor).status = .pending flight)
    (generationEq : generation = flight.retries) (due : flight.deadline ≤ (before.timer actor).now)
    (ordered : (before.last.isNone || decide (before.last.getD 0 < index)) = true) :
    ∃ effect original output,
      evaluate before index (.timeout actor generation true) = .ok effect ∧
      before.source flight.source = some original ∧ original.index = flight.source ∧
      original.actor = actor ∧ original.kind = (match actor with | .active => .syn | .passive => .synAck) ∧
      effect.output = some output ∧ output.index = index ∧ output.actor = actor ∧
      output.kind = original.kind ∧ output.packet = original.packet ∧
      output.cause = .timeout original.index generation := by
  obtain ⟨packet, retry, timerKindEq, original, member, sourceIndex, sourceActor, sourceKind, sourcePacket⟩ :=
    pending_timeout_template invariant pending
  have lookup := timeout_source_of_member emissionOrder member
  rw [sourceIndex] at lookup
  have expired : ∃ after, HandshakeTimer.expire (before.timer actor) generation = .ok after := by
    simp only [HandshakeTimer.expire, pending, generationEq, ne_eq, not_true_eq_false, ite_false,
      Nat.not_lt.mpr due]
    exact ⟨_, rfl⟩
  obtain ⟨timer, timed⟩ := expired
  let next := before.withTimer actor timer (HandshakeTimer.expire_valid (before.timer_valid actor) timed)
  let output : Emission := ⟨index, actor, original.kind, original.packet, .timeout original.index generation⟩
  let effect : Effect active passive :=
    { publish next output with state := { (publish next output).state with last := some index } }
  have succeeded : timeout before index actor generation true = .ok (publish next output) := by
    simp only [timeout, pending,
      show ¬generation ≠ flight.retries from fun different => different generationEq,
      ne_eq, not_true_eq_false, Bool.not_true, Bool.false_eq_true, ite_false,
      retry, timerKindEq, lookup, sourceActor, sourceKind,
      false_or, bind, Except.bind, pure, Except.pure, output, next]
    split
    · rename_i reason failed
      have impossible := failed.symm.trans timed
      cases impossible
    · rename_i actualTimer computed
      have same : actualTimer = timer := Except.ok.inj (computed.symm.trans timed)
      subst actualTimer
      rfl
  have evaluated : evaluate before index (.timeout actor generation true) = .ok effect := by
    simp only [evaluate, ordered, Bool.not_true, Bool.false_eq_true, ite_false,
      succeeded, bind, Except.bind, pure, Except.pure, effect]
  exact ⟨effect, original, output, evaluated, lookup, sourceIndex, sourceActor, sourceKind, rfl, rfl, rfl, rfl, rfl, rfl⟩

end Netlib.Check.TCPHandshakeRecovery

namespace Netlib.Check.TCPHandshakeRecovery

open Protocol.TCP

variable {active passive : H.Local} {before : State active passive} {effect : Effect active passive} {output : Emission}

private theorem onSyn_output_ttl (computed : onSyn before receipt policy = .ok effect)
    (emitted : effect.output = some output) : 1 < output.packet.packet.ip.packet.ttl.toNat := by
  unfold onSyn at computed
  repeat' first
    | (solve | cases computed)
    | (split at computed)
    | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)
  all_goals
    simp only [Except.ok.injEq] at computed
    subst effect
    dsimp only [respond, publish] at emitted
    cases emitted
    first
      | (solve | rw [SynReceived.output_ttl]; decide)
      | (solve | rw [HandshakeDuplicate.BareAck.ttl]; decide)

private theorem onSynAck_output_ttl (computed : onSynAck before receipt policy = .ok effect)
    (emitted : effect.output = some output) : 1 < output.packet.packet.ip.packet.ttl.toNat := by
  unfold onSynAck at computed
  repeat' first
    | (solve | cases computed)
    | (split at computed)
    | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)
  all_goals
    simp only [Except.ok.injEq] at computed
    subst effect
    dsimp only [respond, publish] at emitted
    cases emitted
    first
      | (solve | rw [ActiveEstablished.output_ttl]; decide)
      | (solve | rw [HandshakeDuplicate.BareAck.ttl]; decide)

private theorem receive_output_ttl (computed : receive before index source bytes path policy = .ok effect)
    (emitted : effect.output = some output) : 1 < output.packet.packet.ip.packet.ttl.toNat := by
  unfold receive at computed
  repeat' first
    | (solve | cases computed)
    | (split at computed)
    | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)
  all_goals
    simp only [Except.ok.injEq] at computed
    subst effect
    rename_i result operated
    change result.output = some output at emitted
    first
      | (solve | exact onSyn_output_ttl operated emitted)
      | (solve | exact onSynAck_output_ttl operated emitted)
      | (solve | have quiet := onFinalAck_no_output operated; rw [quiet] at emitted; cases emitted)
      | (solve | have quiet := onSynReplyAck_no_output operated; rw [quiet] at emitted; cases emitted)

private theorem openConnection_output_ttl (computed : openConnection before index remote policy = .ok effect)
    (emitted : effect.output = some output) : 1 < output.packet.packet.ip.packet.ttl.toNat := by
  unfold openConnection at computed
  repeat' first
    | (solve | cases computed)
    | (split at computed)
    | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)
  simp only [Except.ok.injEq] at computed
  subst effect
  cases emitted
  rw [SynSent.output_ttl]
  decide

private theorem timeout_output_ttl (prior : OutputTTL before)
    (computed : timeout before index actor generation policy = .ok effect)
    (emitted : effect.output = some output) : 1 < output.packet.packet.ip.packet.ttl.toNat := by
  unfold timeout at computed
  repeat' first
    | (solve | cases computed)
    | (split at computed)
    | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)
  all_goals
    simp only [Except.ok.injEq] at computed
    subst effect
    first
      | (solve | cases emitted)
      | (cases emitted; have bounded := prior.source (by assumption); exact bounded)

theorem evaluate_output_ttl (prior : OutputTTL before)
    (computed : evaluate before index event = .ok effect) : OutputTTL effect.state := by
  intro output member
  rw [(evaluate_records computed).emissions] at member
  rcases List.mem_append.mp member with old | fresh
  · exact prior output old
  · have emitted : effect.output = some output := by simpa only [Option.mem_toList] using fresh
    unfold evaluate at computed
    dsimp only at computed
    cases event <;>
      repeat' first
        | (solve | cases computed)
        | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)
        | (split at computed)
    all_goals
      simp only [Except.ok.injEq] at computed
      subst effect
      rename_i result operated
      first
        | (solve | exact openConnection_output_ttl operated emitted)
        | (solve | exact receive_output_ttl operated emitted)
        | (solve | exact timeout_output_ttl prior operated emitted)
        | (solve | cases emitted)

end Netlib.Check.TCPHandshakeRecovery
namespace Netlib.Check.TCPHandshakeRecovery

open Protocol.TCP

variable {active passive : H.Local}
variable {before after : State active passive} {effect : Effect active passive} {receipt : Receipt}

private theorem onSyn_ack_inventory (prior : PhaseInvariant before) (inventory : AckInventory before)
    (computed : onSyn before receipt policy = .ok effect) : AckInventory effect.state := by
  cases phase : before.phase with
  | idle => simp [onSyn, phase] at computed
  | opened opened =>
    simp only [onSyn, phase] at computed
    repeat' first
      | (solve | cases computed)
      | (split at computed)
      | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)
    rename_i same sourceEq pending listened result next timerEq
    simp only [Except.ok.injEq] at computed
    subst effect
    apply AckInventory.publish
    · apply inventory.reframe
      · rw [phase]
        exact Phase.AckFrame.answered ⟨opened, policy, receipt.index, receipt.spec,
          same.property ▸ receipt.delivery, pending, listened⟩
      · exact (armTimer_logs timerEq).1
    · intro ack
      rcases ack with impossible | impossible <;> cases impossible
  | answered answered =>
    simp only [onSyn, phase] at computed
    repeat' first
      | (solve | cases computed)
      | (split at computed)
      | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)
    simp only [Except.ok.injEq] at computed
    subst effect
    apply AckInventory.publish inventory
    intro ack
    rw [phase]
    rfl
  | acknowledged acknowledged client =>
    simp only [onSyn, phase] at computed
    repeat' first
      | (solve | cases computed)
      | (split at computed)
      | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)
    simp only [Except.ok.injEq] at computed
    subst effect
    apply AckInventory.publish inventory
    intro ack
    rw [phase]
    rfl
  | complete complete client server =>
    simp only [onSyn, phase] at computed
    repeat' first
      | (solve | cases computed)
      | (split at computed)
      | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)
    simp only [Except.ok.injEq] at computed
    subst effect
    have clean := prior.2.1
    simp only [PreDataFrames, phase] at clean
    apply AckInventory.publish inventory
    intro ack
    simp only [phase, Phase.ackTemplate]
    exact congrArg some (Completed.current_passive_ack_eq complete clean.2 _).symm

private theorem onSynAck_ack_inventory (prior : PhaseInvariant before) (inventory : AckInventory before)
    (computed : onSynAck before receipt policy = .ok effect) : AckInventory effect.state := by
  cases phase : before.phase with
  | idle | opened opened => simp [onSynAck, phase] at computed
  | answered answered =>
    simp only [onSynAck, phase] at computed
    repeat' first
      | (solve | cases computed)
      | (split at computed)
      | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)
    rename_i same sourceEq ready received result next timerEq
    simp only [Except.ok.injEq] at computed
    subst effect
    let acknowledged : O.Acknowledged active passive := ⟨answered, policy, receipt.index, receipt.spec,
      same.property ▸ receipt.delivery, ready, received⟩
    apply AckInventory.publish
    · apply inventory.reframe
      · rw [phase]
        exact Phase.AckFrame.acknowledged acknowledged _
      · exact (ackTimer_logs timerEq).1
    · intro ack
      rfl
  | acknowledged acknowledged client =>
    simp only [onSynAck, phase] at computed
    repeat' first
      | (solve | cases computed)
      | (split at computed)
      | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)
    simp only [Except.ok.injEq] at computed
    subst effect
    have clean := prior.2.1
    simp only [PreDataFrames, phase] at clean
    apply AckInventory.publish inventory
    intro ack
    simp only [phase, Phase.ackTemplate]
    exact congrArg some (Acknowledged.current_ack_eq acknowledged clean _).symm
  | complete complete client server =>
    simp only [onSynAck, phase] at computed
    repeat' first
      | (solve | cases computed)
      | (split at computed)
      | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)
    simp only [Except.ok.injEq] at computed
    subst effect
    have clean := prior.2.1
    simp only [PreDataFrames, phase] at clean
    apply AckInventory.publish inventory
    intro ack
    simp only [phase, Phase.ackTemplate]
    exact congrArg some (Completed.current_active_ack_eq complete clean.1 _).symm

private theorem openConnection_ack_inventory (inventory : AckInventory before)
    (computed : openConnection before index remote policy = .ok effect) : AckInventory effect.state := by
  unfold openConnection at computed
  repeat' first
    | (solve | cases computed)
    | (split at computed)
    | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)
  all_goals
    simp only [Except.ok.injEq] at computed
    subst effect
    rename_i pending opened result next timerEq
    apply AckInventory.publish
    · apply inventory.reframe
      · rw [show before.phase = .idle by assumption]
        exact Phase.AckFrame.initial _
      · exact (armTimer_logs timerEq).1
    · intro ack; rcases ack with impossible | impossible <;> cases impossible

private theorem onFinalAck_ack_inventory (inventory : AckInventory before)
    (computed : onFinalAck before receipt = .ok effect) : AckInventory effect.state := by
  cases phase : before.phase with
  | idle | opened opened | answered answered => simp [onFinalAck, phase] at computed
  | acknowledged acknowledged client =>
    simp only [onFinalAck, phase] at computed
    repeat' first
      | (solve | cases computed)
      | (split at computed)
      | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)
    simp only [Except.ok.injEq] at computed
    subst effect
    rename_i next timerEq
    apply inventory.reframe
    · rw [phase]
      exact Phase.AckFrame.finish acknowledged receipt.index receipt.spec _ _ _ _ client
    · exact (ackTimer_logs (after := next) timerEq).1
  | complete complete client server =>
    simp only [onFinalAck, phase] at computed
    repeat' first
      | (solve | cases computed)
      | (split at computed)
      | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)
    simp only [Except.ok.injEq] at computed
    subst effect
    apply inventory.reframe
    · rw [phase]
      exact Phase.AckFrame.complete_current complete _ _ _ _
    · rfl

private theorem onSynReplyAck_ack_inventory (inventory : AckInventory before)
    (computed : onSynReplyAck before receipt = .ok effect) : AckInventory effect.state := by
  cases phase : before.phase with
  | idle => simp [onSynReplyAck, phase] at computed
  | opened opened | answered opened =>
    simp only [onSynReplyAck, phase] at computed
    repeat' first
      | (solve | cases computed)
      | (split at computed)
      | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)
    cases computed
    exact inventory
  | acknowledged acknowledged client =>
    simp only [onSynReplyAck, phase] at computed
    repeat' first
      | (solve | cases computed)
      | (split at computed)
      | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)
    simp only [Except.ok.injEq] at computed
    subst effect
    apply inventory.reframe
    · rw [phase]
      exact Phase.AckFrame.acknowledged_current acknowledged _ _
    · rfl
  | complete complete client server =>
    simp only [onSynReplyAck, phase] at computed
    repeat' first
      | (solve | cases computed)
      | (split at computed)
      | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)
    simp only [Except.ok.injEq] at computed
    subst effect
    apply inventory.reframe
    · rw [phase]
      exact Phase.AckFrame.complete_current complete _ _ _ _
    · rfl

private theorem ack_inventory_same (inventory : AckInventory before)
    (phase : after.phase = before.phase) (emissions : after.emissions = before.emissions) : AckInventory after :=
  inventory.reframe (by rw [phase]; exact Phase.AckFrame.refl _) emissions

private theorem timeout_ack_inventory (inventory : AckInventory before)
    (computed : timeout before index actor generation policy = .ok effect) : AckInventory effect.state := by
  unfold timeout at computed
  repeat' first
    | (solve | cases computed)
    | (split at computed)
    | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)
  all_goals
    simp only [Except.ok.injEq] at computed
    subst effect
    first
      | (solve | exact inventory)
      | (
        rename_i original sourceEq timer expired correct kind retry permitted
        apply AckInventory.publish
        · cases actor <;> exact ack_inventory_same inventory rfl rfl
        · intro ack
          have sourceKind : original.kind = outputKind actor := by
            simpa only [not_or, ne_eq, Decidable.not_not] using (not_or.mp correct).2
          cases actor <;> simp only [outputKind] at sourceKind
          all_goals
            change AckKind original.kind at ack
            rcases ack with impossible | impossible
            all_goals rw [sourceKind] at impossible; cases impossible)

private theorem ack_inventory_retain (inventory : AckInventory effect.state) (receipt : Receipt) :
    AckInventory (retainReceipt effect receipt).state := ⟨inventory.templates⟩

private theorem ack_inventory_last (inventory : AckInventory before) (index : Nat) :
    AckInventory { before with last := some index } := ⟨inventory.templates⟩

private theorem ack_inventory_clock (inventory : AckInventory before)
    (computed : HandshakeTimer.advance (before.timer actor) now = .ok timer) :
    AckInventory (before.withTimer actor timer (HandshakeTimer.advance_valid (before.timer_valid actor) computed)) := by
  cases actor <;> exact ⟨inventory.templates⟩

private theorem receive_ack_inventory (prior : PhaseInvariant before) (inventory : AckInventory before)
    (computed : receive before index source bytes path policy = .ok effect) : AckInventory effect.state := by
  unfold receive at computed
  repeat' first
    | (solve | cases computed)
    | (split at computed)
    | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)
  all_goals
    simp only [Except.ok.injEq] at computed
    subst effect
    apply ack_inventory_retain
    first
      | exact onSyn_ack_inventory prior inventory (by assumption)
      | exact onSynAck_ack_inventory prior inventory (by assumption)
      | exact onFinalAck_ack_inventory inventory (by assumption)
      | exact onSynReplyAck_ack_inventory inventory (by assumption)

theorem evaluate_ack_inventory (prior : PhaseInvariant before) (inventory : AckInventory before)
    (computed : evaluate before index event = .ok effect) : AckInventory effect.state := by
  unfold evaluate at computed
  dsimp only at computed
  cases event <;>
    repeat' first
      | (solve | cases computed)
      | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)
      | (split at computed)
  all_goals
    simp only [Except.ok.injEq] at computed
    subst effect
    first
      | (solve | exact ack_inventory_last (openConnection_ack_inventory inventory (by assumption)) index)
      | (solve | exact ack_inventory_last (receive_ack_inventory prior inventory (by assumption)) index)
      | (solve | exact ack_inventory_last (timeout_ack_inventory inventory (by assumption)) index)
      | (solve | exact ack_inventory_last (ack_inventory_clock inventory (by assumption)) index)


end Netlib.Check.TCPHandshakeRecovery

namespace Netlib.Check.TCPHandshakeRecovery

open Protocol.TCP

variable {active passive : H.Local} {before : State active passive} {effect : Effect active passive}

private theorem order_at_next (prior : PhaseOrder before)
    (fresh : ∀ old, before.last = some old → old < index) : before.phase.OrderedAt index := by
  simpa only [PhaseOrder] using prior.restamp fresh

private theorem onSyn_phase_order (prior : PhaseOrder before)
    (fresh : ∀ old, before.last = some old → old < receipt.index)
    (computed : onSyn before receipt policy = .ok effect) : effect.state.phase.OrderedAt receipt.index := by
  have current := order_at_next prior fresh
  cases phase : before.phase with
  | idle => simp [onSyn, phase] at computed
  | opened opened =>
    have earlier := prior.opened_before phase fresh
    simp only [onSyn, phase] at computed
    repeat' first
      | (solve | cases computed)
      | (split at computed)
      | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)
    simp only [Except.ok.injEq] at computed
    subst effect
    exact ⟨earlier, Nat.le_refl _⟩
  | answered answered | acknowledged acknowledged client | complete complete client server =>
    simp only [onSyn, phase] at computed
    repeat' first
      | (solve | cases computed)
      | (split at computed)
      | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)
    all_goals
      simp only [Except.ok.injEq] at computed
      subst effect
      simpa only [phase, Phase.OrderedAt, respond, publish] using current

private theorem onSynAck_phase_order (prior : PhaseOrder before)
    (fresh : ∀ old, before.last = some old → old < receipt.index)
    (computed : onSynAck before receipt policy = .ok effect) : effect.state.phase.OrderedAt receipt.index := by
  have current := order_at_next prior fresh
  cases phase : before.phase with
  | idle | opened opened => simp [onSynAck, phase] at computed
  | answered answered =>
    have earlier := prior.answered_before phase fresh
    simp only [onSynAck, phase] at computed
    repeat' first
      | (solve | cases computed)
      | (split at computed)
      | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)
    simp only [Except.ok.injEq] at computed
    subst effect
    exact ⟨earlier.1, earlier.2, Nat.le_refl _⟩
  | acknowledged acknowledged client | complete complete client server =>
    simp only [onSynAck, phase] at computed
    repeat' first
      | (solve | cases computed)
      | (split at computed)
      | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)
    all_goals
      simp only [Except.ok.injEq] at computed
      subst effect
      simpa only [phase, Phase.OrderedAt, respond, publish] using current

private theorem onFinalAck_phase_order (prior : PhaseOrder before)
    (fresh : ∀ old, before.last = some old → old < receipt.index)
    (computed : onFinalAck before receipt = .ok effect) : effect.state.phase.OrderedAt receipt.index := by
  have current := order_at_next prior fresh
  cases phase : before.phase with
  | idle | opened opened | answered answered => simp [onFinalAck, phase] at computed
  | acknowledged acknowledged client =>
    simp only [onFinalAck, phase] at computed
    repeat' first
      | (solve | cases computed)
      | (split at computed)
      | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)
    simp only [Except.ok.injEq] at computed
    subst effect
    exact ⟨by assumption, Nat.le_refl _⟩
  | complete complete client server =>
    simp only [onFinalAck, phase] at computed
    repeat' first
      | (solve | cases computed)
      | (split at computed)
      | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)
    simp only [Except.ok.injEq] at computed
    subst effect
    simpa only [phase, Phase.OrderedAt] using current

private theorem onSynReplyAck_phase_order (prior : PhaseOrder before)
    (fresh : ∀ old, before.last = some old → old < receipt.index)
    (computed : onSynReplyAck before receipt = .ok effect) : effect.state.phase.OrderedAt receipt.index := by
  have current := order_at_next prior fresh
  cases phase : before.phase with
  | idle => simp [onSynReplyAck, phase] at computed
  | opened opened | answered answered | acknowledged acknowledged client | complete complete client server =>
    simp only [onSynReplyAck, phase] at computed
    repeat' first
      | (solve | cases computed)
      | (split at computed)
      | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)
    all_goals
      simp only [Except.ok.injEq] at computed
      subst effect
      simpa only [phase, Phase.OrderedAt] using current

private theorem receive_phase_order (prior : PhaseOrder before)
    (fresh : ∀ old, before.last = some old → old < index)
    (computed : receive before index source bytes path policy = .ok effect) : effect.state.phase.OrderedAt index := by
  unfold receive at computed
  repeat' first
    | (solve | cases computed)
    | (split at computed)
    | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)
  all_goals
    simp only [Except.ok.injEq] at computed
    subst effect
    rename_i receiptResult received receivedAt kind actor kindAt actorAt resultResult result operated
    have same := (receivePacket_fields (before := before) (index := index) (source := source)
      (bytes := bytes) (path := path) (by assumption)).1
    have freshReceipt : ∀ old, before.last = some old → old < received.index := by
      rw [same]
      exact fresh
    first
      | (solve | simpa only [retainReceipt, same] using onSyn_phase_order prior freshReceipt (by assumption))
      | (solve | simpa only [retainReceipt, same] using onSynAck_phase_order prior freshReceipt (by assumption))
      | (solve | simpa only [retainReceipt, same] using onFinalAck_phase_order prior freshReceipt (by assumption))
      | (solve | simpa only [retainReceipt, same] using onSynReplyAck_phase_order prior freshReceipt (by assumption))

private theorem openConnection_phase_order (computed : openConnection before index remote policy = .ok effect) :
    effect.state.phase.OrderedAt index := by
  obtain ⟨opened, _, phase, _, _, stamp, _⟩ := openConnection_opened computed
  simp only [phase, Phase.OrderedAt, stamp, Nat.le_refl]

private theorem timeout_phase_order (prior : PhaseOrder before)
    (fresh : ∀ old, before.last = some old → old < index)
    (computed : timeout before index actor generation policy = .ok effect) : effect.state.phase.OrderedAt index := by
  have current := order_at_next prior fresh
  unfold timeout at computed
  repeat' first
    | (solve | cases computed)
    | (split at computed)
    | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)
  all_goals
    simp only [Except.ok.injEq] at computed
    subst effect
    first
      | exact current
      | (cases actor <;> exact current)

theorem evaluate_phase_order (prior : PhaseOrder before)
    (computed : evaluate before index event = .ok effect) : PhaseOrder effect.state := by
  have fresh : ∀ old, before.last = some old → old < index := fun _ last => evaluate_order computed last
  unfold evaluate at computed
  dsimp only at computed
  cases event <;>
    repeat' first
      | (solve | cases computed)
      | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)
      | (split at computed)
  all_goals
    simp only [Except.ok.injEq] at computed
    subst effect
    rename_i next operated
    first
      | (solve | simpa only [PhaseOrder] using openConnection_phase_order (before := before) (effect := next) operated)
      | (solve | simpa only [PhaseOrder] using receive_phase_order (effect := next) prior fresh operated)
      | (solve | simpa only [PhaseOrder] using timeout_phase_order (effect := next) prior fresh operated)
      | (solve | cases ‹Side› <;> simpa only [PhaseOrder, State.withTimer] using order_at_next prior fresh)

end Netlib.Check.TCPHandshakeRecovery

namespace Netlib.Check.TCPHandshakeRecovery

open Protocol.TCP

variable {active passive : H.Local} {before : State active passive} {receipt : Receipt}

private theorem receive_source_packet (same : receipt.source.packet = packet) :
    ∃ chosen, source_packet receipt packet = .ok chosen := by
  unfold source_packet
  split
  · exact ⟨_, rfl⟩
  · rename_i different
    exact False.elim (different (congrArg EstablishedReceive.Input.bytes same))

private theorem receive_delivery_input (same : source = packet) (delivery : X.Delivery source spec) :
    (same ▸ delivery).input = delivery.input := by cases same; rfl

private theorem receive_duplicate (same : SameDecoded packet original) : duplicate_input packet original = .ok () := by
  unfold SameDecoded at same
  unfold duplicate_input
  exact ite_eq_left same

private theorem receive_arm (idle : (before.timer actor).status = .idle) :
    ∃ next, armTimer before actor kind index = .ok next := by
  have enabled : ∃ timer, HandshakeTimer.arm (before.timer actor) kind index = .ok timer := by
    simp only [HandshakeTimer.arm, idle]
    exact ⟨_, rfl⟩
  obtain ⟨timer, computed⟩ := enabled
  unfold armTimer
  split
  · rename_i reason failed
    rw [computed] at failed
    cases failed
  · exact ⟨_, rfl⟩

private theorem receive_ack_timer (pending : TimerPending (before.timer actor) kind source) :
    ∃ next, ackTimer before actor kind source = .ok next := by
  obtain ⟨flight, status, kindEq, sourceEq⟩ := pending
  have enabled : ∃ timer, HandshakeTimer.acknowledge (before.timer actor) = .ok timer := by
    simp only [HandshakeTimer.acknowledge, status]
    exact ⟨_, rfl⟩
  obtain ⟨timer, computed⟩ := enabled
  simp only [ackTimer, status, kindEq, sourceEq, and_self, ↓reduceIte]
  split
  · rename_i reason failed
    rw [computed] at failed
    cases failed
  · exact ⟨_, rfl⟩

private def ReceiveResult (before : State active passive) (receipt : Receipt) (effect : Effect active passive) : Prop :=
  phaseLevel effect.state.phase = receiveLevel (phaseLevel before.phase) receipt.source.kind ∧
    ResponseKind (receiveResponse before.phase receipt.source.kind) effect.output

private theorem receive_on_syn (prior : PhaseInvariant before) (kind : receipt.source.kind = .syn)
    (fields : ReceiveFields before receipt) :
    ∃ effect, onSyn before receipt true = .ok effect ∧ ReceiveResult before receipt effect := by
  have ready := fields.2
  cases phase : before.phase with
  | idle => simp only [kind, phase, ReceiveFields] at fields; cases fields.2
  | opened opened =>
    simp only [kind, phase] at ready
    obtain ⟨chosen, chosenAt⟩ := receive_source_packet ready.1
    let delivery : X.Delivery opened.pending.output receipt.spec := chosen.property ▸ receipt.delivery
    have inputEq : delivery.input = receipt.delivery.input := receive_delivery_input chosen.property receipt.delivery
    obtain ⟨pending, listened⟩ := Handshake.listenSyn_enabled passive delivery.input ready.2.1
      (by rw [inputEq]; exact ready.2.2.1) (by rw [inputEq]; exact ready.2.2.2)
    have timers := prior.1
    simp only [PhaseTimers, phase] at timers
    obtain ⟨next, armed⟩ := receive_arm (before := before) (actor := .passive) (kind := .synAck) (index := receipt.index) timers.2
    simp only [onSyn, phase, chosenAt, bind, Except.bind]
    split
    · rename_i reason failed
      rw [listened] at failed
      cases failed
    · rename_i selected selectedAt
      have same : selected = pending := Except.ok.inj (selectedAt.symm.trans listened)
      subst selected
      rw [armed]
      dsimp only [bind, Except.bind, pure, Except.pure]
      refine ⟨_, rfl, ?_, ?_⟩
      · simp [respond, publish, phase, kind, receiveLevel, phaseLevel]
      · simp only [receiveResponse, phase, kind, ResponseKind]
        exact ⟨_, rfl, rfl, rfl⟩
  | answered answered =>
    simp only [kind, phase] at ready
    obtain ⟨chosen, chosenAt⟩ := receive_source_packet ready.1
    simp only [onSyn, phase, chosenAt, bind, Except.bind, receive_duplicate ready.2, pure, Except.pure]
    refine ⟨_, rfl, ?_, ?_⟩
    · simp [respond, publish, phase, kind, receiveLevel, phaseLevel]
    · simp only [receiveResponse, phase, kind, ResponseKind]
      exact ⟨_, rfl, rfl, rfl⟩
  | acknowledged acknowledged client =>
    simp only [kind, phase] at ready
    obtain ⟨chosen, chosenAt⟩ := receive_source_packet ready.1
    simp only [onSyn, phase, chosenAt, bind, Except.bind, receive_duplicate ready.2, pure, Except.pure]
    refine ⟨_, rfl, ?_, ?_⟩
    · simp [respond, publish, phase, kind, receiveLevel, phaseLevel]
    · simp only [receiveResponse, phase, kind, ResponseKind]
      exact ⟨_, rfl, rfl, rfl⟩
  | complete complete client server =>
    simp only [kind, phase] at ready
    obtain ⟨chosen, chosenAt⟩ := receive_source_packet ready.1
    simp only [onSyn, phase, chosenAt, bind, Except.bind, receive_duplicate ready.2, pure, Except.pure]
    refine ⟨_, rfl, ?_, ?_⟩
    · simp [respond, publish, phase, kind, receiveLevel, phaseLevel]
    · simp only [receiveResponse, phase, kind, ResponseKind]
      exact ⟨_, rfl, rfl, rfl⟩

private theorem receive_on_synAck (prior : PhaseInvariant before) (kind : receipt.source.kind = .synAck)
    (fields : ReceiveFields before receipt) :
    ∃ effect, onSynAck before receipt true = .ok effect ∧ ReceiveResult before receipt effect := by
  have ready := fields.2
  cases phase : before.phase with
  | idle | opened opened => simp only [kind, phase] at ready
  | answered answered =>
    simp only [kind, phase] at ready
    obtain ⟨chosen, chosenAt⟩ := receive_source_packet ready.1
    let delivery : X.Delivery answered.pending.output receipt.spec := chosen.property ▸ receipt.delivery
    have inputEq : delivery.input = receipt.delivery.input := receive_delivery_input chosen.property receipt.delivery
    obtain ⟨established, accepted⟩ := Handshake.synSentSynAck_enabled answered.opened.pending delivery.input
      (by rw [inputEq]; exact ready.2)
    have timers := prior.1
    simp only [PhaseTimers, phase] at timers
    obtain ⟨next, acknowledged⟩ := receive_ack_timer (before := before) (actor := .active) timers.1
    simp only [onSynAck, phase, chosenAt, bind, Except.bind]
    split
    · rename_i reason failed
      rw [accepted] at failed
      cases failed
    · rename_i selected selectedAt
      have same : selected = established := Except.ok.inj (selectedAt.symm.trans accepted)
      subst selected
      rw [acknowledged]
      dsimp only [bind, Except.bind, pure, Except.pure]
      refine ⟨_, rfl, ?_, ?_⟩
      · simp [respond, publish, phase, kind, receiveLevel, phaseLevel]
      · simp only [receiveResponse, kind, ResponseKind]
        exact ⟨_, rfl, rfl, rfl⟩
  | acknowledged acknowledged client =>
    simp only [kind, phase] at ready
    obtain ⟨chosen, chosenAt⟩ := receive_source_packet ready.1
    simp only [onSynAck, phase, chosenAt, bind, Except.bind, receive_duplicate ready.2, pure, Except.pure]
    refine ⟨_, rfl, ?_, ?_⟩
    · simp [respond, publish, phase, kind, receiveLevel, phaseLevel]
    · simp only [receiveResponse, kind, ResponseKind]
      exact ⟨_, rfl, rfl, rfl⟩
  | complete complete client server =>
    simp only [kind, phase] at ready
    obtain ⟨chosen, chosenAt⟩ := receive_source_packet ready.1
    simp only [onSynAck, phase, chosenAt, bind, Except.bind, receive_duplicate ready.2, pure, Except.pure]
    refine ⟨_, rfl, ?_, ?_⟩
    · simp [respond, publish, phase, kind, receiveLevel, phaseLevel]
    · simp only [receiveResponse, kind, ResponseKind]
      exact ⟨_, rfl, rfl, rfl⟩

private theorem receive_empty_ack (before : PreData seed) (clean : PreDataClean seed before)
    (fields : EmptyAckFields before packet index) :
    ∃ applied, before.receiveAck packet index = .ok applied := by
  obtain ⟨applied, computed, _⟩ := PreData.receiveAck_enabled before clean packet index
    fields.1 fields.2.1 ⟨fields.2.2.1, fields.2.2.2.1⟩ fields.2.2.2.2
  exact ⟨applied, computed⟩

private theorem receive_on_finalAck (prior : PhaseInvariant before) (kind : receipt.source.kind = .finalAck)
    (fields : ReceiveFields before receipt) :
    ∃ effect, onFinalAck before receipt = .ok effect ∧ ReceiveResult before receipt effect := by
  have ready := fields.2
  cases phase : before.phase with
  | idle | opened opened | answered answered => simp only [kind, phase] at ready
  | acknowledged acknowledged client =>
    simp only [kind, phase] at ready
    obtain ⟨chosen, chosenAt⟩ := receive_source_packet ready.1
    let delivery : X.Delivery acknowledged.ready.output receipt.spec := chosen.property ▸ receipt.delivery
    have inputEq : delivery.input = receipt.delivery.input := receive_delivery_input chosen.property receipt.delivery
    obtain ⟨established, accepted⟩ := Handshake.synReceivedAck_enabled acknowledged.answered.pending delivery.input
      (by rw [inputEq]; exact ready.2.1)
    have timers := prior.1
    simp only [PhaseTimers, phase] at timers
    obtain ⟨next, acked⟩ := receive_ack_timer (before := before) (actor := .passive) timers.2
    simp only [onFinalAck, phase, chosenAt, bind, Except.bind]
    split
    · rename_i reason failed
      rw [accepted] at failed
      cases failed
    · rename_i selected selectedAt
      have same : selected = established := Except.ok.inj (selectedAt.symm.trans accepted)
      subst selected
      rw [dite_eq_left ready.2.2]
      rw [acked]
      dsimp only [bind, Except.bind, pure, Except.pure]
      refine ⟨_, rfl, ?_, ?_⟩
      · simp only [kind, receiveLevel, phaseLevel]
      · simp only [receiveResponse, kind, ResponseKind]
  | complete complete client server =>
    simp only [kind, phase] at ready
    have clean := prior.2.1
    simp only [PreDataFrames, phase] at clean
    obtain ⟨applied, appliedAt⟩ := receive_empty_ack server clean.2 ready
    simp only [onFinalAck, phase, appliedAt, bind, Except.bind, pure, Except.pure]
    refine ⟨_, rfl, ?_, ?_⟩
    · simp only [kind, receiveLevel, phaseLevel]
    · simp only [receiveResponse, kind, ResponseKind]

private theorem receive_discard (fields : DiscardAckFields active opened receipt.delivery.input) :
    discardBareAck opened receipt = .ok () := by
  unfold DiscardAckFields at fields
  unfold discardBareAck
  exact ite_eq_left fields

private theorem receive_on_synReplyAck (prior : PhaseInvariant before) (kind : receipt.source.kind = .synReplyAck)
    (fields : ReceiveFields before receipt) :
    ∃ effect, onSynReplyAck before receipt = .ok effect ∧ ReceiveResult before receipt effect := by
  have ready := fields.2
  cases phase : before.phase with
  | idle => simp only [kind, phase] at ready
  | opened opened =>
    simp only [kind, phase] at ready
    simp only [onSynReplyAck, phase, receive_discard ready, bind, Except.bind, pure, Except.pure]
    refine ⟨_, rfl, ?_, ?_⟩
    · simp only [phase, kind, receiveLevel]
    · simp only [receiveResponse, kind, ResponseKind]
  | answered answered =>
    simp only [kind, phase] at ready
    simp only [onSynReplyAck, phase, receive_discard ready, bind, Except.bind, pure, Except.pure]
    refine ⟨_, rfl, ?_, ?_⟩
    · simp only [phase, kind, receiveLevel]
    · simp only [receiveResponse, kind, ResponseKind]
  | acknowledged acknowledged client =>
    simp only [kind, phase] at ready
    have clean := prior.2.1
    simp only [PreDataFrames, phase] at clean
    obtain ⟨applied, appliedAt⟩ := receive_empty_ack client clean ready
    simp only [onSynReplyAck, phase, appliedAt, bind, Except.bind, pure, Except.pure]
    refine ⟨_, rfl, ?_, ?_⟩
    · simp only [phase, kind, receiveLevel, phaseLevel]
    · simp only [receiveResponse, kind, ResponseKind]
  | complete complete client server =>
    simp only [kind, phase] at ready
    have clean := prior.2.1
    simp only [PreDataFrames, phase] at clean
    obtain ⟨applied, appliedAt⟩ := receive_empty_ack client clean.1 ready
    simp only [onSynReplyAck, phase, appliedAt, bind, Except.bind, pure, Except.pure]
    refine ⟨_, rfl, ?_, ?_⟩
    · simp only [phase, kind, receiveLevel, phaseLevel]
    · simp only [receiveResponse, kind, ResponseKind]

private theorem receive_packet_input (input : ReceiveInput before index path) :
    receivePacket before index input.source.index input.packet.bytes path = .ok input.receipt := by
  simp only [receivePacket, input.selected, input.earlier, dite_true, bind, Except.bind,
    TCPHandshakeWireDelivery.input_parsed input.packet, input.delivery.checked]
  rfl

private theorem receive_handler_enabled (prior : PhaseInvariant before) (fields : ReceiveFields before receipt) :
    ∃ effect,
      (match receipt.source.kind, receipt.source.actor with
      | .syn, .active => onSyn before receipt true
      | .synAck, .passive => onSynAck before receipt true
      | .finalAck, .active => onFinalAck before receipt
      | .synReplyAck, .passive => onSynReplyAck before receipt
      | _, _ => throw "The selected startup occurrence has a different control actor.") = .ok effect ∧
        ReceiveResult before receipt effect := by
  have actor := fields.1
  cases kind : receipt.source.kind with
  | syn =>
    have selected : receipt.source.actor = .active := by simpa only [kind, Kind.actor] using actor
    simp only [selected]
    exact receive_on_syn prior kind fields
  | synAck =>
    have selected : receipt.source.actor = .passive := by simpa only [kind, Kind.actor] using actor
    simp only [selected]
    exact receive_on_synAck prior kind fields
  | finalAck =>
    have selected : receipt.source.actor = .active := by simpa only [kind, Kind.actor] using actor
    simp only [selected]
    exact receive_on_finalAck prior kind fields
  | synReplyAck =>
    have selected : receipt.source.actor = .passive := by simpa only [kind, Kind.actor] using actor
    simp only [selected]
    exact receive_on_synReplyAck prior kind fields

private theorem receive_input_enabled (prior : PhaseInvariant before) (input : ReceiveInput before index path)
    (fields : ReceiveFields before input.receipt) :
    ∃ effect, receive before index input.source.index input.packet.bytes path true = .ok effect ∧
      ReceiveResult before input.receipt effect ∧ effect.receipt = some input.receipt := by
  obtain ⟨effect, handled, result⟩ := receive_handler_enabled prior fields
  have retained := congrArg
    (fun operation : Except String (Effect active passive) =>
      operation >>= fun next => pure (retainReceipt next input.receipt)) handled
  refine ⟨retainReceipt effect input.receipt, ?_, result, rfl⟩
  cases kind : input.receipt.source.kind <;> cases actor : input.receipt.source.actor <;>
    simpa only [receive, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
      receive_packet_input input, bind, Except.bind, pure, Except.pure, kind, actor] using retained

theorem evaluate_receive_enabled (prior : PhaseInvariant before) (input : ReceiveInput before index path)
    (ordered : ReceiveIndex before index) (fields : ReceiveFields before input.receipt) :
    ∃ effect, evaluate before index input.event = .ok effect ∧
      phaseLevel effect.state.phase = receiveLevel (phaseLevel before.phase) input.source.kind ∧
      ResponseKind (receiveResponse before.phase input.source.kind) effect.output ∧ effect.receipt = some input.receipt := by
  obtain ⟨effect, computed, result, receipt⟩ := receive_input_enabled prior input fields
  have fresh : (before.last.isNone || decide (before.last.getD 0 < index)) = true := ordered
  simp only [evaluate, ReceiveInput.event, fresh, Bool.not_true, Bool.false_eq_true, ↓reduceIte, computed,
    bind, Except.bind, pure, Except.pure]
  exact ⟨_, rfl, result.1, result.2, receipt⟩

end Netlib.Check.TCPHandshakeRecovery

namespace Netlib.Check.TCPHandshakeRecovery

open Protocol.TCP

variable {active passive : H.Local} {before : State active passive} {effect : Effect active passive}
variable {flight : HandshakeTimer.Flight}

private theorem timeout_pending_effect
    (pending : (before.timer actor).status = .pending flight)
    (generationEq : generation = flight.retries)
    (computed : timeout before index actor generation true = .ok effect) :
    ∃ timer, HandshakeTimer.expire (before.timer actor) generation = .ok timer ∧
      effect.state.phase = before.phase ∧ effect.state.timer actor = timer ∧
      effect.state.timer actor.other = before.timer actor.other ∧
      effect.decision = .accepted ∧ effect.receipt = none ∧ effect.application = none := by
  simp only [timeout, pending,
    show ¬generation ≠ flight.retries from fun different => different generationEq,
    ne_eq, Bool.not_true, Bool.false_eq_true, ite_false] at computed
  repeat' first
    | (solve | cases computed)
    | (split at computed)
    | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)
  all_goals
    simp only [Except.ok.injEq] at computed
    subst effect
    refine ⟨_, by assumption, ?_⟩
    cases actor <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem evaluate_timeout_effect
    (pending : (before.timer actor).status = .pending flight)
    (generationEq : generation = flight.retries)
    (computed : evaluate before index (.timeout actor generation true) = .ok effect) :
    ∃ timer, HandshakeTimer.expire (before.timer actor) generation = .ok timer ∧
      effect.state.phase = before.phase ∧ effect.state.timer actor = timer ∧
      effect.state.timer actor.other = before.timer actor.other ∧
      effect.decision = .accepted ∧ effect.receipt = none ∧ effect.application = none := by
  unfold evaluate at computed
  dsimp only at computed
  repeat' first
    | (solve | cases computed)
    | (split at computed)
    | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)
  simp only [Except.ok.injEq] at computed
  subst effect
  rename_i next operated
  exact timeout_pending_effect (effect := next) (index := index) pending generationEq operated

end Netlib.Check.TCPHandshakeRecovery

namespace Netlib.Check.TCPHandshakeRecovery

open Protocol.TCP

variable {active passive : H.Local} {before : State active passive} {effect : Effect active passive}

private theorem onSyn_same_level_timer_frame (computed : onSyn before receipt policy = .ok effect)
    (sameLevel : phaseLevel effect.state.phase = phaseLevel before.phase) :
    ∀ actor, effect.state.timer actor = before.timer actor := by
  cases phase : before.phase with
  | idle => simp [onSyn, phase] at computed
  | opened opened =>
    simp only [onSyn, phase] at computed
    repeat' first
      | (solve | cases computed)
      | (split at computed)
      | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)
    simp only [Except.ok.injEq] at computed
    subst effect
    simp only [respond, publish, phaseLevel, phase] at sameLevel
    cases sameLevel
  | answered answered | acknowledged acknowledged client | complete complete client server =>
    simp only [onSyn, phase] at computed
    repeat' first
      | (solve | cases computed)
      | (split at computed)
      | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)
    all_goals
      simp only [Except.ok.injEq] at computed
      subst effect
      intro actor
      cases actor <;> rfl

private theorem onSynAck_same_level_timer_frame (computed : onSynAck before receipt policy = .ok effect)
    (sameLevel : phaseLevel effect.state.phase = phaseLevel before.phase) :
    ∀ actor, effect.state.timer actor = before.timer actor := by
  cases phase : before.phase with
  | idle | opened opened => simp [onSynAck, phase] at computed
  | answered answered =>
    simp only [onSynAck, phase] at computed
    repeat' first
      | (solve | cases computed)
      | (split at computed)
      | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)
    simp only [Except.ok.injEq] at computed
    subst effect
    simp only [respond, publish, phaseLevel, phase] at sameLevel
    cases sameLevel
  | acknowledged acknowledged client | complete complete client server =>
    simp only [onSynAck, phase] at computed
    repeat' first
      | (solve | cases computed)
      | (split at computed)
      | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)
    all_goals
      simp only [Except.ok.injEq] at computed
      subst effect
      intro actor
      cases actor <;> rfl

private theorem onFinalAck_same_level_timer_frame (computed : onFinalAck before receipt = .ok effect)
    (sameLevel : phaseLevel effect.state.phase = phaseLevel before.phase) :
    ∀ actor, effect.state.timer actor = before.timer actor := by
  cases phase : before.phase with
  | idle | opened opened | answered answered => simp [onFinalAck, phase] at computed
  | acknowledged acknowledged client =>
    simp only [onFinalAck, phase] at computed
    repeat' first
      | (solve | cases computed)
      | (split at computed)
      | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)
    simp only [Except.ok.injEq] at computed
    subst effect
    simp only [phaseLevel, phase] at sameLevel
    cases sameLevel
  | complete complete client server =>
    simp only [onFinalAck, phase] at computed
    repeat' first
      | (solve | cases computed)
      | (split at computed)
      | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)
    simp only [Except.ok.injEq] at computed
    subst effect
    intro actor
    cases actor <;> rfl

private theorem onSynReplyAck_timer_frame (computed : onSynReplyAck before receipt = .ok effect) :
    ∀ actor, effect.state.timer actor = before.timer actor := by
  unfold onSynReplyAck at computed
  repeat' first
    | (solve | cases computed)
    | (split at computed)
    | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)
  all_goals
    simp only [Except.ok.injEq] at computed
    subst effect
    intro actor
    cases actor <;> rfl

private theorem receive_same_level_timer_frame
    (computed : receive before index source bytes path policy = .ok effect)
    (sameLevel : phaseLevel effect.state.phase = phaseLevel before.phase) :
    ∀ actor, effect.state.timer actor = before.timer actor := by
  unfold receive at computed
  repeat' first
    | (solve | cases computed)
    | (split at computed)
    | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)
  all_goals
    simp only [Except.ok.injEq] at computed
    subst effect
    rename_i result operated
    first
      | exact onSyn_same_level_timer_frame (effect := result) operated sameLevel
      | exact onSynAck_same_level_timer_frame (effect := result) operated sameLevel
      | exact onFinalAck_same_level_timer_frame (effect := result) operated sameLevel
      | exact onSynReplyAck_timer_frame (effect := result) operated

theorem evaluate_receive_timer_frame
    (computed : evaluate before index (.receive source bytes path policy) = .ok effect)
    (sameLevel : phaseLevel effect.state.phase = phaseLevel before.phase) :
    ∀ actor, effect.state.timer actor = before.timer actor := by
  unfold evaluate at computed
  dsimp only at computed
  repeat' first
    | (solve | cases computed)
    | (split at computed)
    | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)
  simp only [Except.ok.injEq] at computed
  subst effect
  rename_i result operated
  exact receive_same_level_timer_frame (effect := result) operated sameLevel

end Netlib.Check.TCPHandshakeRecovery
