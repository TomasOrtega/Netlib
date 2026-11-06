import Netlib.Protocol.TCP.EndpointReceiveFacts

/-!
# Application byte histories for the bounded TCP endpoint

The trace stores the actual result of each endpoint operation.
A time stamp orders model events. It is not a wire field.
The byte ledgers do not affect endpoint decisions.
The paired theorem requires an earlier peer output for each accepted input.
This environment condition does not prove native transmission or eventual delivery.
-/

namespace Netlib.Protocol.TCP.ApplicationTrace

abbrev Model := Endpoint.State
abbrev Input := EstablishedReceive.Input

inductive Event where
  | write (bytes : List UInt8)
  | send (count : Nat) (policyPermitted : Bool)
  | read (count : Nat)
  | emitAck (policyPermitted : Bool)
  | receive (input : Input)
  | enableRecovery
  | advanceClock (millis : Nat)
  | timeout (policyPermitted : Bool)
  | enableAck
  | dispatchAck (policyPermitted : Bool)

def evaluate (before : Model) : Event → Endpoint.Result
  | .write bytes => Endpoint.write before bytes
  | .send count policy => Endpoint.send before count policy
  | .read count => Endpoint.read before count
  | .emitAck policy => Endpoint.emitAck before policy
  | .receive input => Endpoint.receive before input
  | .enableRecovery => Endpoint.enableRecovery before
  | .advanceClock millis => Endpoint.advanceClock before millis
  | .timeout policy => Endpoint.timeout before policy
  | .enableAck => Endpoint.enableAck before
  | .dispatchAck policy => Endpoint.dispatchAck before policy

theorem evaluate_valid (before : Model) (valid : before.Valid) (event : Event) :
    (evaluate before event).state.Valid := by
  cases event with
  | write bytes => exact Endpoint.write_valid before bytes valid
  | send count policy => exact Endpoint.send_valid before count policy valid
  | read count => exact Endpoint.read_valid before count valid
  | emitAck policy => exact Endpoint.emitAck_valid before policy valid
  | receive input => exact Endpoint.receive_valid before input valid
  | enableRecovery => exact Endpoint.enableRecovery_valid before valid
  | advanceClock millis => exact Endpoint.advanceClock_valid before millis valid
  | timeout policy => exact Endpoint.timeout_valid before policy valid
  | enableAck => exact Endpoint.enableAck_valid before valid
  | dispatchAck policy => exact Endpoint.dispatchAck_valid before policy valid

theorem evaluate_storage_valid (before : Model) (event : Event) (valid : before.StorageValid) :
    (evaluate before event).state.StorageValid := by
  cases event with
  | write bytes => exact Endpoint.write_storage_valid before bytes valid
  | send count policy => exact Endpoint.send_storage_valid before count policy valid
  | read count => exact Endpoint.read_storage_valid before count valid
  | emitAck policy => exact Endpoint.emitAck_storage_valid before policy valid
  | receive input => exact Endpoint.receive_storage_valid before input valid
  | enableRecovery => exact Endpoint.enableRecovery_storage_valid before valid
  | advanceClock millis => exact Endpoint.advanceClock_storage_valid before millis valid
  | timeout policy => exact Endpoint.timeout_storage_valid before policy valid
  | enableAck => exact Endpoint.enableAck_storage_valid before valid
  | dispatchAck policy => exact Endpoint.dispatchAck_storage_valid before policy valid

structure Step where
  before : Model
  event : Event
  result : Endpoint.Result
  stamp : Nat
  beforeValid : before.Valid
  computed : result = evaluate before event

def Step.make (before : Model) (valid : before.Valid) (event : Event) (stamp : Nat := 0) : Step :=
  ⟨before, event, evaluate before event, stamp, valid, rfl⟩

def Step.supported (step : Step) : Bool :=
  match step.result.decision with
  | .unsupported _ | .recoveryUnsupported _ | .ackUnsupported _ => false
  | _ => true

theorem Step.valid (step : Step) : step.result.state.Valid := by
  rw [step.computed]
  exact evaluate_valid step.before step.beforeValid step.event

def written (event : Event) (result : Endpoint.Result) : List UInt8 :=
  match event, result.decision with
  | .write bytes, .accepted (.write _) => bytes
  | _, _ => []

def emitted (before : Model) (event : Event) (result : Endpoint.Result) : List UInt8 :=
  match event, result.decision with
  | .send count _, .accepted (.send _) => before.pending.take count
  | _, _ => []

def acknowledged (before : Model) (event : Event) (result : Endpoint.Result) : List UInt8 :=
  match event, result.decision with
  | .receive _, .accepted (.receive count _) => before.core.sent.take count
  | _, _ => []

def acceptedPayload (event : Event) (result : Endpoint.Result) : List UInt8 :=
  match event, result.decision with
  | .receive input, .accepted (.receive _ _) => input.packet.segment.payload
  | _, _ => []

def releasedPayload (before : Model) (event : Event) (result : Endpoint.Result) : List UInt8 :=
  match event with
  | .receive _ => result.state.core.received.drop before.core.received.length
  | _ => []

def Step.written (step : Step) : List UInt8 := ApplicationTrace.written step.event step.result

def Step.emitted (step : Step) : List UInt8 := ApplicationTrace.emitted step.before step.event step.result

def Step.acknowledged (step : Step) : List UInt8 := ApplicationTrace.acknowledged step.before step.event step.result

def Step.acceptedPayload (step : Step) : List UInt8 := ApplicationTrace.acceptedPayload step.event step.result

def Step.releasedPayload (step : Step) : List UInt8 := ApplicationTrace.releasedPayload step.before step.event step.result

def Step.readBytes (step : Step) : List UInt8 := step.result.read

def Balanced (before : Model) (event : Event) (result : Endpoint.Result) : Prop :=
  before.pending ++ written event result = emitted before event result ++ result.state.pending ∧
  before.core.sent ++ emitted before event result = acknowledged before event result ++ result.state.core.sent ∧
  before.core.received ++ releasedPayload before event result = result.read ++ result.state.core.received ∧
  result.state.core.sendNext = before.core.sendNext.add (emitted before event result).length ∧
  result.state.core.receiveNext = before.core.receiveNext.add (releasedPayload before event result).length ∧
  result.state.core.sendUna = before.core.sendUna.add (acknowledged before event result).length

private def FramedBalanced (before : Model) (event : Event) (result : Endpoint.Result) : Prop :=
  Balanced before event result ∧ result.state.localReceiveMSS = before.localReceiveMSS

private theorem rejected_balanced (before : Model) (event : Event) (reason : Endpoint.Reject) :
    FramedBalanced before event (Endpoint.rejected before reason) := by
  cases event <;> simp [FramedBalanced, Balanced, Endpoint.rejected, written, emitted, acknowledged, releasedPayload]

private theorem recoveryBlocked_balanced (before : Model) (event : Event) (reason : Recovery.Stop) :
    FramedBalanced before event (Endpoint.recoveryBlocked before reason) := by
  unfold Endpoint.recoveryBlocked
  split
  · cases event <;> simp [FramedBalanced, Balanced, written, emitted, acknowledged, releasedPayload]
  · exact rejected_balanced _ _ _

private theorem ackBlocked_balanced (before : Model) (event : Event) (reason : AckReaction.Stop) :
    FramedBalanced before event (Endpoint.ackBlocked before reason) := by
  unfold Endpoint.ackBlocked
  split
  · cases event <;> simp [FramedBalanced, Balanced, written, emitted, acknowledged, releasedPayload]
  · exact rejected_balanced _ _ _

private theorem balanced_withRuntime (before : Model) (event : Event) (result : Endpoint.Result)
    (recovery : Option Recovery.State) (ackReaction : Option AckReaction.State) :
    FramedBalanced before event { result with state := { result.state with recovery, ackReaction } } ↔
      FramedBalanced before event result := Iff.rfl

private theorem balanced_withRecovery (before : Model) (event : Event) (result : Endpoint.Result)
    (recovery : Option Recovery.State) :
    FramedBalanced before event { result with state := { result.state with recovery } } ↔ FramedBalanced before event result := Iff.rfl

private theorem receive_balanced (before : Model) (input : Input) :
    FramedBalanced before (.receive input) (Endpoint.receive before input) := by
  obtain ⟨pending, sent, received, sendNext, receiveNext, sendUna, own, _, read⟩ := Endpoint.receive_effects before input
  have released : releasedPayload before (.receive input) (Endpoint.receive before input) = Endpoint.receivedBytes before input := by
    simp only [releasedPayload, received, List.drop_left]
  have retired : acknowledged before (.receive input) (Endpoint.receive before input) =
      before.core.sent.take (Endpoint.receiveRetired (Endpoint.receive before input)) := by
    cases decision : (Endpoint.receive before input).decision with
    | reject _ | unsupported _ | recoveryUnsupported _ | ackUnsupported _ => simp [acknowledged, Endpoint.receiveRetired, decision]
    | accepted action => cases action <;> simp [acknowledged, Endpoint.receiveRetired, decision]
  have length : (acknowledged before (.receive input) (Endpoint.receive before input)).length =
      Endpoint.receiveRetired (Endpoint.receive before input) := by
    rw [retired, List.length_take, Nat.min_eq_left (Endpoint.receiveRetired_bound before input)]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, own⟩
  · simpa only [written, emitted, List.append_nil, List.nil_append] using pending.symm
  · simp only [emitted, List.append_nil, retired, sent, List.take_append_drop]
  · simp only [released, read, List.nil_append, received]
  · simpa only [emitted, List.length_nil, Seq.add_zero] using sendNext
  · rw [released]
    exact receiveNext
  · rw [length]
    exact sendUna

private theorem evaluate_balanced (before : Model) (event : Event) :
    FramedBalanced before event (evaluate before event) := by
  cases event with
  | write bytes =>
    change FramedBalanced before (.write bytes) (Endpoint.write before bytes)
    unfold Endpoint.write
    split
    · exact rejected_balanced _ _ _
    · split
      · exact rejected_balanced _ _ _
      · simp [FramedBalanced, Balanced, written, emitted, acknowledged, releasedPayload, Endpoint.writeState]
  | read count =>
    change FramedBalanced before (.read count) (Endpoint.read before count)
    unfold Endpoint.read
    split
    · exact rejected_balanced _ _ _
    · split
      · exact rejected_balanced _ _ _
      · simp [FramedBalanced, Balanced, written, emitted, acknowledged, releasedPayload, Endpoint.readState]
  | send count policy =>
    change FramedBalanced before (.send count policy) (Endpoint.send before count policy)
    unfold Endpoint.send
    split
    · exact rejected_balanced _ _ _
    · split
      · exact rejected_balanced _ _ _
      · split
        · split
          · exact recoveryBlocked_balanced _ _ _
          · exact rejected_balanced _ _ _
        · rename_i ready
          cases prepared : Endpoint.ackReady before with
          | error reason => exact ackBlocked_balanced _ _ _
          | ok answer =>
            cases answer
            cases encoded : Endpoint.emit before (before.pending.take count) with
            | error reason => exact rejected_balanced _ _ _
            | ok output =>
              have bounded := (Decidable.not_not.mp ready).2.1
              have size : (before.pending.take count).length = count := by simp [List.length_take, Nat.min_eq_left bounded]
              simp [FramedBalanced, Balanced, written, emitted, acknowledged, releasedPayload, Endpoint.sendState, Endpoint.outputState, size]
  | emitAck policy =>
    change FramedBalanced before (.emitAck policy) (Endpoint.pureAck before policy false)
    unfold Endpoint.pureAck
    repeat' first
      | (solve | exact rejected_balanced _ _ _)
      | (solve | exact ackBlocked_balanced _ _ _)
      | (solve | simp [FramedBalanced, Balanced, written, emitted, acknowledged, releasedPayload, Endpoint.outputState])
      | split
  | dispatchAck policy =>
    change FramedBalanced before (.dispatchAck policy) (Endpoint.pureAck before policy true)
    unfold Endpoint.pureAck
    repeat' first
      | (solve | exact rejected_balanced _ _ _)
      | (solve | exact ackBlocked_balanced _ _ _)
      | (solve | simp [FramedBalanced, Balanced, written, emitted, acknowledged, releasedPayload, Endpoint.outputState])
      | split
  | receive input =>
    exact receive_balanced before input
  | enableRecovery =>
    change FramedBalanced before .enableRecovery (Endpoint.enableRecovery before)
    unfold Endpoint.enableRecovery
    split
    · exact rejected_balanced _ _ _
    · split
      · exact recoveryBlocked_balanced _ _ _
      · simp [FramedBalanced, Balanced, written, emitted, acknowledged, releasedPayload]
  | advanceClock millis =>
    change FramedBalanced before (.advanceClock millis) (Endpoint.advanceClock before millis)
    unfold Endpoint.advanceClock
    repeat' first
      | (solve | exact rejected_balanced _ _ _)
      | (solve | exact recoveryBlocked_balanced _ _ _)
      | (solve | exact ackBlocked_balanced _ _ _)
      | (solve | simp [FramedBalanced, Balanced, written, emitted, acknowledged, releasedPayload])
      | split
  | timeout policy =>
    change FramedBalanced before (.timeout policy) (Endpoint.timeout before policy)
    unfold Endpoint.timeout
    repeat' first
      | (solve | exact rejected_balanced _ _ _)
      | (solve | exact recoveryBlocked_balanced _ _ _)
      | (solve | exact ackBlocked_balanced _ _ _)
      | (solve | simp [FramedBalanced, Balanced, written, emitted, acknowledged, releasedPayload, Endpoint.outputState])
      | split
  | enableAck =>
    change FramedBalanced before .enableAck (Endpoint.enableAck before)
    unfold Endpoint.enableAck
    repeat' first
      | (solve | exact rejected_balanced _ _ _)
      | (solve | exact recoveryBlocked_balanced _ _ _)
      | (solve | exact ackBlocked_balanced _ _ _)
      | (solve | simp [FramedBalanced, Balanced, written, emitted, acknowledged, releasedPayload])
      | split

theorem Step.balance (step : Step) : Balanced step.before step.event step.result := by
  rw [step.computed]
  exact (evaluate_balanced step.before step.event).1


theorem Step.pending_balance (step : Step) :
    step.before.pending ++ step.written = step.emitted ++ step.result.state.pending := step.balance.1

theorem Step.sent_balance (step : Step) :
    step.before.core.sent ++ step.emitted = step.acknowledged ++ step.result.state.core.sent := step.balance.2.1

theorem Step.received_balance (step : Step) :
    step.before.core.received ++ step.releasedPayload = step.readBytes ++ step.result.state.core.received := step.balance.2.2.1

theorem Step.sendNext_balance (step : Step) :
    step.result.state.core.sendNext = step.before.core.sendNext.add step.emitted.length := step.balance.2.2.2.1

theorem Step.receiveNext_balance (step : Step) :
    step.result.state.core.receiveNext = step.before.core.receiveNext.add step.releasedPayload.length := step.balance.2.2.2.2.1

theorem Step.sendUna_balance (step : Step) :
    step.result.state.core.sendUna = step.before.core.sendUna.add step.acknowledged.length := step.balance.2.2.2.2.2


theorem Step.storage_valid (step : Step) (valid : step.before.StorageValid) : step.result.state.StorageValid := by
  rw [step.computed]
  exact evaluate_storage_valid step.before step.event valid

theorem Step.localReceiveMSS (step : Step) :
    step.result.state.localReceiveMSS = step.before.localReceiveMSS := by
  rw [step.computed]
  exact (evaluate_balanced step.before step.event).2


inductive Chain : Model → List Step → Model → Prop where
  | nil (state : Model) : Chain state [] state
  | cons (head : Step) (tail : Chain head.result.state steps final) :
      Chain head.before (head :: steps) final

namespace Chain

theorem valid (chain : Chain initial steps final) (valid : initial.Valid) : final.Valid := by
  induction chain with
  | nil state => exact valid
  | cons head tail ih => exact ih head.valid

theorem storage_valid (chain : Chain initial steps final) (valid : initial.StorageValid) : final.StorageValid := by
  induction chain with
  | nil state => exact valid
  | cons head tail ih => exact ih (head.storage_valid valid)

theorem localReceiveMSS (chain : Chain initial steps final) :
    final.localReceiveMSS = initial.localReceiveMSS := by
  induction chain with
  | nil state => rfl
  | cons head tail ih => exact ih.trans head.localReceiveMSS

theorem split (chain : Chain initial steps final) (head : Step) (member : head ∈ steps) :
    ∃ prior later, steps = prior ++ head :: later ∧ Chain initial prior head.before ∧
      Chain head.result.state later final := by
  induction chain with
  | nil state => simp at member
  | @cons steps final step tail ih =>
    rcases List.mem_cons.mp member with same | member
    · subst head
      exact ⟨[], steps, rfl, .nil step.before, tail⟩
    · obtain ⟨prior, later, same, preceding, following⟩ := ih member
      exact ⟨step :: prior, later, by simp [same], .cons step preceding, following⟩


theorem pending (chain : Chain initial steps final) :
    initial.pending ++ steps.flatMap Step.written = steps.flatMap Step.emitted ++ final.pending := by
  induction chain with
  | nil state => simp
  | cons head tail ih =>
    simp only [List.flatMap_cons]
    rw [← List.append_assoc, head.pending_balance, List.append_assoc, ih, List.append_assoc]

theorem sent (chain : Chain initial steps final) :
    initial.core.sent ++ steps.flatMap Step.emitted = steps.flatMap Step.acknowledged ++ final.core.sent := by
  induction chain with
  | nil state => simp
  | cons head tail ih =>
    simp only [List.flatMap_cons]
    rw [← List.append_assoc, head.sent_balance, List.append_assoc, ih, List.append_assoc]

theorem received (chain : Chain initial steps final) :
    initial.core.received ++ steps.flatMap Step.releasedPayload = steps.flatMap Step.readBytes ++ final.core.received := by
  induction chain with
  | nil state => simp
  | cons head tail ih =>
    simp only [List.flatMap_cons]
    rw [← List.append_assoc, head.received_balance, List.append_assoc, ih, List.append_assoc]

theorem sendNext (chain : Chain initial steps final) :
    final.core.sendNext = initial.core.sendNext.add (steps.flatMap Step.emitted).length := by
  induction chain with
  | nil state => simp
  | cons head tail ih =>
    rw [ih, head.sendNext_balance, Seq.add_add]
    simp

theorem sendUna (chain : Chain initial steps final) :
    final.core.sendUna = initial.core.sendUna.add (steps.flatMap Step.acknowledged).length := by
  induction chain with
  | nil state => simp
  | cons head tail ih =>
    rw [ih, head.sendUna_balance, Seq.add_add]
    simp

theorem receiveNext (chain : Chain initial steps final) :
    final.core.receiveNext = initial.core.receiveNext.add (steps.flatMap Step.releasedPayload).length := by
  induction chain with
  | nil state => simp
  | cons head tail ih =>
    rw [ih, head.receiveNext_balance, Seq.add_add]
    simp

theorem emitted_prefix_written (chain : Chain initial steps final) (empty : initial.pending = []) :
    steps.flatMap Step.emitted <+: steps.flatMap Step.written := by
  have balance := chain.pending
  simp only [empty, List.nil_append] at balance
  exact ⟨final.pending, balance.symm⟩

theorem read_prefix_received (chain : Chain initial steps final) (empty : initial.core.received = []) :
    steps.flatMap Step.readBytes <+: steps.flatMap Step.releasedPayload := by
  have balance := chain.received
  simp only [empty, List.nil_append] at balance
  exact ⟨final.core.received, balance.symm⟩

end Chain


namespace Chain

theorem cut (chain : Chain initial (prior ++ head :: later) final) :
    Chain initial prior head.before ∧ Chain head.result.state later final := by
  induction prior generalizing initial with
  | nil =>
    cases chain with
    | cons first tail => exact ⟨.nil head.before, tail⟩
  | cons first prior ih =>
    cases chain with
    | cons first tail =>
      obtain ⟨preceding, following⟩ := ih tail
      exact ⟨.cons first preceding, following⟩

end Chain

inductive BytePath : Input → Input → Prop where
  | direct {source target : Input} (same : target.bytes = source.bytes) : BytePath source target
  | rewrite {source target : Input} (header : Packet.Header) (ttl : UInt8)
      (transport : header.protocol = Packet.Protocol.tcp)
      (same : target.bytes = (source.rewrite header ttl transport).bytes) : BytePath source target
  | trans {source middle target : Input} (first : BytePath source middle) (second : BytePath middle target) :
      BytePath source target

theorem BytePath.fields (path : BytePath source target) :
    target.packet.segment.payload = source.packet.segment.payload ∧
      target.packet.segment.sequence = source.packet.segment.sequence := by
  induction path with
  | @direct source target same =>
    have packet : target.packet = source.packet := by
      have decoded := target.checked
      rw [same, source.checked] at decoded
      exact (Except.ok.inj decoded).symm
    simp [packet]
  | @rewrite source target header ttl transport same =>
    have packet : target.packet = (source.rewrite header ttl transport).packet := by
      have decoded := target.checked
      rw [same, (source.rewrite header ttl transport).checked] at decoded
      exact (Except.ok.inj decoded).symm
    rw [packet]
    exact ⟨rfl, rfl⟩
  | trans first second ihFirst ihSecond =>
    exact ⟨ihSecond.1.trans ihFirst.1, ihSecond.2.trans ihFirst.2⟩

def NoRetry (step : Step) : Prop := ∀ policy, step.event ≠ .timeout policy

inductive OutputOrigin (step : Step) (output : Input) : Prop where
  | send (count : Nat) (policy : Bool)
      (event : step.event = .send count policy)
      (accepted : step.result.decision = .accepted (.send count))
      (actual : step.result.output = some output) : OutputOrigin step output
  | retry (count : Nat) (policy : Bool)
      (event : step.event = .timeout policy)
      (accepted : step.result.decision = .accepted (.retry count))
      (actual : step.result.output = some output) : OutputOrigin step output
  | ack (policy : Bool)
      (event : step.event = .emitAck policy)
      (accepted : step.result.decision = .accepted .emitAck)
      (actual : step.result.output = some output) : OutputOrigin step output
  | dispatchAck (policy : Bool)
      (event : step.event = .dispatchAck policy)
      (accepted : step.result.decision = .accepted .dispatchAck)
      (actual : step.result.output = some output) : OutputOrigin step output

theorem OutputOrigin.fields (origin : OutputOrigin step output) (original : NoRetry step) :
    output.packet.segment.payload = step.emitted ∧
      output.packet.segment.sequence = step.before.core.sendNext := by
  cases origin with
  | send count policy event accepted actual =>
    have selected : (Endpoint.send step.before count policy).decision = .accepted (.send count) := by
      simpa only [step.computed, event, evaluate] using accepted
    obtain ⟨value, same, encoded, payload, sequence, _⟩ := Endpoint.send_output _ _ _ selected
    have actual' : (Endpoint.send step.before count policy).output = some output := by
      simpa only [step.computed, event, evaluate] using actual
    have equal : value = output := Option.some.inj (same.symm.trans actual')
    subst output
    exact ⟨by simpa only [Step.emitted, event, accepted, emitted] using payload, sequence⟩
  | ack policy event accepted actual =>
    have selected : (Endpoint.emitAck step.before policy).decision = .accepted .emitAck := by
      simpa only [step.computed, event, evaluate] using accepted
    obtain ⟨value, same, encoded⟩ := Endpoint.emitAck_output _ _ selected
    have actual' : (Endpoint.emitAck step.before policy).output = some output := by
      simpa only [step.computed, event, evaluate] using actual
    have equal : value = output := Option.some.inj (same.symm.trans actual')
    subst output
    exact ⟨by simpa only [Step.emitted, event, emitted] using Endpoint.emit_payload _ _ _ encoded,
      (Endpoint.emit_transport _ _ _ encoded).2.1⟩
  | dispatchAck policy event accepted actual =>
    have selected : (Endpoint.dispatchAck step.before policy).decision = .accepted .dispatchAck := by
      simpa only [step.computed, event, evaluate] using accepted
    obtain ⟨value, same, encoded⟩ := Endpoint.dispatchAck_output _ _ selected
    have actual' : (Endpoint.dispatchAck step.before policy).output = some output := by
      simpa only [step.computed, event, evaluate] using actual
    have equal : value = output := Option.some.inj (same.symm.trans actual')
    subst output
    exact ⟨by simpa only [Step.emitted, event, emitted] using Endpoint.emit_payload _ _ _ encoded,
      (Endpoint.emit_transport _ _ _ encoded).2.1⟩
  | retry count policy event accepted actual => exact False.elim (original policy event)

theorem OutputOrigin.actual (origin : OutputOrigin step output) : step.result.output = some output := by
  cases origin <;> assumption

theorem OutputOrigin.ack_fields (origin : OutputOrigin step output) :
    output.packet.segment.acknowledgment = step.before.core.receiveNext ∧
      output.packet.segment.window.val = Endpoint.outputWindow step.before := by
  cases origin with
  | send count policy event accepted actual =>
    have selected : (Endpoint.send step.before count policy).decision = .accepted (.send count) := by
      simpa only [step.computed, event, evaluate] using accepted
    obtain ⟨value, same, encoded, _, _, _⟩ := Endpoint.send_output _ _ _ selected
    have actual' : (Endpoint.send step.before count policy).output = some output := by
      simpa only [step.computed, event, evaluate] using actual
    have equal : value = output := Option.some.inj (same.symm.trans actual')
    subst output
    exact ⟨(Endpoint.emit_transport _ _ _ encoded).2.2.1, (Endpoint.emit_transport _ _ _ encoded).2.2.2.1⟩
  | ack policy event accepted actual =>
    have selected : (Endpoint.emitAck step.before policy).decision = .accepted (.emitAck) := by
      simpa only [step.computed, event, evaluate] using accepted
    obtain ⟨value, same, encoded⟩ := Endpoint.emitAck_output _ _ selected
    have actual' : (Endpoint.emitAck step.before policy).output = some output := by
      simpa only [step.computed, event, evaluate] using actual
    have equal : value = output := Option.some.inj (same.symm.trans actual')
    subst output
    exact ⟨(Endpoint.emit_transport _ _ _ encoded).2.2.1, (Endpoint.emit_transport _ _ _ encoded).2.2.2.1⟩
  | dispatchAck policy event accepted actual =>
    have selected : (Endpoint.dispatchAck step.before policy).decision = .accepted (.dispatchAck) := by
      simpa only [step.computed, event, evaluate] using accepted
    obtain ⟨value, same, encoded⟩ := Endpoint.dispatchAck_output _ _ selected
    have actual' : (Endpoint.dispatchAck step.before policy).output = some output := by
      simpa only [step.computed, event, evaluate] using actual
    have equal : value = output := Option.some.inj (same.symm.trans actual')
    subst output
    exact ⟨(Endpoint.emit_transport _ _ _ encoded).2.2.1, (Endpoint.emit_transport _ _ _ encoded).2.2.2.1⟩
  | retry count policy event accepted actual =>
    have selected : (Endpoint.timeout step.before policy).decision = .accepted (.retry count) := by
      simpa only [step.computed, event, evaluate] using accepted
    obtain ⟨_, _, value, _, _, _, same, encoded, _, _, _⟩ := Endpoint.timeout_output _ _ _ selected
    have actual' : (Endpoint.timeout step.before policy).output = some output := by
      simpa only [step.computed, event, evaluate] using actual
    have equal : value = output := Option.some.inj (same.symm.trans actual')
    subst output
    exact ⟨(Endpoint.emitAt_transport _ _ _ _ encoded).2.2.1, (Endpoint.emitAt_transport _ _ _ _ encoded).2.2.2.1⟩


theorem OutputOrigin.ack_coherent (origin : OutputOrigin step output) : Endpoint.AckCoherent step.before := by
  apply Endpoint.ackReady_coherent
  cases origin with
  | send count policy event accepted actual =>
    apply Endpoint.send_ackReady step.before count policy
    simpa only [step.computed, event, evaluate] using accepted
  | retry count policy event accepted actual =>
    apply Endpoint.timeout_ackReady step.before policy count
    simpa only [step.computed, event, evaluate] using accepted
  | ack policy event accepted actual =>
    apply Endpoint.pureAck_ackReady step.before policy false .emitAck
    simpa only [step.computed, event, evaluate, Endpoint.emitAck] using accepted
  | dispatchAck policy event accepted actual =>
    apply Endpoint.pureAck_ackReady step.before policy true .dispatchAck
    simpa only [step.computed, event, evaluate, Endpoint.dispatchAck] using accepted

theorem OutputOrigin.ack_state (origin : OutputOrigin step output) :
    step.result.state.ackReaction = step.before.ackReaction.map (fun reaction =>
      AckReaction.outputState reaction step.before.now step.before.core.receiveNext
        step.before.core.capacity step.before.core.window step.before.effectiveMSS) := by
  cases origin with
  | send count policy event accepted actual =>
    have selected : (Endpoint.send step.before count policy).decision = .accepted (.send count) := by
      simpa only [step.computed, event, evaluate] using accepted
    obtain ⟨_, _, _, _, _, changed⟩ := Endpoint.send_accepted step.before count policy selected
    simp only [step.computed, event, evaluate, changed]
    rfl
  | retry count policy event accepted actual =>
    have selected : (Endpoint.timeout step.before policy).decision = .accepted (.retry count) := by
      simpa only [step.computed, event, evaluate] using accepted
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, changed⟩ := Endpoint.timeout_accepted step.before policy count selected
    simp only [step.computed, event, evaluate, changed]
    rfl
  | ack policy event accepted actual =>
    have selected : (Endpoint.pureAck step.before policy false).decision = .accepted .emitAck := by
      simpa only [step.computed, event, evaluate, Endpoint.emitAck] using accepted
    have changed := Endpoint.pureAck_state step.before policy false .emitAck selected
    simp only [step.computed, event, evaluate, Endpoint.emitAck, changed]
    rfl
  | dispatchAck policy event accepted actual =>
    have selected : (Endpoint.pureAck step.before policy true).decision = .accepted .dispatchAck := by
      simpa only [step.computed, event, evaluate, Endpoint.dispatchAck] using accepted
    have changed := Endpoint.pureAck_state step.before policy true .dispatchAck selected
    simp only [step.computed, event, evaluate, Endpoint.dispatchAck, changed]
    rfl


structure OutputAt (steps : List Step) where
  prior : List Step
  step : Step
  later : List Step
  same : steps = prior ++ step :: later
  output : Input
  origin : OutputOrigin step output

namespace OutputAt

theorem member (value : OutputAt steps) : value.step ∈ steps := by
  have member : value.step ∈ value.prior ++ value.step :: value.later := by simp
  exact Eq.mp (congrArg (fun list => value.step ∈ list) value.same.symm) member

theorem emitted_prefix (value : OutputAt steps) (original : NoRetry value.step) :
    value.prior.flatMap Step.emitted ++ value.output.packet.segment.payload <+: steps.flatMap Step.emitted := by
  rw [(value.origin.fields original).1]
  have all := congrArg (List.flatMap Step.emitted) value.same
  simp only [List.flatMap_append, List.flatMap_cons] at all
  rw [all]
  exact ⟨value.later.flatMap Step.emitted, List.append_assoc _ _ _⟩

theorem coordinate (value : OutputAt steps) (chain : Chain initial steps final) (original : NoRetry value.step) :
    value.output.packet.segment.sequence = initial.core.sendNext.add (value.prior.flatMap Step.emitted).length := by
  rw [(value.origin.fields original).2]
  have split := chain
  rw [value.same] at split
  exact split.cut.1.sendNext

theorem scope_prefix (value : OutputAt steps) :
    (value.prior ++ [value.step]).flatMap Step.emitted <+: steps.flatMap Step.emitted := by
  have all := congrArg (List.flatMap Step.emitted) value.same
  exact ⟨value.later.flatMap Step.emitted, by simpa only [List.flatMap_append, List.flatMap_cons,
    List.flatMap_singleton, List.flatMap_nil, List.nil_append, List.append_assoc] using all.symm⟩

theorem range (value : OutputAt steps) (chain : Chain initial steps final) (emptySent : initial.core.sent = []) :
    ∃ prefixBytes : List UInt8,
      prefixBytes ++ value.output.packet.segment.payload <+: (value.prior ++ [value.step]).flatMap Step.emitted ∧
      value.output.packet.segment.sequence = initial.core.sendNext.add prefixBytes.length := by
  have split := chain
  rw [value.same] at split
  have prior := split.cut.1
  cases origin : value.origin with
  | send count policy event accepted actual =>
    have original : NoRetry value.step := by intro other same; rw [event] at same; cases same
    refine ⟨value.prior.flatMap Step.emitted, ?_, value.coordinate chain original⟩
    rw [(value.origin.fields original).1]
    exact ⟨[], by simp⟩
  | ack policy event accepted actual =>
    have original : NoRetry value.step := by intro other same; rw [event] at same; cases same
    refine ⟨value.prior.flatMap Step.emitted, ?_, value.coordinate chain original⟩
    rw [(value.origin.fields original).1]
    exact ⟨[], by simp⟩
  | dispatchAck policy event accepted actual =>
    have original : NoRetry value.step := by intro other same; rw [event] at same; cases same
    refine ⟨value.prior.flatMap Step.emitted, ?_, value.coordinate chain original⟩
    rw [(value.origin.fields original).1]
    exact ⟨[], by simp⟩
  | retry count policy event accepted actual =>
    have selected : (Endpoint.timeout value.step.before policy).decision = .accepted (.retry count) := by
      simpa only [value.step.computed, event, evaluate] using accepted
    obtain ⟨recovery, after, output, _, timed, changed, produced, encoded, payload, sequence, bound⟩ :=
      Endpoint.timeout_output _ _ _ selected
    have same : output = value.output := by
      have emitted : (Endpoint.timeout value.step.before policy).output = some value.output := by
        simpa only [value.step.computed, event, evaluate] using actual
      exact Option.some.inj (produced.symm.trans emitted)
    subst output
    have balance := prior.sent
    simp only [emptySent, List.nil_append] at balance
    have emitted : value.step.emitted = [] := by simp [Step.emitted, ApplicationTrace.emitted, event]
    have initialValid : initial.Valid := by
      have member := value.member
      cases chain with
      | nil state => simp at member
      | cons head tail => exact head.beforeValid
    have initialCursor := initialValid.1.2.2.2.2.1
    simp only [emptySent, List.length_nil, Seq.add_zero] at initialCursor
    refine ⟨value.prior.flatMap Step.acknowledged, ?_, ?_⟩
    · rw [payload]
      refine ⟨value.step.before.core.sent.drop count, ?_⟩
      rw [List.append_assoc, List.take_append_drop, ← balance]
      simp [emitted]
    · rw [sequence, prior.sendUna, initialCursor]

end OutputAt

def Chronological (steps : List Step) : Prop :=
  steps.Pairwise (fun first second => first.stamp < second.stamp)

structure DeliveryHistory (sender receiver : List Step) : Prop where
  senderOrder : Chronological sender
  receiverOrder : Chronological receiver
  delivered : ∀ step ∈ receiver, ∀ input, step.event = .receive input →
    ∃ source : OutputAt sender, source.step.stamp < step.stamp ∧ BytePath source.output input

theorem Step.data (step : Step) (nonempty : step.acceptedPayload ≠ []) :
    ∃ input count size, step.event = .receive input ∧
      step.result.decision = .accepted (.receive count size) ∧
      step.acceptedPayload = input.packet.segment.payload := by
  cases event : step.event with
  | write bytes | send bytes _ | read bytes | emitAck bytes | advanceClock bytes | timeout bytes | dispatchAck bytes =>
    simp [Step.acceptedPayload, ApplicationTrace.acceptedPayload, event] at nonempty
  | enableRecovery | enableAck => simp [Step.acceptedPayload, ApplicationTrace.acceptedPayload, event] at nonempty
  | receive input =>
    cases selected : step.result.decision with
    | reject reason | unsupported reason | recoveryUnsupported reason | ackUnsupported reason =>
      simp [Step.acceptedPayload, ApplicationTrace.acceptedPayload, event, selected] at nonempty
    | accepted action =>
      cases action with
      | receive count size => exact ⟨input, count, size, rfl, rfl, by simp only [Step.acceptedPayload, ApplicationTrace.acceptedPayload, event, selected]⟩
      | write _ | send _ | read _ | emitAck | enableRecovery | advanceClock | retry _ | enableAck | dispatchAck =>
        simp [Step.acceptedPayload, ApplicationTrace.acceptedPayload, event, selected] at nonempty


def Delivered (sender : List Step) (step : Step) : Prop :=
  ∀ input, step.event = .receive input →
    ∃ source : OutputAt sender, source.step.stamp < step.stamp ∧ BytePath source.output input


end Netlib.Protocol.TCP.ApplicationTrace
