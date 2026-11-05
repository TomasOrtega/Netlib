import Netlib.Protocol.TCP.Endpoint

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

def evaluate (before : Model) : Event → Endpoint.Result
  | .write bytes => Endpoint.write before bytes
  | .send count policy => Endpoint.send before count policy
  | .read count => Endpoint.read before count
  | .emitAck policy => Endpoint.emitAck before policy
  | .receive input => Endpoint.receive before input

theorem evaluate_valid (before : Model) (valid : before.Valid) (event : Event) :
    (evaluate before event).state.Valid := by
  cases event with
  | write bytes => exact Endpoint.write_valid before bytes valid
  | send count policy => exact Endpoint.send_valid before count policy valid
  | read count => exact Endpoint.read_valid before count valid
  | emitAck policy => exact Endpoint.emitAck_valid before policy valid
  | receive input => exact Endpoint.receive_valid before input valid

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
  | .unsupported _ => false
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

def Step.written (step : Step) : List UInt8 := ApplicationTrace.written step.event step.result

def Step.emitted (step : Step) : List UInt8 := ApplicationTrace.emitted step.before step.event step.result

def Step.acknowledged (step : Step) : List UInt8 := ApplicationTrace.acknowledged step.before step.event step.result

def Step.acceptedPayload (step : Step) : List UInt8 := ApplicationTrace.acceptedPayload step.event step.result

def Step.readBytes (step : Step) : List UInt8 := step.result.read

def Balanced (before : Model) (event : Event) (result : Endpoint.Result) : Prop :=
  before.pending ++ written event result = emitted before event result ++ result.state.pending ∧
  before.core.sent ++ emitted before event result = acknowledged before event result ++ result.state.core.sent ∧
  before.core.received ++ acceptedPayload event result = result.read ++ result.state.core.received ∧
  result.state.core.sendNext = before.core.sendNext.add (emitted before event result).length ∧
  result.state.core.receiveNext = before.core.receiveNext.add (acceptedPayload event result).length

private theorem rejected_balanced (before : Model) (event : Event) (reason : Endpoint.Reject) :
    Balanced before event (Endpoint.rejected before reason) := by
  cases event <;> simp [Balanced, Endpoint.rejected, written, emitted, acknowledged, acceptedPayload]

private theorem evaluate_balanced (before : Model) (event : Event) :
    Balanced before event (evaluate before event) := by
  cases event with
  | write bytes =>
    change Balanced before (.write bytes) (Endpoint.write before bytes)
    unfold Endpoint.write
    split
    · exact rejected_balanced _ _ _
    · split
      · exact rejected_balanced _ _ _
      · simp [Balanced, written, emitted, acknowledged, acceptedPayload, Endpoint.writeState]
  | read count =>
    change Balanced before (.read count) (Endpoint.read before count)
    unfold Endpoint.read
    split
    · exact rejected_balanced _ _ _
    · split
      · exact rejected_balanced _ _ _
      · simp [Balanced, written, emitted, acknowledged, acceptedPayload, Endpoint.readState]
  | send count policy =>
    change Balanced before (.send count policy) (Endpoint.send before count policy)
    unfold Endpoint.send
    split
    · exact rejected_balanced _ _ _
    · split
      · exact rejected_balanced _ _ _
      · split
        · exact rejected_balanced _ _ _
        · rename_i ready
          cases encoded : Output.emit before.core (before.pending.take count) with
          | error reason => exact rejected_balanced _ _ _
          | ok output =>
            have bounded := (Decidable.not_not.mp ready).2.1
            have size : (before.pending.take count).length = count := by simp [List.length_take, Nat.min_eq_left bounded]
            simp [Balanced, written, emitted, acknowledged, acceptedPayload, Endpoint.sendState, size]
  | emitAck policy =>
    change Balanced before (.emitAck policy) (Endpoint.emitAck before policy)
    unfold Endpoint.emitAck
    split
    · exact rejected_balanced _ _ _
    · split
      · exact rejected_balanced _ _ _
      · cases Output.emit before.core [] <;>
          simp [Balanced, written, emitted, acknowledged, acceptedPayload, Endpoint.rejected]
  | receive input =>
    change Balanced before (.receive input) (Endpoint.receive before input)
    unfold Endpoint.receive
    split
    · exact rejected_balanced _ _ _
    · cases selected : (EstablishedReceive.receive before.core input).decision with
      | blocked reason =>
        cases reason <;> simp [selected, Balanced, written, emitted, acknowledged, acceptedPayload]
      | accepted count size =>
        have changed := EstablishedReceive.receive_accepted before.core input count size selected
        obtain ⟨_, bound, _, fits, after⟩ := changed
        simp only [selected, Balanced, written, emitted, acknowledged, acceptedPayload, Endpoint.receiveState, Endpoint.windowState, after]
        split <;>
          simp [EstablishedReceive.commit]

theorem Step.balance (step : Step) : Balanced step.before step.event step.result := by
  rw [step.computed]
  exact evaluate_balanced step.before step.event


theorem Step.pending_balance (step : Step) :
    step.before.pending ++ step.written = step.emitted ++ step.result.state.pending := step.balance.1

theorem Step.sent_balance (step : Step) :
    step.before.core.sent ++ step.emitted = step.acknowledged ++ step.result.state.core.sent := step.balance.2.1

theorem Step.received_balance (step : Step) :
    step.before.core.received ++ step.acceptedPayload = step.readBytes ++ step.result.state.core.received := step.balance.2.2.1

theorem Step.sendNext_balance (step : Step) :
    step.result.state.core.sendNext = step.before.core.sendNext.add step.emitted.length := step.balance.2.2.2.1

theorem Step.receiveNext_balance (step : Step) :
    step.result.state.core.receiveNext = step.before.core.receiveNext.add step.acceptedPayload.length := step.balance.2.2.2.2


inductive Chain : Model → List Step → Model → Prop where
  | nil (state : Model) : Chain state [] state
  | cons (head : Step) (tail : Chain head.result.state steps final) :
      Chain head.before (head :: steps) final

namespace Chain

theorem valid (chain : Chain initial steps final) (valid : initial.Valid) : final.Valid := by
  induction chain with
  | nil state => exact valid
  | cons head tail ih => exact ih head.valid

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
    initial.core.received ++ steps.flatMap Step.acceptedPayload = steps.flatMap Step.readBytes ++ final.core.received := by
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

theorem receiveNext (chain : Chain initial steps final) :
    final.core.receiveNext = initial.core.receiveNext.add (steps.flatMap Step.acceptedPayload).length := by
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
    steps.flatMap Step.readBytes <+: steps.flatMap Step.acceptedPayload := by
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

inductive OutputOrigin (step : Step) (output : Input) : Prop where
  | send (count : Nat) (policy : Bool)
      (event : step.event = .send count policy)
      (accepted : step.result.decision = .accepted (.send count))
      (actual : step.result.output = some output) : OutputOrigin step output
  | ack (policy : Bool)
      (event : step.event = .emitAck policy)
      (accepted : step.result.decision = .accepted .emitAck)
      (actual : step.result.output = some output) : OutputOrigin step output

theorem OutputOrigin.fields (origin : OutputOrigin step output) :
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
    exact ⟨by simpa only [Step.emitted, event, emitted] using Output.emit_payload _ _ _ encoded,
      (Output.emit_transport _ _ _ encoded).2.1⟩

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

theorem emitted_prefix (value : OutputAt steps) :
    value.prior.flatMap Step.emitted ++ value.output.packet.segment.payload <+: steps.flatMap Step.emitted := by
  rw [value.origin.fields.1]
  have all := congrArg (List.flatMap Step.emitted) value.same
  simp only [List.flatMap_append, List.flatMap_cons] at all
  rw [all]
  exact ⟨value.later.flatMap Step.emitted, List.append_assoc _ _ _⟩

theorem coordinate (value : OutputAt steps) (chain : Chain initial steps final) :
    value.output.packet.segment.sequence = initial.core.sendNext.add (value.prior.flatMap Step.emitted).length := by
  rw [value.origin.fields.2]
  have split := chain
  rw [value.same] at split
  exact split.cut.1.sendNext

end OutputAt

def Chronological (steps : List Step) : Prop :=
  steps.Pairwise (fun first second => first.stamp < second.stamp)

structure DeliveryHistory (sender receiver : List Step) : Prop where
  senderOrder : Chronological sender
  receiverOrder : Chronological receiver
  delivered : ∀ step ∈ receiver, ∀ input, step.event = .receive input →
    ∃ source : OutputAt sender, source.step.stamp < step.stamp ∧ BytePath source.output input

private theorem Step.data (step : Step) (nonempty : step.acceptedPayload ≠ []) :
    ∃ input count size, step.event = .receive input ∧
      step.result.decision = .accepted (.receive count size) ∧
      step.acceptedPayload = input.packet.segment.payload ∧
      input.packet.segment.sequence = step.before.core.receiveNext := by
  cases event : step.event with
  | write bytes => simp [Step.acceptedPayload, ApplicationTrace.acceptedPayload, event] at nonempty
  | send count policy => simp [Step.acceptedPayload, ApplicationTrace.acceptedPayload, event] at nonempty
  | read count => simp [Step.acceptedPayload, ApplicationTrace.acceptedPayload, event] at nonempty
  | emitAck policy => simp [Step.acceptedPayload, ApplicationTrace.acceptedPayload, event] at nonempty
  | receive input =>
    cases selected : step.result.decision with
    | reject reason => simp [Step.acceptedPayload, ApplicationTrace.acceptedPayload, event, selected] at nonempty
    | unsupported reason => simp [Step.acceptedPayload, ApplicationTrace.acceptedPayload, event, selected] at nonempty
    | accepted action =>
      cases action with
      | write count => simp [Step.acceptedPayload, ApplicationTrace.acceptedPayload, event, selected] at nonempty
      | send count => simp [Step.acceptedPayload, ApplicationTrace.acceptedPayload, event, selected] at nonempty
      | read count => simp [Step.acceptedPayload, ApplicationTrace.acceptedPayload, event, selected] at nonempty
      | emitAck => simp [Step.acceptedPayload, ApplicationTrace.acceptedPayload, event, selected] at nonempty
      | receive count size =>
        have accepted : (Endpoint.receive step.before input).decision = .accepted (.receive count size) := by
          simpa only [step.computed, event, evaluate] using selected
        have nonempty' : input.packet.segment.payload ≠ [] := by
          simpa only [Step.acceptedPayload, ApplicationTrace.acceptedPayload, event, selected] using nonempty
        exact ⟨input, count, size, rfl, rfl,
          by simp only [Step.acceptedPayload, ApplicationTrace.acceptedPayload, event, selected],
          Endpoint.receive_in_order _ _ _ _ accepted nonempty'⟩


def Delivered (sender : List Step) (step : Step) : Prop :=
  ∀ input, step.event = .receive input →
    ∃ source : OutputAt sender, source.step.stamp < step.stamp ∧ BytePath source.output input

private theorem extend_prefix (sourceChain : Chain sourceInitial sourceSteps sourceFinal)
    (epoch : (sourceSteps.flatMap Step.emitted).length < Seq.halfSpace)
    (step : Step) (accumulated : List UInt8)
    (priorPrefix : accumulated <+: sourceSteps.flatMap Step.emitted)
    (cursor : step.before.core.receiveNext = sourceInitial.core.sendNext.add accumulated.length)
    (delivered : Delivered sourceSteps step) :
    accumulated ++ step.acceptedPayload <+: sourceSteps.flatMap Step.emitted := by
  by_cases empty : step.acceptedPayload = []
  · simpa only [empty, List.append_nil] using priorPrefix
  · obtain ⟨input, count, size, event, _, payload, inOrder⟩ := step.data empty
    obtain ⟨source, _, path⟩ := delivered input event
    have sourcePrefix : source.prior.flatMap Step.emitted <+: sourceSteps.flatMap Step.emitted :=
      (List.prefix_append _ _).trans source.emitted_prefix
    have accumulatedBound : accumulated.length < Seq.modulus := by
      have bound := priorPrefix.length_le
      unfold Seq.modulus Seq.halfSpace at *
      omega
    have sourceBound : (source.prior.flatMap Step.emitted).length < Seq.modulus := by
      have bound := sourcePrefix.length_le
      unfold Seq.modulus Seq.halfSpace at *
      omega
    have sameSequence : sourceInitial.core.sendNext.add accumulated.length =
        sourceInitial.core.sendNext.add (source.prior.flatMap Step.emitted).length := by
      calc
        _ = step.before.core.receiveNext := cursor.symm
        _ = input.packet.segment.sequence := inOrder.symm
        _ = source.output.packet.segment.sequence := path.fields.2
        _ = _ := source.coordinate sourceChain
    have sameLength := congrArg (Seq.distance sourceInitial.core.sendNext) sameSequence
    simp only [Seq.distance_add, Nat.mod_eq_of_lt accumulatedBound, Nat.mod_eq_of_lt sourceBound] at sameLength
    have sameBytes : accumulated = source.prior.flatMap Step.emitted :=
      (List.prefix_of_prefix_length_le priorPrefix sourcePrefix (Nat.le_of_eq sameLength)).eq_of_length sameLength
    rw [sameBytes, payload, path.fields.1]
    exact source.emitted_prefix

private theorem accepted_prefix_aux (sourceChain : Chain sourceInitial sourceSteps sourceFinal)
    (epoch : (sourceSteps.flatMap Step.emitted).length < Seq.halfSpace)
    (targetChain : Chain targetInitial targetSteps targetFinal) :
    ∀ accumulated : List UInt8,
      accumulated <+: sourceSteps.flatMap Step.emitted →
      targetInitial.core.receiveNext = sourceInitial.core.sendNext.add accumulated.length →
      (∀ step ∈ targetSteps, Delivered sourceSteps step) →
      accumulated ++ targetSteps.flatMap Step.acceptedPayload <+: sourceSteps.flatMap Step.emitted := by
  induction targetChain with
  | nil state => intro accumulated priorPrefix _ _; simpa using priorPrefix
  | cons head tail ih =>
    intro accumulated priorPrefix cursor delivered
    have added := extend_prefix sourceChain epoch head accumulated priorPrefix cursor (delivered head (by simp))
    have nextCursor : head.result.state.core.receiveNext =
        sourceInitial.core.sendNext.add (accumulated ++ head.acceptedPayload).length := by
      rw [head.receiveNext_balance, cursor, Seq.add_add, List.length_append]
    have rest := ih (accumulated ++ head.acceptedPayload) added nextCursor
      (fun step member => delivered step (by simp [member]))
    simpa only [List.flatMap_cons, List.append_assoc] using rest

theorem accepted_prefix_emitted (sourceChain : Chain sourceInitial sourceSteps sourceFinal)
    (targetChain : Chain targetInitial targetSteps targetFinal)
    (history : DeliveryHistory sourceSteps targetSteps)
    (cursors : targetInitial.core.receiveNext = sourceInitial.core.sendNext)
    (epoch : (sourceSteps.flatMap Step.emitted).length < Seq.halfSpace) :
    targetSteps.flatMap Step.acceptedPayload <+: sourceSteps.flatMap Step.emitted := by
  have result := accepted_prefix_aux sourceChain epoch targetChain [] (by simp)
    (by simpa using cursors) history.delivered
  simpa only [List.nil_append] using result

theorem application_prefix (sourceChain : Chain sourceInitial sourceSteps sourceFinal)
    (targetChain : Chain targetInitial targetSteps targetFinal)
    (history : DeliveryHistory sourceSteps targetSteps)
    (emptyPending : sourceInitial.pending = [])
    (emptyReceived : targetInitial.core.received = [])
    (cursors : targetInitial.core.receiveNext = sourceInitial.core.sendNext)
    (epoch : (sourceSteps.flatMap Step.emitted).length < Seq.halfSpace) :
    targetSteps.flatMap Step.readBytes <+: sourceSteps.flatMap Step.written := by
  exact (targetChain.read_prefix_received emptyReceived).trans
    ((accepted_prefix_emitted sourceChain targetChain history cursors epoch).trans
      (sourceChain.emitted_prefix_written emptyPending))


theorem OutputOrigin.pending_prefix (origin : OutputOrigin step output) :
    output.packet.segment.payload <+: step.before.pending := by
  rw [origin.fields.1]
  cases origin with
  | send count policy event accepted actual =>
    simpa only [Step.emitted, event, accepted, emitted] using List.take_prefix count step.before.pending
  | ack policy event accepted actual =>
    simp only [Step.emitted, event, emitted, List.nil_prefix]

theorem OutputOrigin.nonempty_send (origin : OutputOrigin step output)
    (nonempty : output.packet.segment.payload ≠ []) :
    ∃ count policy, step.event = .send count policy ∧ step.result.decision = .accepted (.send count) := by
  cases origin with
  | send count policy event accepted actual => exact ⟨count, policy, event, accepted⟩
  | ack policy event accepted actual =>
    have payload := (OutputOrigin.ack policy event accepted actual).fields.1
    simp only [Step.emitted, event, emitted] at payload
    exact False.elim (nonempty payload)

theorem OutputAt.written_prefix (value : OutputAt steps) (chain : Chain initial steps final)
    (empty : initial.pending = []) :
    value.prior.flatMap Step.emitted ++ value.output.packet.segment.payload <+: value.prior.flatMap Step.written := by
  have split := chain
  rw [value.same] at split
  have balance := split.cut.1.pending
  simp only [empty, List.nil_append] at balance
  obtain ⟨remaining, same⟩ := value.origin.pending_prefix
  exact ⟨remaining, by rw [List.append_assoc, same, ← balance]⟩

theorem OutputAt.prior_before (value : OutputAt steps) (order : Chronological steps)
    (writer : Step) (member : writer ∈ value.prior) : writer.stamp < value.step.stamp := by
  have ordered := order
  unfold Chronological at ordered
  rw [value.same] at ordered
  exact (List.pairwise_append.mp ordered).2.2 writer member value.step (by simp)

theorem OutputAt.byte_write (value : OutputAt steps) (chain : Chain initial steps final)
    (empty : initial.pending = []) (order : Chronological steps)
    (byte : UInt8) (member : byte ∈ value.output.packet.segment.payload) :
    ∃ writer ∈ value.prior, writer.stamp < value.step.stamp ∧ byte ∈ writer.written := by
  have priorMember : byte ∈ value.prior.flatMap Step.written :=
    (value.written_prefix chain empty).subset (List.mem_append_right _ member)
  obtain ⟨writer, before, present⟩ := List.mem_flatMap.mp priorMember
  exact ⟨writer, before, value.prior_before order writer before, present⟩

theorem Step.written_event (step : Step) (byte : UInt8) (member : byte ∈ step.written) :
    ∃ bytes count, step.event = .write bytes ∧
      step.result.decision = .accepted (.write count) ∧ byte ∈ bytes := by
  cases event : step.event with
  | send count policy => simp [Step.written, ApplicationTrace.written, event] at member
  | read count => simp [Step.written, ApplicationTrace.written, event] at member
  | emitAck policy => simp [Step.written, ApplicationTrace.written, event] at member
  | receive input => simp [Step.written, ApplicationTrace.written, event] at member
  | write bytes =>
    cases selected : step.result.decision with
    | reject reason => simp [Step.written, ApplicationTrace.written, event, selected] at member
    | unsupported reason => simp [Step.written, ApplicationTrace.written, event, selected] at member
    | accepted action =>
      cases action with
      | write count =>
        exact ⟨bytes, count, rfl, rfl, by
          simpa only [Step.written, ApplicationTrace.written, event, selected] using member⟩
      | send count => simp [Step.written, ApplicationTrace.written, event, selected] at member
      | read count => simp [Step.written, ApplicationTrace.written, event, selected] at member
      | emitAck => simp [Step.written, ApplicationTrace.written, event, selected] at member
      | receive count size => simp [Step.written, ApplicationTrace.written, event, selected] at member

theorem received_byte_origin (sourceChain : Chain sourceInitial sourceSteps sourceFinal)
    (history : DeliveryHistory sourceSteps targetSteps) (empty : sourceInitial.pending = [])
    (step : Step) (member : step ∈ targetSteps)
    (byte : UInt8) (present : byte ∈ step.acceptedPayload) :
    ∃ input count size, step.event = .receive input ∧
      step.result.decision = .accepted (.receive count size) ∧
      ∃ source : OutputAt sourceSteps,
        BytePath source.output input ∧ source.step.stamp < step.stamp ∧
        (∃ sent policy, source.step.event = .send sent policy ∧
          source.step.result.decision = .accepted (.send sent)) ∧
        ∃ writer ∈ source.prior,
          writer.stamp < source.step.stamp ∧
          ∃ bytes writtenCount, writer.event = .write bytes ∧
            writer.result.decision = .accepted (.write writtenCount) ∧ byte ∈ bytes := by
  have nonempty : step.acceptedPayload ≠ [] := by intro empty; simp [empty] at present
  obtain ⟨input, count, size, event, accepted, payload, _⟩ := step.data nonempty
  obtain ⟨source, earlier, path⟩ := history.delivered step member input event
  have sourceMember : byte ∈ source.output.packet.segment.payload := by
    rw [payload, path.fields.1] at present
    exact present
  have sourceNonempty : source.output.packet.segment.payload ≠ [] := by
    intro empty
    simp [empty] at sourceMember
  obtain ⟨writer, prior, before, writtenMember⟩ :=
    source.byte_write sourceChain empty history.senderOrder byte sourceMember
  exact ⟨input, count, size, event, accepted, source, path, earlier,
    source.origin.nonempty_send sourceNonempty, writer, prior, before,
    writer.written_event byte writtenMember⟩

theorem paired_application_prefix
    (leftChain : Chain leftInitial leftSteps leftFinal)
    (rightChain : Chain rightInitial rightSteps rightFinal)
    (leftToRight : DeliveryHistory leftSteps rightSteps)
    (rightToLeft : DeliveryHistory rightSteps leftSteps)
    (leftPending : leftInitial.pending = []) (rightPending : rightInitial.pending = [])
    (leftReceived : leftInitial.core.received = []) (rightReceived : rightInitial.core.received = [])
    (leftCursor : leftInitial.core.receiveNext = rightInitial.core.sendNext)
    (rightCursor : rightInitial.core.receiveNext = leftInitial.core.sendNext)
    (leftEpoch : (leftSteps.flatMap Step.emitted).length < Seq.halfSpace)
    (rightEpoch : (rightSteps.flatMap Step.emitted).length < Seq.halfSpace) :
    rightSteps.flatMap Step.readBytes <+: leftSteps.flatMap Step.written ∧
      leftSteps.flatMap Step.readBytes <+: rightSteps.flatMap Step.written := by
  exact ⟨application_prefix leftChain rightChain leftToRight leftPending rightReceived rightCursor leftEpoch,
    application_prefix rightChain leftChain rightToLeft rightPending leftReceived leftCursor rightEpoch⟩

end Netlib.Protocol.TCP.ApplicationTrace
