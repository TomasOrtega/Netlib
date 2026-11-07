import Netlib.Protocol.TCP.ApplicationTraceFacts
import Netlib.Protocol.TCP.AckReaction

/-!
# Actual ACK causes and timed output on one endpoint chain

The checker projects actual endpoint operations into the timed reaction history.
Each cause retains its actual issuer. Each discharge retains its exact packet output.
The endpoint chain supplies the local clock context. Separate chains keep separate clocks.
-/

namespace Netlib.Protocol.TCP.AckTrace

namespace T
export Netlib.Theory.TimedReaction (Adapter CheckedStep History CausalWitness State initial observe)
end T
namespace A
export ApplicationTrace (Step Event Chain OutputAt Chronological)
end A

def work (state : Endpoint.State) : AckReaction.Work :=
  (state.ackReaction.map (·.work)).getD (T.initial ())

def receiveRequest (before : Endpoint.State) (result : Endpoint.Result) (immediate : Bool := false) : Option (AckReaction.Demand × Nat) :=
  match before.ackReaction, result.state.ackReaction, result.ack with
  | some previous, some next, some request =>
    match request.kind, result.decision with
    | .data, .accepted (.receive _ size) =>
      let delay := if immediate || decide (2 ≤ next.fullSegments ∨ 2 * previous.rmss ≤ next.dataBytes) then 0 else 499
      some (⟨.data, result.state.core.receiveNext, next.advertisement.frontier, size, 0⟩, delay)
    | .sequence, .reject (.input .sequence) =>
      some (AckReaction.demand previous .sequence before.core.receiveNext 0 0, 0)
    | _, _ => none
  | _, _, _ => none

def readRequest (before : Endpoint.State) (result : Endpoint.Result) : Option (AckReaction.Demand × Nat) :=
  match before.ackReaction, result.decision with
  | some previous, .accepted (.read _) =>
    let old := AckReaction.candidate previous before.core.capacity before.core.window before.effectiveMSS
    let next := AckReaction.candidate previous before.core.capacity result.state.core.window before.effectiveMSS
    if old < next then
      some (AckReaction.demand previous .window before.core.receiveNext 0 (previous.advertisement.frontier + next), 0)
    else none
  | _, _ => none

def request (before : Endpoint.State) (event : A.Event) (result : Endpoint.Result) : Option (AckReaction.Demand × Nat) :=
  match event with
  | .receive input => receiveRequest before result (ReceiveReassembly.immediate before.core before.receiveStore input)
  | .read _ => readRequest before result
  | _ => none

def output (result : Endpoint.Result) : Option AckReaction.Acknowledgment :=
  match result.state.ackReaction, result.output with
  | some reaction, some packet => some ⟨packet.packet.segment.acknowledgment, reaction.advertisement.frontier,
      packet.packet.segment.window.val⟩
  | _, _ => none

def kind (_before : Endpoint.State) (_event : A.Event) (result : Endpoint.Result) : Netlib.Theory.TimedReaction.OutputKind :=
  match result.decision with
  | .accepted .emitAck | .accepted .dispatchAck => .response
  | _ => .independent

def adapter : T.Adapter Endpoint.State A.Event Endpoint.Result Unit AckReaction.Demand AckReaction.Acknowledgment :=
  ⟨ApplicationTrace.evaluate, Endpoint.Result.state, work, Endpoint.State.now, request, output, kind, AckReaction.covers⟩

def active (step : A.Step) : Bool :=
  (request step.before step.event step.result).isSome || (output step.result).isSome

structure Link (actual : A.Step) (checked : T.CheckedStep adapter) : Prop where
  before : checked.before = actual.before
  event : checked.event = actual.event
  result : checked.result = actual.result
  stamp : checked.stamp = actual.stamp
  clock : active actual = true → checked.view.now = actual.before.now
  origin : ∀ packet, actual.result.output = some packet → ApplicationTrace.OutputOrigin actual packet

def validateOutput (step : A.Step) : Except String { _value : Unit //
    ∀ packet, step.result.output = some packet → ApplicationTrace.OutputOrigin step packet } :=
  match actual : step.result.output with
  | none => .ok ⟨(), by intro packet found; cases found⟩
  | some packet =>
    match parsed : ApplicationTrace.stepOutput step with
    | .error reason => .error reason
    | .ok certified =>
      have same : certified.val = packet := Option.some.inj (certified.property.actual.symm.trans actual)
      .ok ⟨(), by
        intro next found
        have equal : packet = next := Option.some.inj found
        rw [← equal, ← same]
        exact certified.property⟩

def checkStep (step : A.Step) : Except String (T.CheckedStep adapter) :=
  if !step.supported then .error "The ACK trace contains an unsupported endpoint operation."
  else if active step && decide (step.result.state.now ≠ step.before.now) then
    .error "An ACK cause or output changed its local clock within one operation."
  else match validateOutput step with
    | .error reason => .error reason
    | .ok _ =>
      match reflected : T.observe (work step.before) (adapter.observation step.before step.event step.result) AckReaction.covers with
      | .error _ => .error "The actual endpoint operation does not meet its timed reaction transition."
      | .ok projected =>
        if same : projected = work step.result.state then
          .ok ⟨step.before, step.event, step.result, step.stamp, step.computed, by
            change T.observe (work step.before) (adapter.observation step.before step.event step.result) AckReaction.covers = .ok (work step.result.state)
            exact reflected.trans (congrArg Except.ok same)⟩
        else .error "The actual endpoint reaction state differs from its checked projection."

theorem checkStep_link (actual : A.Step) (checked : T.CheckedStep adapter)
    (accepted : checkStep actual = .ok checked) : Link actual checked := by
  unfold checkStep at accepted
  split at accepted
  · cases accepted
  · split at accepted
    · cases accepted
    · rename_i unchanged
      split at accepted
      · cases accepted
      · rename_i certificate verified
        split at accepted
        · cases accepted
        · rename_i projected reflected
          split at accepted
          · cases accepted
            refine ⟨rfl, rfl, rfl, rfl, ?_, certificate.property⟩
            intro enabled
            have same : actual.result.state.now = actual.before.now := by
              cases different : decide (actual.result.state.now ≠ actual.before.now) <;> simp_all
            exact same
          · cases accepted

def checkSteps : List A.Step → Except String (List (T.CheckedStep adapter))
  | [] => .ok []
  | head :: tail => do
    let checked ← checkStep head
    let rest ← checkSteps tail
    return checked :: rest

theorem checkSteps_cons (head : A.Step) (tail : List A.Step) (checked : List (T.CheckedStep adapter))
    (accepted : checkSteps (head :: tail) = .ok checked) :
    ∃ first rest, checkStep head = .ok first ∧ checkSteps tail = .ok rest ∧ checked = first :: rest := by
  unfold checkSteps at accepted
  cases first : checkStep head with
  | error reason => simp [first, bind, Except.bind] at accepted
  | ok projected =>
    cases rest : checkSteps tail with
    | error reason => simp [first, rest, bind, Except.bind] at accepted
    | ok list =>
      simp only [first, rest, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at accepted
      exact ⟨projected, list, rfl, rfl, accepted.symm⟩

theorem checkSteps_history (chain : A.Chain initial steps final) (checked : List (T.CheckedStep adapter))
    (accepted : checkSteps steps = .ok checked) : T.History adapter initial checked final := by
  induction chain generalizing checked with
  | nil state =>
    simp only [checkSteps, Except.ok.injEq] at accepted
    subst checked
    exact .nil state
  | cons head tail ih =>
    obtain ⟨first, rest, firstEq, restEq, same⟩ := checkSteps_cons head _ checked accepted
    have link := checkStep_link head first firstEq
    have history := ih rest restEq
    rw [same, ← link.before]
    apply Netlib.Theory.TimedReaction.History.cons first
    have after : first.after = head.result.state := by
      change first.result.state = _
      rw [link.result]
    rw [after]
    exact history

theorem checkSteps_origin (steps : List A.Step) (checked : List (T.CheckedStep adapter))
    (accepted : checkSteps steps = .ok checked) (step : T.CheckedStep adapter) (member : step ∈ checked) :
    ∃ actual ∈ steps, Link actual step := by
  induction steps generalizing checked with
  | nil => simp [checkSteps] at accepted; subst checked; simp at member
  | cons head tail ih =>
    obtain ⟨first, rest, firstEq, restEq, same⟩ := checkSteps_cons head tail checked accepted
    rw [same] at member
    rcases List.mem_cons.mp member with equal | member
    · subst step
      exact ⟨head, by simp, checkStep_link head first firstEq⟩
    · obtain ⟨actual, belongs, link⟩ := ih rest restEq member
      exact ⟨actual, by simp [belongs], link⟩

theorem receiveRequest_kind (before : Endpoint.State) (result : Endpoint.Result)
    (demand : AckReaction.Demand) (delay : Nat) (immediate : Bool)
    (selected : receiveRequest before result immediate = some (demand, delay)) :
    demand.kind = .data ∨ demand.kind = .sequence := by
  unfold receiveRequest at selected
  split at selected
  · split at selected <;> first | (cases selected; simp [AckReaction.demand]) | (cases selected)
  · cases selected

theorem receiveRequest_ack (before : Endpoint.State) (result : Endpoint.Result)
    (demand : AckReaction.Demand) (delay : Nat) (immediate : Bool)
    (selected : receiveRequest before result immediate = some (demand, delay)) :
    result.ack.isSome = true := by
  unfold receiveRequest at selected
  split at selected
  · simp_all
  · cases selected

theorem readRequest_kind (before : Endpoint.State) (result : Endpoint.Result)
    (demand : AckReaction.Demand) (delay : Nat) (selected : readRequest before result = some (demand, delay)) :
    demand.kind = .window := by
  unfold readRequest at selected
  split at selected
  · dsimp only at selected
    split at selected <;> cases selected
    rfl
  · cases selected

theorem request_source (step : A.Step) (demand : AckReaction.Demand) (delay : Nat)
    (selected : request step.before step.event step.result = some (demand, delay)) :
    (∃ input, step.event = .receive input ∧ step.result.ack.isSome = true ∧
      (demand.kind = .data ∨ demand.kind = .sequence)) ∨
    (∃ count, step.event = .read count ∧ demand.kind = .window) := by
  cases event : step.event with
  | receive input =>
    have received : receiveRequest step.before step.result
        (ReceiveReassembly.immediate step.before.core step.before.receiveStore input) = some (demand, delay) := by
      simpa only [request, event] using selected
    exact .inl ⟨input, rfl, receiveRequest_ack _ _ _ _ _ received, receiveRequest_kind _ _ _ _ _ received⟩
  | read count =>
    have consumed : readRequest step.before step.result = some (demand, delay) := by
      simpa only [request, event] using selected
    exact .inr ⟨count, rfl, readRequest_kind _ _ _ _ consumed⟩
  | write _ | send _ _ | emitAck _ | dispatchAck _ | timeout _ | advanceClock _ | enableAck | enableRecovery | enableStartupRecovery _ =>
    simp [request, event] at selected

theorem output_fields (result : Endpoint.Result) (metadata : AckReaction.Acknowledgment)
    (selected : output result = some metadata) :
    ∃ reaction packet, result.state.ackReaction = some reaction ∧ result.output = some packet ∧
      metadata = ⟨packet.packet.segment.acknowledgment, reaction.advertisement.frontier, packet.packet.segment.window.val⟩ := by
  unfold output at selected
  split at selected
  · rename_i reaction packet enabled present
    cases selected
    exact ⟨reaction, packet, enabled, present, rfl⟩
  · cases selected

theorem Link.request (link : Link actual checked) :
    checked.view.request = request actual.before actual.event actual.result := by
  change AckTrace.request checked.before checked.event checked.result = _
  rw [link.before, link.event, link.result]

theorem checkSteps_stamps (steps : List A.Step) (checked : List (T.CheckedStep adapter))
    (accepted : checkSteps steps = .ok checked) : checked.map (·.stamp) = steps.map (·.stamp) := by
  induction steps generalizing checked with
  | nil => simp [checkSteps] at accepted; subst checked; rfl
  | cons head tail ih =>
    obtain ⟨first, rest, firstEq, restEq, same⟩ := checkSteps_cons head tail checked accepted
    rw [same]
    simp only [List.map_cons, (checkStep_link head first firstEq).stamp, ih rest restEq]

theorem checkSteps_ordered (steps : List A.Step) (checked : List (T.CheckedStep adapter))
    (accepted : checkSteps steps = .ok checked) (ordered : A.Chronological steps) :
    checked.Pairwise (fun first second => first.stamp < second.stamp) := by
  have mapped : (steps.map (·.stamp)).Pairwise (· < ·) := List.pairwise_map.mpr ordered
  rw [← checkSteps_stamps steps checked accepted] at mapped
  exact List.pairwise_map.mp mapped

structure Assurance (initial : Endpoint.State) (steps : List A.Step) (final : Endpoint.State) where
  chain : A.Chain initial steps final
  ordered : A.Chronological steps
  started : initial.ackReaction = none
  enabled : final.ackReaction.isSome = true
  projected : List (T.CheckedStep adapter)
  checked : checkSteps steps = .ok projected
  history : T.History adapter initial projected final
  closed : (work final).pending = []

def assure (chain : A.Chain initial steps final) (ordered : A.Chronological steps)
    (started : initial.ackReaction = none) : Except String (Assurance initial steps final) := do
  match checked : checkSteps steps with
  | .error reason => throw reason
  | .ok projected =>
    if enabled : final.ackReaction.isSome = true then
      if closed : (work final).pending = [] then
        return ⟨chain, ordered, started, enabled, projected, checked, checkSteps_history chain projected checked, closed⟩
      else throw "The actual endpoint trace has unresolved ACK causes."
    else throw "The actual endpoint trace did not enable ACK scheduling."

theorem receiveRequest_delay (before : Endpoint.State) (result : Endpoint.Result)
    (demand : AckReaction.Demand) (delay : Nat) (immediate : Bool)
    (selected : receiveRequest before result immediate = some (demand, delay)) :
    delay ≤ 499 := by
  unfold receiveRequest at selected
  split at selected
  · split at selected
    · cases selected
      split <;> omega
    · cases selected
      omega
    · cases selected
  · cases selected

theorem readRequest_delay (before : Endpoint.State) (result : Endpoint.Result)
    (demand : AckReaction.Demand) (delay : Nat) (selected : readRequest before result = some (demand, delay)) :
    delay ≤ 499 := by
  unfold readRequest at selected
  split at selected
  · dsimp only at selected
    split at selected <;> cases selected
    omega
  · cases selected

theorem request_delay (step : A.Step) (demand : AckReaction.Demand) (delay : Nat)
    (selected : request step.before step.event step.result = some (demand, delay)) : delay ≤ 499 := by
  cases event : step.event with
  | receive input => exact receiveRequest_delay _ _ _ _ _ (by simpa only [request, event] using selected)
  | read count => exact readRequest_delay _ _ _ _ (by simpa only [request, event] using selected)
  | write _ | send _ _ | emitAck _ | dispatchAck _ | timeout _ | advanceClock _ | enableAck | enableRecovery | enableStartupRecovery _ =>
    simp [request, event] at selected

theorem request_none_of_origin (origin : ApplicationTrace.OutputOrigin step packet) :
    request step.before step.event step.result = none := by
  cases origin with
  | send count policy event accepted actual => simp only [request, event]
  | ack policy event accepted actual => simp only [request, event]
  | dispatchAck policy event accepted actual => simp only [request, event]
  | retry count policy event accepted actual => simp only [request, event]

structure Causal (steps : List A.Step) (completion : Netlib.Theory.TimedReaction.Discharge Unit AckReaction.Demand AckReaction.Acknowledgment)
    (cause : Netlib.Theory.TimedReaction.Cause Unit AckReaction.Demand) where
  issuer : A.Step
  issuerMember : issuer ∈ steps
  delay : Nat
  request : AckTrace.request issuer.before issuer.event issuer.result = some (cause.demand, delay)
  allocated : cause = Netlib.Theory.TimedReaction.fresh (work issuer.before) issuer.before.now cause.demand delay
  response : A.OutputAt steps
  actualOutput : output response.step.result = some completion.output
  created : completion = ⟨(work response.step.before).nextDischarge, (work response.step.before).domain,
    response.step.before.now, completion.output, (work response.step.before).pending⟩
  pending : cause ∈ (work response.step.before).pending
  issuedAt : cause.issuedAt = issuer.before.now
  outputAt : completion.time = response.step.before.now
  earlier : issuer.stamp ≤ response.step.stamp
  timed : cause.issuedAt ≤ completion.time ∧ completion.time ≤ cause.due
  covered : AckReaction.covers cause.demand completion.output = true

theorem Causal.strict_delay (value : Causal steps completion cause) :
    value.response.step.before.now - value.issuer.before.now < 500 := by
  have delay := request_delay value.issuer cause.demand value.delay value.request
  have due : cause.due = value.issuer.before.now + value.delay := congrArg Netlib.Theory.TimedReaction.Cause.due value.allocated
  have upper := value.timed.2
  rw [value.outputAt, due] at upper
  omega

theorem Assurance.causal (value : Assurance initial steps final)
    (completion : Netlib.Theory.TimedReaction.Discharge Unit AckReaction.Demand AckReaction.Acknowledgment)
    (completed : completion ∈ (work final).completed)
    (cause : Netlib.Theory.TimedReaction.Cause Unit AckReaction.Demand) (member : cause ∈ completion.causes) :
    Nonempty (Causal steps completion cause) := by
  have empty : adapter.reaction initial = T.initial () := by
    change work initial = T.initial ()
    simp only [work, value.started, Option.map_none, Option.getD_none]
  obtain ⟨generic⟩ := value.history.causal_witness () empty completion completed cause member
  have dischargedMember : generic.discharge ∈ value.projected :=
    Eq.mpr (congrArg (fun list => generic.discharge ∈ list) generic.split) (by simp)
  have issuerMember : generic.issuer ∈ value.projected := by
    apply Eq.mpr (congrArg (fun list => generic.issuer ∈ list) generic.split)
    rcases generic.place with prior | same
    · exact List.mem_append_left _ prior
    · rw [same]
      simp
  obtain ⟨issuer, issuerPresent, issuerLink⟩ := checkSteps_origin steps value.projected value.checked generic.issuer issuerMember
  obtain ⟨response, responsePresent, responseLink⟩ := checkSteps_origin steps value.projected value.checked generic.discharge dischargedMember
  have actualOutput : output response.result = some completion.output := by
    rw [← responseLink.result]
    exact generic.actualOutput
  obtain ⟨reaction, packet, enabled, packetPresent, packetFields⟩ := output_fields response.result completion.output actualOutput
  obtain ⟨prior, later, split, _, _⟩ := value.chain.split response responsePresent
  let responseAt : A.OutputAt steps := ⟨prior, response, later, split, packet, responseLink.origin packet packetPresent⟩
  have responseActive : active response = true := by simp only [active, actualOutput, Option.isSome_some, Bool.or_true]
  have outputAt : completion.time = response.before.now := by
    obtain ⟨_, _, _, _, same⟩ := generic.discharged
    exact (congrArg Netlib.Theory.TimedReaction.Discharge.time same).trans (responseLink.clock responseActive)
  have noRequest : generic.discharge.view.request = none :=
    responseLink.request.trans (request_none_of_origin responseAt.origin)
  have requestedStateEq : Netlib.Theory.TimedReaction.requestedState
      (adapter.reaction generic.discharge.before) generic.discharge.view = work response.before := by
    simp only [Netlib.Theory.TimedReaction.requestedState, noRequest]
    exact congrArg work responseLink.before
  have created : completion = ⟨(work response.before).nextDischarge, (work response.before).domain,
      response.before.now, completion.output, (work response.before).pending⟩ := by
    obtain ⟨_, metadata, _, _, same⟩ := generic.discharged
    have metadataEq : completion.output = metadata := congrArg Netlib.Theory.TimedReaction.Discharge.output same
    apply same.trans
    rw [requestedStateEq, responseLink.clock responseActive, ← metadataEq]
  have pending : cause ∈ (work response.before).pending :=
    Eq.mp (congrArg (fun causes => cause ∈ causes) (congrArg Netlib.Theory.TimedReaction.Discharge.causes created)) member
  have ordinal := generic.ordinal (checkSteps_ordered steps value.projected value.checked value.ordered)
  rw [issuerLink.stamp, responseLink.stamp] at ordinal
  have issued := generic.issued
  change cause ∈ Netlib.Theory.TimedReaction.issued (work generic.issuer.before) generic.issuer.view at issued
  cases selected : generic.issuer.view.request with
  | none => simp [Netlib.Theory.TimedReaction.issued, selected] at issued
  | some pair =>
    obtain ⟨demand, delay⟩ := pair
    have allocated : cause = Netlib.Theory.TimedReaction.fresh (work generic.issuer.before) generic.issuer.view.now demand delay := by
      simpa only [Netlib.Theory.TimedReaction.issued, selected, List.mem_singleton] using issued
    have requested : request issuer.before issuer.event issuer.result = some (demand, delay) :=
      issuerLink.request.symm.trans selected
    have issuerActive : active issuer = true := by simp only [active, requested, Option.isSome_some, Bool.true_or]
    have clock := issuerLink.clock issuerActive
    have demandEq : cause.demand = demand := congrArg Netlib.Theory.TimedReaction.Cause.demand allocated
    have allocatedActual : cause = Netlib.Theory.TimedReaction.fresh (work issuer.before) issuer.before.now cause.demand delay := by
      rw [demandEq]
      simpa only [issuerLink.before, clock] using allocated
    have issuerTime : cause.issuedAt = issuer.before.now := by rw [allocatedActual]; rfl
    have requestActual : request issuer.before issuer.event issuer.result = some (cause.demand, delay) := by
      rw [demandEq]
      exact requested
    exact ⟨⟨issuer, issuerPresent, delay, requestActual, allocatedActual, responseAt, actualOutput, created, pending,
      issuerTime, outputAt, ordinal, ⟨generic.issuedBefore, generic.onTime⟩, generic.covered⟩⟩

theorem checkSteps_projects (steps : List A.Step) (checked : List (T.CheckedStep adapter))
    (accepted : checkSteps steps = .ok checked) (actual : A.Step) (member : actual ∈ steps) :
    ∃ step ∈ checked, Link actual step := by
  induction steps generalizing checked with
  | nil => simp at member
  | cons head tail ih =>
    obtain ⟨first, rest, firstEq, restEq, same⟩ := checkSteps_cons head tail checked accepted
    rw [same]
    rcases List.mem_cons.mp member with equal | member
    · subst actual
      exact ⟨first, by simp, checkStep_link head first firstEq⟩
    · obtain ⟨step, belongs, link⟩ := ih rest restEq member
      exact ⟨step, by simp [belongs], link⟩

theorem Assurance.issued_response (value : Assurance initial steps final) (issuer : A.Step)
    (member : issuer ∈ steps) (demand : AckReaction.Demand) (delay : Nat)
    (requested : request issuer.before issuer.event issuer.result = some (demand, delay)) :
    let cause := Netlib.Theory.TimedReaction.fresh (work issuer.before) issuer.before.now demand delay
    ∃ completion ∈ (work final).completed, cause ∈ completion.causes ∧ Nonempty (Causal steps completion cause) := by
  obtain ⟨step, belongs, link⟩ := checkSteps_projects steps value.projected value.checked issuer member
  have active : active issuer = true := by simp only [AckTrace.active, requested, Option.isSome_some, Bool.true_or]
  have selected : step.view.request = some (demand, delay) := link.request.trans requested
  have issued : Netlib.Theory.TimedReaction.IssuedAt step
      (Netlib.Theory.TimedReaction.fresh (work issuer.before) issuer.before.now demand delay) := by
    change _ ∈ Netlib.Theory.TimedReaction.issued (work step.before) step.view
    simp only [Netlib.Theory.TimedReaction.issued, selected, List.mem_singleton]
    rw [link.before, link.clock active]
  have empty : adapter.reaction initial = T.initial () := by
    change work initial = T.initial ()
    simp only [work, value.started, Option.map_none, Option.getD_none]
  obtain ⟨completion, completed, present, _⟩ := value.history.closed_response () empty value.closed step belongs _ issued
  exact ⟨completion, completed, present, value.causal completion completed _ present⟩

theorem Causal.packet_fields (value : Causal steps completion cause) :
    completion.output.cursor = value.response.output.packet.segment.acknowledgment ∧
      completion.output.window = value.response.output.packet.segment.window.val := by
  obtain ⟨reaction, packet, enabled, present, fields⟩ := output_fields value.response.step.result completion.output value.actualOutput
  have same : packet = value.response.output :=
    Option.some.inj (present.symm.trans value.response.origin.actual)
  subst packet
  exact ⟨congrArg AckReaction.Acknowledgment.cursor fields, congrArg AckReaction.Acknowledgment.window fields⟩

theorem readRequest_source (before : Endpoint.State) (result : Endpoint.Result)
    (demand : AckReaction.Demand) (delay : Nat) (selected : readRequest before result = some (demand, delay)) :
    ∃ reaction amount, before.ackReaction = some reaction ∧ result.decision = .accepted (.read amount) ∧
      AckReaction.candidate reaction before.core.capacity before.core.window before.effectiveMSS <
        AckReaction.candidate reaction before.core.capacity result.state.core.window before.effectiveMSS := by
  unfold readRequest at selected
  split at selected
  · rename_i reaction amount stored accepted
    dsimp only at selected
    split at selected
    · rename_i grows
      exact ⟨reaction, amount, stored, accepted, grows⟩
    · cases selected
  · cases selected

theorem read_amount (step : A.Step) (count amount : Nat) (event : step.event = .read count)
    (accepted : step.result.decision = .accepted (.read amount)) : amount = count := by
  have selected : (Endpoint.read step.before count).decision = .accepted (.read amount) := by
    simpa only [step.computed, event, ApplicationTrace.evaluate] using accepted
  unfold Endpoint.read at selected
  split at selected
  · cases selected
  · split at selected
    · cases selected
    · have equal := Endpoint.Accepted.read.inj (Endpoint.Decision.accepted.inj selected)
      exact equal.symm

theorem read_source (step : A.Step) (count : Nat) (event : step.event = .read count)
    (demand : AckReaction.Demand) (delay : Nat)
    (selected : request step.before step.event step.result = some (demand, delay)) :
    ∃ reaction, step.before.ackReaction = some reaction ∧ step.result.decision = .accepted (.read count) ∧
      AckReaction.candidate reaction step.before.core.capacity step.before.core.window step.before.effectiveMSS <
        AckReaction.candidate reaction step.before.core.capacity step.result.state.core.window step.before.effectiveMSS := by
  have read : readRequest step.before step.result = some (demand, delay) := by
    simpa only [request, event] using selected
  obtain ⟨reaction, amount, stored, accepted, grows⟩ := readRequest_source _ _ _ _ read
  have same := read_amount step count amount event accepted
  subst amount
  exact ⟨reaction, stored, accepted, grows⟩

theorem ordered_unique {steps : List A.Step} (ordered : A.Chronological steps) (first second : A.Step)
    (firstMember : first ∈ steps) (secondMember : second ∈ steps) (same : first.stamp = second.stamp) : first = second := by
  induction steps with
  | nil => simp at firstMember
  | cons head tail ih =>
    have pair := List.pairwise_cons.mp ordered
    rcases List.mem_cons.mp firstMember with equal | firstTail
    · subst first
      rcases List.mem_cons.mp secondMember with equal | secondTail
      · exact equal.symm
      · have before := pair.1 second secondTail
        omega
    · rcases List.mem_cons.mp secondMember with equal | secondTail
      · subst second
        have before := pair.1 first firstTail
        omega
      · exact ih pair.2 firstTail secondTail

theorem Causal.strict_ordinal (value : Causal steps completion cause) (ordered : A.Chronological steps) :
    value.issuer.stamp < value.response.step.stamp := by
  have different : value.issuer ≠ value.response.step := by
    intro same
    have requested := value.request
    rw [same, request_none_of_origin value.response.origin] at requested
    cases requested
  by_cases earlier : value.issuer.stamp < value.response.step.stamp
  · exact earlier
  · have same : value.issuer.stamp = value.response.step.stamp := by have bound := value.earlier; omega
    exact False.elim (different (ordered_unique ordered _ _ value.issuerMember value.response.member same))

theorem Causal.sequence_coverage (value : Causal steps completion cause) :
    cause.demand.position ≤ completion.output.position ∧
      cause.demand.cursor.add (completion.output.position - cause.demand.position) =
        value.response.output.packet.segment.acknowledgment := by
  obtain ⟨afterReaction, packet, enabled, present, metadata⟩ := output_fields value.response.step.result completion.output value.actualOutput
  have same : packet = value.response.output := Option.some.inj (present.symm.trans value.response.origin.actual)
  subst packet
  have state := value.response.origin.ack_state
  rw [enabled] at state
  cases beforeEnabled : value.response.step.before.ackReaction with
  | none => simp [beforeEnabled] at state
  | some previous =>
    simp only [beforeEnabled, Option.map_some, Option.some.injEq] at state
    have position : completion.output.position = previous.advertisement.frontier :=
      (congrArg AckReaction.Acknowledgment.position metadata).trans
        ((congrArg (fun reaction : AckReaction.State => reaction.advertisement.frontier) state).trans rfl)
    have coherent := value.response.origin.ack_coherent
    simp only [Endpoint.AckCoherent, beforeEnabled] at coherent
    have pending : cause ∈ previous.work.pending := by
      simpa only [work, beforeEnabled, Option.map_some, Option.getD_some] using value.pending
    have frame := coherent.2
    have target := frame.2.2.2.2 cause pending
    have bound : cause.demand.position ≤ completion.output.position ∧
        cause.demand.minimumEdge ≤ completion.output.position + completion.output.window := by
      simpa only [AckReaction.covers, decide_eq_true_eq] using value.covered
    refine ⟨bound.1, ?_⟩
    calc
      cause.demand.cursor.add (completion.output.position - cause.demand.position) =
          (previous.origin.add cause.demand.position).add (previous.advertisement.frontier - cause.demand.position) := by
            rw [target.2, position]
      _ = previous.origin.add (cause.demand.position + (previous.advertisement.frontier - cause.demand.position)) :=
        Seq.add_add _ _ _
      _ = previous.origin.add previous.advertisement.frontier := by
        congr 1
        have inside := target.1
        omega
      _ = value.response.step.before.core.receiveNext := frame.2.1
      _ = value.response.output.packet.segment.acknowledgment := value.response.origin.ack_fields.1.symm

theorem Causal.strict_earlier (value : Causal steps completion cause) (ordered : A.Chronological steps) :
    value.issuer.stamp < value.response.step.stamp := value.strict_ordinal ordered

end Netlib.Protocol.TCP.AckTrace
