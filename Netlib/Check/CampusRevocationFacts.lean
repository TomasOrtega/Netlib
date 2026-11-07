import Netlib.Check.CampusRevocationModel

namespace Netlib.Check.CampusRevocationModel

theorem process_event (input : Input) (budget : Nat) (before : State) (event : Event)
    (payload : Payload input budget before) (computed : process input budget before event = .ok payload) :
    payload.event = event := by
  cases event with
  | campus observation =>
    dsimp only [process] at computed
    split at computed
    · simp [throw] at computed
    · simp only [pure, Except.pure, Except.ok.injEq] at computed
      cases computed
      rfl
  | packet call =>
    dsimp only [process] at computed
    split at computed
    · simp [throw, bind, Except.bind] at computed
    · split at computed
      · simp [throw] at computed
      · cases found : SessionInstallation.check input.authentication input.requirements before.campus.authentication
          (before.campus.deployment.handoff.configurations call.gateway) input.handoff.configs budget with
        | error reason => simp [found, bind, Except.bind] at computed
        | ok certificate =>
          simp only [found, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at computed
          cases computed
          rfl
  | deliver capacity => cases computed; rfl
  | idle => cases computed; rfl

theorem Step.processed (actual : Step input budget) :
    process input budget actual.before actual.event = .ok actual.effect.payload := by
  have accepted := actual.computed
  unfold step at accepted
  split at accepted
  · cases found : process input budget actual.before actual.event with
    | error reason => simp [found, bind, Except.bind] at accepted
    | ok payload =>
      simp only [found, bind, Except.bind] at accepted
      split at accepted
      · simp only [pure, Except.pure, Except.ok.injEq] at accepted
        have same := congrArg Effect.payload accepted
        rw [← same]
      · simp [throw] at accepted
  · simp [throw] at accepted

theorem Step.event_eq (actual : Step input budget) : actual.effect.payload.event = actual.event :=
  process_event input budget actual.before actual.event actual.effect.payload actual.processed

theorem State.packetAllowed_correct (before : State) (gateway : Protocol.StatefulFailover.Gateway) :
    before.packetAllowed gateway = true ↔
      before.campus.deployment.handoff.gateways.isFenced gateway = false ∧
        (gateway = .primary → before.campus.deployment.withdrawn = false) := by
  cases gateway <;> simp [State.packetAllowed]

theorem Step.packet_available (actual : Step input budget) (call : PacketCall) (selected : actual.event = .packet call) :
    actual.before.packetAllowed call.gateway = true := by
  have computed := actual.processed
  rw [selected] at computed
  dsimp only [process] at computed
  cases available : actual.before.packetAllowed call.gateway with
  | false => simp [available, throw, bind, Except.bind] at computed
  | true => rfl

theorem campusDatagrams_length (result : CampusDeployment.Result input) : (campusDatagrams result).length ≤ 1 := by
  cases result with
  | mk before payload safe =>
    cases payload with
    | authentication evidence => simp [campusDatagrams]
    | withdraw evidence => simp [campusDatagrams]
    | network evidence =>
      cases served : evidence.model.served with
      | some packet =>
        cases emitted : packet.outcome.output <;> simp [campusDatagrams, served, emitted]
      | none =>
        cases established : evidence.model.established with
        | none => simp [campusDatagrams, served, established]
        | some packet =>
          cases emitted : packet.outcome.output <;> simp [campusDatagrams, served, established, emitted]

theorem Payload.arrivals_length (payload : Payload input budget before) : payload.arrivals.length ≤ 1 := by
  cases payload with
  | campus observation result computed => exact campusDatagrams_length result
  | packet call outcome computed certificate => cases emitted : outcome.output <;> simp [Payload.arrivals, emitted]
  | deliver capacity => simp [Payload.arrivals]
  | idle => simp [Payload.arrivals]

theorem Payload.backlog_bound (payload : Payload input budget before) :
    payload.state.queue.pending.length ≤ before.queue.pending.length + 1 := by
  have bound := Theory.Queue.backlog_bounded before.queue payload.tick
  have arrivals := payload.arrivals_length
  exact Nat.le_trans bound (Nat.add_le_add_left arrivals _)

theorem Payload.deliver_backlog (before : State) (capacity : Nat) :
    (Payload.state (Payload.deliver (input := input) (budget := budget) (before := before) capacity)).queue.pending.length =
      before.queue.pending.length - capacity := by
  simp [Payload.state, Payload.tick, Payload.capacity, Payload.arrivals, Theory.Queue.advance, Theory.Queue.step]

theorem Payload.campus_before (before : State) (observation : CampusDeployment.Observation)
    (result : CampusDeployment.Result input)
    (computed : CampusDeployment.step input budget before.campus observation = .ok result) :
    result.before = before.campus := CampusDeployment.step_before input budget before.campus observation result computed

end Netlib.Check.CampusRevocationModel
