import Netlib.Check.CampusTCPTwoProgressPhaseNetworkState
import Netlib.Check.CampusTCPTwoProgressPhaseNormalize

namespace Netlib.Check.CampusTCPTwoProgressPhaseDropState

open Protocol Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart CampusTCPTwoProgressPhaseBase
open CampusTCPTwoProgressPhaseState CampusTCPTwoProgressPaths
open CampusTCPTwoProgressReadWriter (SelectedOutput)
open CampusTCPTwoProgressSetup (config)
open CampusTCPTwoProgressPathsReady (rangeAt)
open CampusTCPTwoProgressPhaseNormalize (Resolved)

namespace M
export CampusTCPTwoProgressMonitor (Monitor Lane DropTarget observe normalize)
end M
namespace S
export CampusTCPTwoProgressSender (Stage Part)
end S
namespace R
export CampusTCPTwoProgressReceiver (Stage)
end R
namespace D
export CampusTCPTwoProgressPhaseDebt (Work Debt)
end D
namespace P
export CampusTCPTwoProgressPathDrop (Dropped Credited originalTarget creditBook)
end P

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current : Cut input complete} {sender : Actor} {gateway : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {native : NativeEnv cut gateway initial.gatewayState.session.entry} {quantum allowance : Nat}
variable {monitor raw updated : M.Monitor} {sent : S.Stage initial} {received : R.Stage}
variable {part : S.Part} {lane : M.Lane} {actual : Step input}
variable {core : Core initial native quantum allowance current monitor sent received}
variable {produced : Produced input.active input.passive} {packetID : Nat} {target : M.DropTarget}

structure Scalar (received : R.Stage) (raw : M.Monitor) : Prop where
  mode : raw.mode = .originals ∨ raw.mode = .recovery
  originals : raw.mode = .originals → raw.retry.phase = .done ∧ raw.waiting = false ∧ raw.retries = 0
  recovery : raw.mode = .recovery → raw.lower.phase = .done ∧ raw.upper.phase = .done
  serial : raw.ack.isSome = true → raw.retry.phase = .done
  ackNonempty : raw.ack.isSome = true → received ≠ .empty
  waiting : raw.waiting = true → raw.ack = none ∧ raw.retry.phase = .done

structure Normal (received : R.Stage) (raw updated : M.Monitor) : Prop where
  shape : Scalar received updated
  lowerLane : updated.lower = raw.lower
  upperLane : updated.upper = raw.upper
  retryLane : updated.retry = raw.retry
  ack : updated.ack = raw.ack
  retries : updated.retries = raw.retries
  runnable : updated.mode = .recovery → updated.waiting = false → updated.ack = none → updated.retry.phase ≠ .done
  originalOpen : updated.mode = .originals → updated.ack = none → ¬(updated.lower.phase = .done ∧ updated.upper.phase = .done)

theorem normalized (active : Active core)
    {item : Theory.PacketCustody.Item (Transit input)} {selected : CampusTCPTwoProgressPhaseDrop.Selected core item target actual}
    {book : CampusTCPTwoProgressLossHistory.Book initial (config initial native quantum allowance)}
    (result : CampusTCPTwoProgressPhaseDrop.Result selected book) (shape : Scalar received raw)
    (observed : M.observe (config initial native quantum allowance) monitor actual =
      M.normalize (config initial native quantum allowance) selected.appended.move.after.report.final raw) :
    Normal received raw (M.observe (config initial native quantum allowance) monitor actual) := by
  rcases CampusTCPTwoProgressPhaseNormalize.normalize_cases (raw := raw) result.next active.nonempty with
    ⟨unresolved, same⟩ | ⟨resolved, same⟩
  · rw [observed, same]
    refine ⟨shape, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
    · intro mode _ ack done
      exact unresolved ⟨ack, .inr ⟨mode, done⟩⟩
    · intro mode ack done
      exact unresolved ⟨ack, .inl ⟨mode, done.1, done.2⟩⟩
  · have fields : raw.ack = none ∧ raw.lower.phase = .done ∧ raw.upper.phase = .done ∧ raw.retry.phase = .done := by
      obtain ⟨ack, first | second⟩ := resolved
      · exact ⟨ack, first.2.1, first.2.2, (shape.originals first.1).1⟩
      · exact ⟨ack, (shape.recovery second.1).1, (shape.recovery second.1).2, second.2⟩
    rw [observed, same]
    refine ⟨?_, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
    · refine ⟨.inr rfl, ?_, fun _ => ⟨fields.2.1, fields.2.2.1⟩, ?_, ?_, fun _ => ⟨fields.1, fields.2.2.2⟩⟩
      · intro impossible; cases impossible
      · intro pending; rw [fields.1] at pending; cases pending
      · intro pending; rw [fields.1] at pending; cases pending
    · intro _ impossible; cases impossible
    · intro impossible; cases impossible

theorem observed_drop (drop : P.Dropped core produced packetID target actual) :
    M.observe (config initial native quantum allowance) monitor actual =
      M.normalize (config initial native quantum allowance) drop.selected.appended.move.after.report.final
        (match target with
          | .lower => { monitor with drops := monitor.drops ++ [drop.item.id], lower := { monitor.lower with phase := .done } }
          | .upper => { monitor with drops := monitor.drops ++ [drop.item.id], upper := { monitor.upper with phase := .done } }
          | .retry => { monitor with drops := monitor.drops ++ [drop.item.id], retry := { monitor.retry with phase := .done } }
          | .ack => { monitor with drops := monitor.drops ++ [drop.item.id], ack := none }) := by
  rw [drop.selected.observed, CampusTCPTwoProgressMonitor.observeDrop,
    drop.selected.appended.move.beforeEq, drop.selected.selected, drop.selected.appended.move.final]
  cases target <;> rfl

theorem recovery_fields (drop : P.Dropped core produced packetID target actual)
    (mode : (M.observe (config initial native quantum allowance) monitor actual).mode = .recovery)
    (waiting : (M.observe (config initial native quantum allowance) monitor actual).waiting = false) :
    monitor.mode = .recovery ∧ monitor.waiting = false := by
  rw [observed_drop drop] at mode waiting
  have same := CampusTCPTwoProgressRecoveryHead.normalize_nonwaiting_eq _ _ _ mode waiting
  rw [same] at mode waiting
  cases target <;> exact ⟨mode, waiting⟩

def assemble (active : Active core) (drop : P.Dropped core produced packetID target actual)
    {book : CampusTCPTwoProgressLossHistory.Book initial (config initial native quantum allowance)}
    (result : CampusTCPTwoProgressPhaseDrop.Result drop.selected book)
    (normal : Normal received raw (M.observe (config initial native quantum allowance) monitor actual))
    (lowerLane : OriginalLane initial native drop.selected.appended.move.after result.next.live.gatewayState received .lower
      (M.observe (config initial native quantum allowance) monitor actual).lower)
    (upperLane : OriginalLane initial native drop.selected.appended.move.after result.next.live.gatewayState received .upper
      (M.observe (config initial native quantum allowance) monitor actual).upper)
    (retry : RetryLane initial native drop.selected.appended.move.after result.next.live.gatewayState sent
      (M.observe (config initial native quantum allowance) monitor actual).retry)
    (ack : AckState result.next)
    (debt : ∀ role head rest, CampusTCPTwoProgressRetry.HeadRange sent role head rest → Nonempty (D.Debt result.next role))
    (upperMissing : sent.retiredBytes = 0 → ¬Arrived received .upper →
      (M.observe (config initial native quantum allowance) monitor actual).upper.phase = .done →
      ∃ position, result.next.losses.book.cause .upper = some position)
    (ackFrom : ∀ lane, raw.ack = some lane → monitor.ack = some lane) : Active result.next := by
  have runtime : result.next.live.senderFlight.recovery = core.live.senderFlight.recovery := by
    have slots := congrArg (fun value => (endpoint value sender).recovery) drop.selected.appended.endpoints
    exact Option.some.inj (result.next.live.senderFlight.runtime.symm.trans (slots.trans core.live.senderFlight.runtime))
  have gatewayFrame : beforeService input drop.selected.appended.move.after.report.final gateway =
      beforeService input current.report.final gateway := by
    rw [drop.selected.appended.move.final]
    exact drop.selected.appended.facts.beforeService gateway
  have session : result.next.live.gatewayState.gateway.session = core.live.gatewayState.gateway.session := by
    have phase := result.next.live.gatewayState.gateway.phase
    rw [gatewayFrame, core.live.gatewayState.gateway.phase] at phase
    exact (Admission.Phase.data.inj phase).symm
  exact {
    mode := normal.shape.mode
    preparing := active.preparing, nonempty := active.nonempty
    lowerLane, upperLane, retry, ack
    originals := normal.shape.originals, recovery := normal.shape.recovery
    recoveryHead := fun mode waiting => active.recoveryHead (recovery_fields drop mode waiting).1
      (recovery_fields drop mode waiting).2
    serial := normal.shape.serial, ackNonempty := normal.shape.ackNonempty, waiting := normal.shape.waiting
    ackGateway := fun lane pending phase => by
      rw [session]
      exact active.ackGateway lane (ackFrom lane (normal.ack.symm ▸ pending)) phase
    runnable := normal.runnable, originalOpen := normal.originalOpen
    debt, upperMissing
    zeroAck := fun lane pending retired => by
      rw [runtime]
      exact active.zeroAck lane (ackFrom lane (normal.ack.symm ▸ pending)) retired
    sources := active.sources.non_delivery drop.selected.appended.move (by rw [drop.selected.appended.facts.event]; trivial) }

def keepDataWork {view : CampusTCPTwoProgressGatewayState.View initial current}
    (work : DataWork initial native current view part lane)
    (drop : P.Dropped core produced packetID target actual)
    (next : CampusTCPTwoProgressGatewayState.View initial drop.selected.appended.move.after)
    (different : ∀ other, other.actor = sender → CampusTCPTwoProgressWire.DataFields initial (part.offset lower) (part.bytes lower upper) other →
      produced ≠ other) : DataWork initial native drop.selected.appended.move.after next part lane := by
  have gatewayFrame : beforeService input drop.selected.appended.move.after.report.final gateway =
      beforeService input current.report.final gateway := by
    rw [drop.selected.appended.move.final]; exact drop.selected.appended.facts.beforeService gateway
  have ingressOther (path : DataIngress initial current part lane) :
      CampusTCPTwoProgressPathRetain.consumedPacket current.report.final actual.event ≠ some path.packetID := by
    rw [drop.selected.appended.facts.event, CampusTCPTwoProgressPathRetain.consumedPacket]
    intro same
    have source := CampusTCPTwoProgressPathDrop.ingress_source path.toIngress drop.selected (Option.some.inj same).symm
    exact different path.output.produced path.output.actor path.output.fields (drop.sourceEq.symm.trans source)
  have linkOther (path : DataLink initial current part lane) :
      CampusTCPTwoProgressPathRetain.consumedPacket current.report.final actual.event ≠ some path.packetID := by
    rw [drop.selected.appended.facts.event, CampusTCPTwoProgressPathRetain.consumedPacket]
    intro same
    have source := CampusTCPTwoProgressPathDrop.link_source path.toLink drop.selected (Option.some.inj same).symm
    exact different path.served.ticket.value.produced path.actor path.fields (drop.sourceEq.symm.trans source)
  cases work with
  | ingress path source =>
    exact .ingress (path.after_move drop.selected.appended.move (ingressOther path)) (source.retain_steps drop.selected.appended.move.retained)
  | ticket path source =>
    exact .ticket (path.after_quiet drop.selected.appended.move (by rw [drop.selected.appended.facts.event]; trivial)) (source.retain_steps drop.selected.appended.move.retained)
  | link path source covered =>
    refine .link (path.after_move drop.selected.appended.move (linkOther path)) (source.retain_steps drop.selected.appended.move.retained) ?_
    have ranges := view.ranges_same next gatewayFrame
    cases part with
    | lower => change next.ranges.lowerRun.isSome = true; rw [ranges.1]; exact covered
    | upper => change next.ranges.upperRun.isSome = true; rw [ranges.2]; exact covered

def keepOriginalLane (before : OriginalLane initial native current core.live.gatewayState received part lane)
    (drop : P.Dropped core produced packetID target actual)
    (next : CampusTCPTwoProgressGatewayState.View initial drop.selected.appended.move.after)
    (different : ∀ other, other.actor = sender → CampusTCPTwoProgressWire.DataFields initial (part.offset lower) (part.bytes lower upper) other →
      produced ≠ other) : OriginalLane initial native drop.selected.appended.move.after next received part lane := by
  cases before with
  | done phase => exact .done phase
  | active work missing => exact .active (keepDataWork work drop next different) missing

theorem actors_ne (first : Produced input.active input.passive) (second : Produced input.active input.passive)
    (data : first.actor = sender) (ack : second.actor = sender.other) : first ≠ second := by
  intro same
  have actors := data.symm.trans ((congrArg Produced.actor same).trans ack)
  cases sender <;> cases actors

def keepAckWork (before : AckWork core lane) (drop : P.Dropped core produced packetID target actual)
    {book : CampusTCPTwoProgressLossHistory.Book initial (config initial native quantum allowance)}
    (result : CampusTCPTwoProgressPhaseDrop.Result drop.selected book) (data : produced.actor = sender) : AckWork result.next lane := by
  have ingressOther (path : AckIngress initial current (received.bytes lower upper).length lane) :
      CampusTCPTwoProgressPathRetain.consumedPacket current.report.final actual.event ≠ some path.packetID := by
    rw [drop.selected.appended.facts.event, CampusTCPTwoProgressPathRetain.consumedPacket]
    intro same
    have source := CampusTCPTwoProgressPathDrop.ingress_source path.toIngress drop.selected (Option.some.inj same).symm
    exact actors_ne produced path.output.produced data path.output.actor (drop.sourceEq.symm.trans source)
  have linkOther (path : AckLink initial current (received.bytes lower upper).length lane) :
      CampusTCPTwoProgressPathRetain.consumedPacket current.report.final actual.event ≠ some path.packetID := by
    rw [drop.selected.appended.facts.event, CampusTCPTwoProgressPathRetain.consumedPacket]
    intro same
    have source := CampusTCPTwoProgressPathDrop.link_source path.toLink drop.selected (Option.some.inj same).symm
    exact actors_ne produced path.served.ticket.value.produced data path.actor (drop.sourceEq.symm.trans source)
  cases before with
  | pending phase queue =>
    refine .pending phase ?_
    have runtime : result.next.live.receiverFacts.reaction = core.live.receiverFacts.reaction := by
      have slots := congrArg (fun value => (endpoint value sender.other).ackReaction) drop.selected.appended.endpoints
      exact Option.some.inj (result.next.live.receiverFacts.ackRuntime.symm.trans (slots.trans core.live.receiverFacts.ackRuntime))
    rw [runtime]; exact queue
  | ingress path => exact .ingress (path.after_move drop.selected.appended.move (ingressOther path))
  | ticket path => exact .ticket (path.after_quiet drop.selected.appended.move (by rw [drop.selected.appended.facts.event]; trivial))
  | link path => exact .link (path.after_move drop.selected.appended.move (linkOther path))

end Netlib.Check.CampusTCPTwoProgressPhaseDropState
