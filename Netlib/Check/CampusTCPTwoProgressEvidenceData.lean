import Netlib.Check.CampusTCPTwoProgressEvidenceHop
import Netlib.Check.CampusTCPTwoProgressPhaseNetworkStateData
import Netlib.Check.CampusTCPTwoProgressPhaseNetworkStateMore
import Netlib.Check.CampusTCPTwoProgressPhaseRetryReceiveState

namespace Netlib.Check.CampusTCPTwoProgressPhaseState

open Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart CampusTCPTwoProgressPaths

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current : Cut input complete} {sender : Actor} {gateway : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {native : NativeEnv cut gateway initial.gatewayState.session.entry}
variable {view : CampusTCPTwoProgressGatewayState.View initial current} {part : S.Part} {lane firstLane secondLane : M.Lane}

def DataWork.command (work : DataWork initial native current view part lane)
    (cfg : CampusTCPTwoProgressMonitor.Config) : CampusTCPRoundMonitor.Action :=
  match work with
  | .ingress path _ => .assign path.output.index (cfg.toConfig.ingress cfg.sender)
  | .ticket path _ => .serve path.ticket.id
  | .link path _ _ => .deliver path.index path.emission.bytes true

theorem DataWork.command_next (work : DataWork initial native current view part lane)
    (cfg : CampusTCPTwoProgressMonitor.Config) :
    CampusTCPGapProgressMonitor.nextAction cfg.toConfig current.report.final lane.toGap = some (work.command cfg) := by
  cases work with
  | ingress path _ => exact path.action cfg
  | ticket path _ => exact path.action cfg
  | link path _ _ => exact path.action cfg

theorem DataWork.command_ne (first : DataWork initial native current view .lower firstLane)
    (second : DataWork initial native current view .upper secondLane) (cfg : CampusTCPTwoProgressMonitor.Config) :
    first.command cfg ≠ second.command cfg := by
  intro same
  cases first with
  | ingress first _ =>
    cases second with
    | ingress second _ =>
      exact CampusTCPTwoProgressPathsDistinct.output_index_ne first.output second.output
        (CampusTCPRoundMonitor.Action.assign.inj same).1
    | ticket _ _ => cases same
    | link _ _ _ => cases same
  | ticket first _ =>
    cases second with
    | ingress _ _ => cases same
    | ticket second _ =>
      exact CampusTCPTwoProgressPathsDistinct.ticket_id_ne first second
        (CampusTCPRoundMonitor.Action.serve.inj same)
    | link _ _ _ => cases same
  | link first _ _ =>
    cases second with
    | ingress _ _ => cases same
    | ticket _ _ => cases same
    | link second _ _ =>
      exact CampusTCPTwoProgressPathsDistinct.service_index_ne first second
        (CampusTCPRoundMonitor.Action.deliver.inj same).1

end Netlib.Check.CampusTCPTwoProgressPhaseState

namespace Netlib.Check.CampusTCPTwoProgressEvidence

open Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart CampusTCPTwoProgressPhaseBase CampusTCPTwoProgressPhaseState
open CampusTCPTwoProgressPaths
open CampusTCPTwoProgressSetup (config)

namespace N
export CampusTCPTwoProgressPhaseNetwork (assign_data_at serve_data_at)
end N
namespace NS
export CampusTCPTwoProgressPhaseNetworkState
  (lower_assigned lower_served upper_assigned upper_served retry_assigned retry_served)
end NS
namespace G
export CampusTCPGapProgressMonitor (nextAction)
end G

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current : Cut input complete} {sender : Actor} {gateway : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {native : NativeEnv cut gateway initial.gatewayState.session.entry} {quantum allowance : Nat}
variable {monitor : M.Monitor} {sent : S.Stage initial} {received : R.Stage}
variable {core : Core initial native quantum allowance current monitor sent received}
variable {part : CampusTCPTwoProgressSender.Part} {lane : CampusTCPTwoProgressMonitor.Lane}
variable {action : CampusTCPRoundMonitor.Action}

private theorem lane_action_eq (cfg : CampusTCPTwoProgressMonitor.Config) (state : State input)
    (monitor : M.Monitor) (lane : CampusTCPTwoProgressMonitor.Lane) (first second : CampusTCPRoundMonitor.Action)
    (next : G.nextAction cfg.toConfig state lane.toGap = some first)
    (serves : CampusTCPTwoProgressMonitor.servesOption (CampusTCPTwoProgressMonitor.laneDemand cfg state monitor lane)
      second.event = true) : second = first := by
  cases packet : CampusTCPGapProgressMonitor.packetAt lane.toGap <;>
    by_cases budget : monitor.drops.length < cfg.lossAllowance
  all_goals cases second <;>
    simpa [CampusTCPTwoProgressMonitor.laneDemand, next, packet, budget,
      CampusTCPTwoProgressMonitor.servesOption, CampusTCPGapProgressMonitor.serves,
      CampusTCPRoundMonitor.Action.event, CampusTCPRoundMonitor.actionOf] using serves

private theorem not_lower (active : Active core)
    (work : DataWork initial native current core.live.gatewayState .upper monitor.upper)
    (next : G.nextAction (config initial native quantum allowance).toConfig current.report.final monitor.upper.toGap = some action) :
    CampusTCPTwoProgressMonitor.servesOption
      (CampusTCPTwoProgressMonitor.laneDemand (config initial native quantum allowance) current.report.final monitor monitor.lower)
      action.event = false := by
  apply Bool.eq_false_iff.mpr
  intro serves
  cases active.lowerLane with
  | done phase =>
    simp [CampusTCPTwoProgressMonitor.laneDemand, G.nextAction,
      CampusTCPTwoProgressMonitor.Lane.toGap, phase, CampusTCPTwoProgressMonitor.servesOption] at serves
  | active lowerWork _ =>
    have upperEq : action = work.command (config initial native quantum allowance) :=
      Option.some.inj (next.symm.trans (work.command_next _))
    have lowerEq := lane_action_eq _ _ _ _ _ _ (lowerWork.command_next (config initial native quantum allowance)) serves
    exact lowerWork.command_ne work _ (lowerEq.symm.trans upperEq)

private theorem original_allowed (active : Active core) (mode : monitor.mode = .originals) (ack : monitor.ack = none)
    (serves : CampusTCPTwoProgressMonitor.servesOption
        (CampusTCPTwoProgressMonitor.laneDemand (config initial native quantum allowance) current.report.final monitor monitor.lower) action.event = true ∨
      CampusTCPTwoProgressMonitor.servesOption
        (CampusTCPTwoProgressMonitor.laneDemand (config initial native quantum allowance) current.report.final monitor monitor.upper) action.event = true) :
    CampusTCPTwoProgressMonitor.Allowed (config initial native quantum allowance) current.report.final monitor action.event := by
  let cfg := config initial native quantum allowance
  change CampusTCPTwoProgressMonitor.servesOption
      (CampusTCPTwoProgressMonitor.laneDemand cfg current.report.final monitor monitor.lower) action.event = true ∨
    CampusTCPTwoProgressMonitor.servesOption
      (CampusTCPTwoProgressMonitor.laneDemand cfg current.report.final monitor monitor.upper) action.event = true at serves
  have lower := CampusTCPTwoProgressPhaseNetworkState.OriginalLane.not_needSend active.lowerLane
  have upper := CampusTCPTwoProgressPhaseNetworkState.OriginalLane.not_needSend active.upperLane
  have available : ((CampusTCPTwoProgressMonitor.laneDemand cfg current.report.final monitor monitor.lower).isSome ||
      (CampusTCPTwoProgressMonitor.laneDemand cfg current.report.final monitor monitor.upper).isSome) = true := by
    cases first : CampusTCPTwoProgressMonitor.laneDemand cfg current.report.final monitor monitor.lower <;>
      cases second : CampusTCPTwoProgressMonitor.laneDemand cfg current.report.final monitor monitor.upper <;>
      simp_all [CampusTCPTwoProgressMonitor.servesOption]
  apply (CampusTCPTwoProgressMonitorFacts.allowed_iff cfg current.report.final monitor action.event).mpr
  refine ⟨by rw [mode]; decide, .inl ⟨.originalChoice
    (CampusTCPTwoProgressMonitor.laneDemand cfg current.report.final monitor monitor.lower)
    (CampusTCPTwoProgressMonitor.laneDemand cfg current.report.final monitor monitor.upper), ?_, ?_⟩, ?_⟩
  · simp only [CampusTCPTwoProgressMonitor.nextDemand, mode,
      (CampusTCPTwoProgressMonitorFacts.phase_beq_false _ _).mpr lower,
      (CampusTCPTwoProgressMonitorFacts.phase_beq_false _ _).mpr upper, Bool.false_eq_true, ite_false,
      ack, available, ite_true]
  · exact (CampusTCPTwoProgressMonitorFacts.serves_originalChoice _ _ _).mpr serves
  · cases action <;> rfl

def data_received_hop {target : CampusTCPTwoProgressMonitor.DropTarget}
    (record : CampusTCPTwoProgressPhaseReceiveState.Received core part target) :
    Hop initial native quantum allowance current monitor (.deliver record.path.index record.path.emission.bytes true) :=
  ⟨record.value.value.delivery.step, record.value.value.move, record.value.value.delivery.event,
    .active record.value.next record.active⟩

theorem lower_hop (active : Active core) (mode : monitor.mode = .originals) (ack : monitor.ack = none)
    (action : CampusTCPRoundMonitor.Action)
    (next : G.nextAction (config initial native quantum allowance).toConfig current.report.final monitor.lower.toGap = some action) :
    Nonempty (Hop initial native quantum allowance current monitor action.event) := by
  have serves := CampusTCPTwoProgressPhaseObserve.laneDemand_serves (config initial native quantum allowance)
    current.report.final monitor monitor.lower action next
  have allowed := original_allowed active mode ack (.inl serves)
  cases chosen : active.lowerLane with
  | done phase => simp [G.nextAction, CampusTCPTwoProgressMonitor.Lane.toGap, phase] at next
  | active work missing =>
    cases work with
    | ingress path source =>
      have selected : action = .assign path.output.index (native.ingress sender) := by
        apply Option.some.inj (next.symm.trans _)
        cases sender <;> exact path.action (config initial native quantum allowance)
      subst action
      obtain ⟨actual, ⟨value⟩⟩ := N.assign_data_at core path allowed
      exact ⟨⟨actual, value.value.value.move, value.value.event,
        .active value.advance.nextCore (NS.lower_assigned active path source missing chosen value ack)⟩⟩
    | ticket path source =>
      have selected : action = .serve path.ticket.id := Option.some.inj (next.symm.trans (path.action _))
      subst action
      obtain ⟨actual, ⟨value⟩⟩ := N.serve_data_at core path allowed
      exact ⟨⟨actual, value.value.value.move, value.value.value.facts.event,
        .active value.advance.nextCore (NS.lower_served active path source missing chosen value ack)⟩⟩
    | link path source covered =>
      obtain ⟨record⟩ := CampusTCPTwoProgressPhaseReceiveState.lower_at active mode ack path.phase
      have selected : action = .deliver record.path.index record.path.emission.bytes true :=
        Option.some.inj (next.symm.trans (record.path.action _))
      subst action
      exact ⟨data_received_hop record⟩

theorem upper_hop (active : Active core) (mode : monitor.mode = .originals) (ack : monitor.ack = none)
    (action : CampusTCPRoundMonitor.Action)
    (next : G.nextAction (config initial native quantum allowance).toConfig current.report.final monitor.upper.toGap = some action) :
    Nonempty (Hop initial native quantum allowance current monitor action.event) := by
  have serves := CampusTCPTwoProgressPhaseObserve.laneDemand_serves (config initial native quantum allowance)
    current.report.final monitor monitor.upper action next
  have allowed := original_allowed active mode ack (.inr serves)
  cases chosen : active.upperLane with
  | done phase => simp [G.nextAction, CampusTCPTwoProgressMonitor.Lane.toGap, phase] at next
  | active work missing =>
    have lowerFalse := not_lower active work next
    cases work with
    | ingress path source =>
      have selected : action = .assign path.output.index (native.ingress sender) := by
        apply Option.some.inj (next.symm.trans _)
        cases sender <;> exact path.action (config initial native quantum allowance)
      subst action
      obtain ⟨actual, ⟨value⟩⟩ := N.assign_data_at core path allowed
      have lowerActual : CampusTCPTwoProgressMonitor.servesOption
          (CampusTCPTwoProgressMonitor.laneDemand (config initial native quantum allowance) actual.before monitor monitor.lower)
          actual.event = false := by
        rw [value.value.value.move.beforeEq, value.value.event]
        exact lowerFalse
      exact ⟨⟨actual, value.value.value.move, value.value.event,
        .active value.advance.nextCore (NS.upper_assigned active path source missing chosen value ack lowerActual)⟩⟩
    | ticket path source =>
      have selected : action = .serve path.ticket.id := Option.some.inj (next.symm.trans (path.action _))
      subst action
      obtain ⟨actual, ⟨value⟩⟩ := N.serve_data_at core path allowed
      have lowerActual : CampusTCPTwoProgressMonitor.servesOption
          (CampusTCPTwoProgressMonitor.laneDemand (config initial native quantum allowance) actual.before monitor monitor.lower)
          actual.event = false := by
        rw [value.value.value.move.beforeEq, value.value.value.facts.event]
        exact lowerFalse
      exact ⟨⟨actual, value.value.value.move, value.value.value.facts.event,
        .active value.advance.nextCore (NS.upper_served active path source missing chosen value ack lowerActual)⟩⟩
    | link path source covered =>
      obtain ⟨record⟩ := CampusTCPTwoProgressPhaseReceiveState.upper_at active mode ack path.phase
      have selected : action = .deliver record.path.index record.path.emission.bytes true :=
        Option.some.inj (next.symm.trans (record.path.action _))
      subst action
      exact ⟨data_received_hop record⟩

private theorem retry_fields (active : Active core) (live : monitor.retry.phase ≠ .done) :
    monitor.mode = .recovery ∧ monitor.ack = none ∧ monitor.waiting = false := by
  have mode : monitor.mode = .recovery := by
    rcases active.mode with original | recovery
    · exact False.elim (live (active.originals original).1)
    · exact recovery
  have ack : monitor.ack = none := by
    cases found : monitor.ack with
    | none => rfl
    | some lane => exact False.elim (live (active.serial (by rw [found]; rfl)))
  have waiting : monitor.waiting = false := by
    cases found : monitor.waiting with
    | false => rfl
    | true => exact False.elim (live (active.waiting found).2)
  exact ⟨mode, ack, waiting⟩

private theorem retry_allowed (mode : monitor.mode = .recovery) (ack : monitor.ack = none)
    (waiting : monitor.waiting = false)
    (next : G.nextAction (config initial native quantum allowance).toConfig current.report.final monitor.retry.toGap = some action) :
    CampusTCPTwoProgressMonitor.Allowed (config initial native quantum allowance) current.report.final monitor action.event := by
  let cfg := config initial native quantum allowance
  have serves := CampusTCPTwoProgressPhaseObserve.laneDemand_serves cfg current.report.final monitor monitor.retry action next
  obtain ⟨demand, chosen, served⟩ := (CampusTCPTwoProgressMonitorFacts.servesOption_iff _ _).mp serves
  apply (CampusTCPTwoProgressMonitorFacts.allowed_iff cfg current.report.final monitor action.event).mpr
  refine ⟨by rw [mode]; decide, .inl ⟨.single demand, ?_, served⟩, ?_⟩
  · simp only [CampusTCPTwoProgressMonitor.nextDemand, mode, ack, waiting, Bool.false_eq_true, ite_false,
      chosen, Option.map_some]
  · cases action <;> rfl

theorem retry_hop (active : Active core) (action : CampusTCPRoundMonitor.Action)
    (next : G.nextAction (config initial native quantum allowance).toConfig current.report.final monitor.retry.toGap = some action) :
    Nonempty (Hop initial native quantum allowance current monitor action.event) := by
  cases chosen : active.retry with
  | done phase => simp [G.nextAction, CampusTCPTwoProgressMonitor.Lane.toGap, phase] at next
  | active part head rest selection work =>
    obtain ⟨mode, ack, waiting⟩ := retry_fields active work.work.not_done
    have allowed := retry_allowed mode ack waiting next
    cases work with
    | ingress path source =>
      have selected : action = .assign path.output.index (native.ingress sender) := by
        apply Option.some.inj (next.symm.trans _)
        cases sender <;> exact path.action (config initial native quantum allowance)
      subst action
      obtain ⟨actual, ⟨value⟩⟩ := N.assign_data_at core path allowed
      exact ⟨⟨actual, value.value.value.move, value.value.event,
        .active value.advance.nextCore (NS.retry_assigned active path source head rest selection chosen value)⟩⟩
    | ticket path source =>
      have selected : action = .serve path.ticket.id := Option.some.inj (next.symm.trans (path.action _))
      subst action
      obtain ⟨actual, ⟨value⟩⟩ := N.serve_data_at core path allowed
      exact ⟨⟨actual, value.value.value.move, value.value.value.facts.event,
        .active value.advance.nextCore (NS.retry_served active path source head rest selection chosen value)⟩⟩
    | link path source covered =>
      obtain ⟨part, ⟨record⟩⟩ := CampusTCPTwoProgressPhaseReceiveState.retry_at active path.phase
      have selected : action = .deliver record.path.index record.path.emission.bytes true :=
        Option.some.inj (next.symm.trans (record.path.action _))
      subst action
      exact ⟨data_received_hop record⟩

end Netlib.Check.CampusTCPTwoProgressEvidence
