import Netlib.Check.CampusTCPTwoProgressEvidenceSelected
import Netlib.Check.CampusTCPTwoProgressEvidenceTimer

/-!
# Actual service for a recovery demand

Current packet paths and head timers supply the serving event.
-/

namespace Netlib.Check.CampusTCPTwoProgressEvidence

open Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart CampusTCPTwoProgressPhaseBase CampusTCPTwoProgressPhaseState
open CampusTCPTwoProgressSetup (config)

namespace RecoveryM
export CampusTCPTwoProgressMonitor (Monitor Config Demand nextDemand laneDemand serves servesOption timerDemand clockAllowed)
end RecoveryM

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current : Cut input complete} {sender : Actor} {gateway : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {native : NativeEnv cut gateway initial.gatewayState.session.entry} {quantum allowance : Nat}
variable {monitor : RecoveryM.Monitor} {demand : RecoveryM.Demand}
variable {sent : CampusTCPTwoProgressSender.Stage initial} {received : CampusTCPTwoProgressReceiver.Stage}
variable {core : Core initial native quantum allowance current monitor sent received}

private theorem recovery_lane_serves (cfg : RecoveryM.Config) (state : State input) (monitor : RecoveryM.Monitor)
    (lane : CampusTCPTwoProgressMonitor.Lane) (action : CampusTCPRoundMonitor.Action)
    (next : CampusTCPGapProgressMonitor.nextAction cfg.toConfig state lane.toGap = some action)
    (pending : (RecoveryM.laneDemand cfg state monitor lane).map (fun value => .single value) = some demand) :
    RecoveryM.serves demand action.event = true := by
  have serves := CampusTCPTwoProgressPhaseObserve.laneDemand_serves cfg state monitor lane action next
  cases found : RecoveryM.laneDemand cfg state monitor lane with
  | none => rw [found] at pending; cases pending
  | some raw =>
    have same : (.single raw : RecoveryM.Demand) = demand := by
      simpa only [found, Option.map_some, Option.some.injEq] using pending
    cases same
    simpa only [RecoveryM.servesOption, found, RecoveryM.serves] using serves

private theorem sender_time (active : Active core) (millis : Nat) :
    Endpoint.AckTimeReady (endpoint current.endpoints sender) millis := by
  have output : sent.hasOutput = true := by
    cases sent <;> try rfl
    cases active.preparing
  have quiet := core.live.senderFlight.quiet output
  intro reaction runtime cause member
  have same : reaction = core.live.senderFlight.reaction :=
    Option.some.inj (runtime.symm.trans core.live.senderFlight.ackRuntime)
  subst reaction
  rw [quiet] at member
  cases member

private theorem selected_tick_allowed (active : Active core) (mode : monitor.mode = .recovery) (millis : Nat)
    (pending : RecoveryM.nextDemand (config initial native quantum allowance) current.report.final monitor =
      some (.single (.tick sender millis)))
    (range : (endpoint current.endpoints sender).now ≤ millis ∧
      millis ≤ (endpoint current.endpoints sender).now + quantum) :
    CampusTCPTwoProgressMonitor.Allowed (config initial native quantum allowance) current.report.final monitor (.advanceClock sender millis) := by
  have guard : RecoveryM.clockAllowed (config initial native quantum allowance) current.report.final (.advanceClock sender millis) = true := by
    simp only [RecoveryM.clockAllowed, CampusTCPGapProgressMonitor.clockAllowed,
      CampusTCPRecoveryRoundMonitor.clockAllowed, current.connection]
    rw [core.live.senderFlight.runtime]
    simp only [Option.isSome_some, Bool.true_and]
    simp only [config]
    exact Bool.and_eq_true_iff.mpr ⟨decide_eq_true range, decide_eq_true (sender_time active millis)⟩
  apply (CampusTCPTwoProgressMonitorFacts.allowed_iff _ _ _ _).mpr
  refine ⟨by rw [mode]; decide, .inl ⟨_, pending, ?_⟩, guard⟩
  cases sender <;> simp [RecoveryM.serves, CampusTCPGapProgressMonitor.serves] <;> rfl

private theorem waiting_selected (active : Active core) (waiting : monitor.waiting = true) (budget : allowance ≤ 2)
    (pending : RecoveryM.nextDemand (config initial native quantum allowance) current.report.final monitor = some demand) :
    ∃ event, Nonempty (Hop initial native quantum allowance current monitor event) ∧ RecoveryM.serves demand event = true := by
  have mode := active.waiting_mode waiting
  have ack := (active.waiting waiting).1
  have selected := pending
  simp only [RecoveryM.nextDemand, mode, ack, waiting, ite_true] at selected
  cases found : RecoveryM.timerDemand (config initial native quantum allowance) current.report.final with
  | none => rw [found] at selected; cases selected
  | some raw =>
    have same : (.single raw : RecoveryM.Demand) = demand := by
      simpa only [found, Option.map_some, Option.some.injEq] using selected
    cases same
    obtain ⟨recovery, head, rest, deadline, target, runtime, _, _, _, chosen⟩ :=
      CampusTCPTwoProgressTimer.timerDemand_some found
    have sameRecovery : recovery = core.live.senderFlight.recovery :=
      Option.some.inj (runtime.symm.trans (CampusTCPTwoProgressPhaseNormalize.sender_runtime core))
    subst recovery
    by_cases early : core.live.senderFlight.recovery.now < target
    · simp only [early, ite_true] at chosen
      subst raw
      let millis := min (core.live.senderFlight.recovery.now + quantum) target
      have now : (endpoint current.endpoints sender).now = core.live.senderFlight.recovery.now := by
        simp only [Endpoint.State.now, core.live.senderFlight.runtime, Option.map_some, Option.getD_some]
      have range : (endpoint current.endpoints sender).now ≤ millis ∧
          millis ≤ (endpoint current.endpoints sender).now + quantum := by
        rw [now]
        dsimp only [millis]
        omega
      have allowed := selected_tick_allowed active mode millis pending range
      refine ⟨.advanceClock sender millis, (Evidence.active core active).clock_hop sender millis allowed, ?_⟩
      cases sender <;> simp [RecoveryM.serves, CampusTCPGapProgressMonitor.serves, millis, config] <;> rfl
    · simp only [early, ite_false] at chosen
      subst raw
      refine ⟨.timeout sender true, timeout_hop active waiting budget pending, ?_⟩
      cases sender <;> simp [RecoveryM.serves, CampusTCPGapProgressMonitor.serves, config] <;> rfl

private theorem ready_recovery_hop (ready : Ready core) :
    Nonempty (Hop initial native quantum allowance current monitor (.read sender.other (lower ++ upper).length)) := by
  cases sent with
  | written | lower => cases ready.preparing
  | both | tail => cases ready.retired
  | retired first second =>
    have all := CampusTCPTwoProgressPhaseNormalize.retired_allReleased core
    cases all
    exact ready_read_hop ready

theorem Evidence.recovery_selected (value : Evidence initial native quantum allowance current monitor)
    (nonoriginal : monitor.mode ≠ .originals) (budget : allowance ≤ 2)
    (pending : RecoveryM.nextDemand (config initial native quantum allowance) current.report.final monitor = some demand) :
    ∃ event, Nonempty (Hop initial native quantum allowance current monitor event) ∧ RecoveryM.serves demand event = true := by
  cases value with
  | written before sources => exact False.elim (nonoriginal before.mode)
  | upper first before sources => exact False.elim (nonoriginal before.mode)
  | active core active =>
    have mode : monitor.mode = .recovery := active.mode.resolve_left nonoriginal
    cases ack : monitor.ack with
    | some lane =>
      have work : AckWork core lane := by simpa only [AckState, ack] using active.ack
      have command : ∃ action, CampusTCPGapProgressMonitor.nextAction
          (config initial native quantum allowance).toConfig current.report.final lane.toGap = some action := by
        cases work with
        | pending phase queue =>
          exact ⟨.emitAck sender.other true, by simp only [CampusTCPGapProgressMonitor.nextAction,
            CampusTCPTwoProgressMonitor.Lane.toGap, phase]; rfl⟩
        | ingress path => exact ⟨_, path.action _⟩
        | ticket path => exact ⟨_, path.action _⟩
        | link path => exact ⟨_, path.action _⟩
      obtain ⟨action, next⟩ := command
      refine ⟨action.event, ack_hop active ack action next, recovery_lane_serves _ _ monitor lane action next ?_⟩
      simpa only [RecoveryM.nextDemand, mode, ack] using pending
    | none =>
      cases waiting : monitor.waiting with
      | true => exact waiting_selected active waiting budget pending
      | false =>
        cases active.retry with
        | done phase => exact False.elim (active.runnable mode waiting ack phase)
        | active part head rest selection work =>
          let action := work.command (config initial native quantum allowance)
          have next := work.command_next (config initial native quantum allowance)
          refine ⟨action.event, retry_hop active action next,
            recovery_lane_serves _ _ monitor monitor.retry action next ?_⟩
          simpa only [RecoveryM.nextDemand, mode, ack, waiting, Bool.false_eq_true, ite_false] using pending
  | ready core ready =>
    have same : demand = .single (.operation (.read sender.other (lower ++ upper).length)) := by
      simpa only [RecoveryM.nextDemand, ready.mode, config, Option.some.injEq] using pending.symm
    subst demand
    refine ⟨_, ready_recovery_hop ready, ?_⟩
    cases sender <;> simp [RecoveryM.serves, CampusTCPGapProgressMonitor.serves, CampusTCPRoundMonitor.actionOf]
  | done done => simp only [RecoveryM.nextDemand, done.mode] at pending; cases pending

end Netlib.Check.CampusTCPTwoProgressEvidence
