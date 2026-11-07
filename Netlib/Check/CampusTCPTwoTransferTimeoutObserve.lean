import Netlib.Check.CampusTCPTwoTransferLocatedTimeout
import Netlib.Check.CampusTCPTwoTransferLocatedCore
import Netlib.Check.CampusTCPTwoTransferLossUpdate

namespace Netlib.Check.CampusTCPTwoTransferTimeoutObserve

open Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart
open CampusTCPTwoTransferNative (Checks Routing)
open CampusTCPTwoTransferLocatedCore (Core config)

namespace W
export CampusTCPTwoTransferMonitor (Allowed allowed controlDemand drainTicket observe ordinary)
end W
namespace M
export CampusTCPTwoProgressMonitor (Allowed observe observeTimeout Lane)
end M
namespace X
export CampusTCPTwoExchangeMonitor (allowed observe)
end X
namespace T
export CampusTCPTwoTransferLocatedTimeout (Retry)
end T

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current : Cut input complete} {sender actor : Actor} {gateway location : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {checks : Checks cut initial.gatewayState.session.entry} {routing : Routing cut gateway}
variable {quantum allowance : Nat} {reverseLower reverseUpper : List UInt8}
variable {monitor : CampusTCPTwoTransferMonitor.Monitor} {actual : Step input}
variable {sent : CampusTCPTwoProgressSender.Stage initial} {received : CampusTCPTwoProgressReceiver.Stage}
variable {core : Core initial checks routing quantum allowance reverseLower reverseUpper current monitor location sent received}
variable {part : CampusTCPTwoProgressSender.Part} {head : Recovery.Outstanding} {rest : List Recovery.Outstanding}

local notation "cfg" => config initial checks routing quantum allowance reverseLower reverseUpper

theorem allowed_timeout_fields (config : CampusTCPTwoTransferMonitor.Config) (state : State input)
    (monitor : CampusTCPTwoTransferMonitor.Monitor) (actor : Actor)
    (allowed : W.Allowed config state monitor (.timeout actor true)) (phase : monitor.exchange.mode = .forward) :
    monitor.mode ≠ .invalid ∧ W.drainTicket state monitor = none ∧ W.controlDemand monitor = none ∧
      M.Allowed (config.at state).forward state monitor.exchange.forward (.timeout actor true) := by
  have valid : monitor.mode ≠ .invalid := by
    intro invalid
    simp only [W.Allowed, W.allowed, invalid, decide_true, ite_true, Bool.false_eq_true] at allowed
  have drainless : W.drainTicket state monitor = none := by
    cases found : W.drainTicket state monitor with
    | none => rfl
    | some ticket =>
      simp only [W.Allowed, W.allowed, valid, decide_false, Bool.false_eq_true, ite_false, found,
        CampusTCPTwoTransferMonitor.drainServes] at allowed
  have controls : W.controlDemand monitor = none := by
    cases found : W.controlDemand monitor with
    | none => rfl
    | some kind =>
      cases kind <;>
        simp only [W.Allowed, W.allowed, valid, decide_false, Bool.false_eq_true, ite_false, drainless,
          found, CampusTCPTwoTransferMonitor.Control.serves] at allowed
  refine ⟨valid, drainless, controls, ?_⟩
  simpa only [W.Allowed, W.allowed, valid, decide_false, Bool.false_eq_true, ite_false, drainless, controls,
    X.allowed, phase, M.Allowed] using allowed

def ingressLane (lane : M.Lane) (index packet : Nat) : M.Lane :=
  ⟨.dataIngress, { lane.refs with dataOutput := some index, dataIngressPacket := some packet }⟩

def afterTimeout (monitor : CampusTCPTwoTransferMonitor.Monitor) (index packet : Nat) : CampusTCPTwoTransferMonitor.Monitor :=
  { monitor with exchange := { monitor.exchange with
    forward := { monitor.exchange.forward with
      retry := ingressLane monitor.exchange.forward.retry index packet
      waiting := false
      retries := monitor.exchange.forward.retries + 1 }
    timeouts := monitor.exchange.timeouts + 1
    slots := monitor.exchange.slots + 1 } }

theorem local_observe (value : T.Retry core.live part head rest actual)
    (allowed : M.Allowed ((cfg).at current.report.final).forward current.report.final monitor.exchange.forward actual.event) :
    M.observe ((cfg).at actual.before).forward monitor.exchange.forward actual =
      { monitor.exchange.forward with
        retry := ingressLane monitor.exchange.forward.retry current.report.final.outputs.length value.packetID
        waiting := false
        retries := monitor.exchange.forward.retries + 1 } := by
  rw [CampusTCPTwoProgressMonitorFacts.observe_timeout _ _ _ value.move.supported value.move.passed
    (by rw [value.move.beforeEq]; exact allowed) value.facts.event]
  have custody := value.custody
  rw [value.move.final] at custody
  have actor : value.facts.produced.actor = sender := by rw [value.facts.production]; rfl
  have self : (sender == sender) = true := by cases sender <;> rfl
  simp only [M.observeTimeout, CampusTCPTwoProgressMonitor.Lane.ofGap,
    CampusTCPGapProgressMonitor.observeOutput, value.facts.output, actor, config,
    CampusTCPTwoTransferNative.Checks.monitorConfig, CampusTCPTwoTransferMonitor.Config.at,
    CampusTCPTwoExchangeSetup.config, CampusTCPTwoProgressSetup.config, ite_true, self,
    value.move.beforeEq, custody, CampusTCPTwoProgressMonitor.Lane.toGap,
    CampusTCPTwoProgressMonitorFacts.phase_beq, reduceCtorEq, decide_false, Bool.false_eq_true,
    ite_false, ingressLane]

theorem observe_timeout (value : T.Retry core.live part head rest actual)
    (phase : monitor.exchange.mode = .forward) (mode : monitor.exchange.forward.mode = .recovery)
    (allowed : W.Allowed cfg current.report.final monitor actual.event) :
    W.observe cfg monitor actual = afterTimeout monitor current.report.final.outputs.length value.packetID := by
  obtain ⟨_, drainless, controls, localAllowed⟩ := allowed_timeout_fields cfg current.report.final monitor sender
    (by rw [← value.facts.event]; exact allowed) phase
  have localStep := local_observe value (by rw [value.facts.event]; exact localAllowed)
  have exchangeAllowed : X.allowed ((cfg).at actual.before) actual.before monitor.exchange actual.event = true := by
    simpa only [X.allowed, phase, M.Allowed, value.move.beforeEq, value.facts.event] using localAllowed
  have exchangeChecked : (actual.result.supported && actual.result.passed &&
      X.allowed ((cfg).at actual.before) actual.before monitor.exchange actual.event) = true := by
    rw [value.move.supported, value.move.passed]
    exact exchangeAllowed
  have exchangeStep : X.observe ((cfg).at actual.before) monitor.exchange actual =
      (afterTimeout monitor current.report.final.outputs.length value.packetID).exchange := by
    rw [X.observe, ite_eq_left exchangeChecked]
    simp only [phase, localStep, mode, CampusTCPTwoProgressMonitorFacts.mode_beq, reduceCtorEq,
      decide_false, Bool.false_eq_true, ite_false]
    congr 1
    · congr 1 <;> exact mode.symm
    · change (match actual.event with | .dropPacket id => monitor.exchange.drops ++ [id] | _ => monitor.exchange.drops) = _
      rw [value.facts.event]
    · change (match actual.event with | .timeout _ true => monitor.exchange.timeouts + 1 | _ => monitor.exchange.timeouts) = _
      rw [value.facts.event]
  have checked : (actual.result.supported && actual.result.passed && W.allowed cfg actual.before monitor actual.event) = true := by
    rw [value.move.supported, value.move.passed, value.move.beforeEq]
    exact allowed
  rw [W.observe, ite_eq_left checked, value.move.beforeEq, drainless, controls, W.ordinary, exchangeStep]
  simp only [afterTimeout, phase, reduceCtorEq, decide_false, Bool.false_eq_true, ite_false]

theorem frame (value : T.Retry core.live part head rest actual)
    (phase : monitor.exchange.mode = .forward) (mode : monitor.exchange.forward.mode = .recovery)
    (allowed : W.Allowed cfg current.report.final monitor actual.event) :
    CampusTCPTwoTransferLossHistory.TimeoutFrame cfg monitor actual := by
  have observed := observe_timeout value phase mode allowed
  exact ⟨by rw [observed]; rfl, by rw [observed]; rfl, by rw [observed]; rfl, by rw [observed]; rfl⟩

theorem healthy (value : T.Retry core.live part head rest actual)
    (phase : monitor.exchange.mode = .forward) (mode : monitor.exchange.forward.mode = .recovery)
    (allowed : W.Allowed cfg current.report.final monitor actual.event) : (W.observe cfg monitor actual).mode ≠ .invalid := by
  rw [observe_timeout value phase mode allowed]
  exact (allowed_timeout_fields cfg current.report.final monitor sender
    (by rw [← value.facts.event]; exact allowed) phase).1

end Netlib.Check.CampusTCPTwoTransferTimeoutObserve
