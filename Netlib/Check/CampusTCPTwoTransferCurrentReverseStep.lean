import Netlib.Check.CampusTCPTwoTransferCurrentReverseGeometry

/-!
# Every actual step before the reverse write

Allowed clocks retain the past reader at the current cut.
The selected write starts the reverse task on that same report.
-/

namespace Netlib.Check.CampusTCPTwoTransferCurrentReverseStep

open Protocol Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPRoundPhaseBase (Move)
open CampusTCPTwoProgressStart
open CampusTCPTwoTransferNative (Checks Routing)
open CampusTCPTwoTransferEvidence (Evidence ReadAdvanced)
open CampusTCPTwoTransferPostRead (After Clocked)
open CampusTCPTwoTransferCurrentReverseGeometry (Started)
open CampusTCPTwoTransferLocatedCore (config)

namespace W
export CampusTCPTwoTransferMonitor (Monitor Allowed observe)
end W

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut readBefore current : Cut input complete} {sender : Actor} {gateway location : Gateway}
variable {lower upper : List UInt8} {initial : TwoWriteInitial cut sender gateway lower upper}
variable {checks : Checks cut initial.gatewayState.session.entry} {routing : Routing cut gateway}
variable {quantum allowance : Nat} {reverseLower reverseUpper : List UInt8}
variable {readMonitor monitor : W.Monitor} {readActual actual : Step input}
variable {evidence : Evidence initial checks routing quantum allowance reverseLower reverseUpper readBefore readMonitor location}
variable {forward : ReadAdvanced evidence readActual}

local notation "cfg" => config initial checks routing quantum allowance reverseLower reverseUpper

private theorem actor_beq (left right : Actor) : (left == right) = true ↔ left = right := by
  cases left <;> cases right <;> decide

theorem needWrite_event (value : After forward current monitor) (actual : Step input)
    (allowed : W.Allowed cfg current.report.final monitor actual.event) :
    actual.event = .write sender.other (reverseLower ++ reverseUpper) ∨
      ∃ actor millis, actual.event = .advanceClock actor millis := by
  have noDrain := CampusTCPTwoTransferControlObserve.noDrain_of_non_capture current.report.final monitor
    (by rw [value.finished]; decide)
  have control : CampusTCPTwoTransferMonitor.controlDemand monitor = none := by
    rw [CampusTCPTwoTransferMonitor.controlDemand, value.finished]
  have inner : CampusTCPTwoExchangeMonitor.Allowed ((cfg).at current.report.final) current.report.final monitor.exchange actual.event := by
    simpa only [W.Allowed, CampusTCPTwoTransferMonitor.allowed,
      value.finished, reduceCtorEq, decide_false, Bool.false_eq_true, ite_false, noDrain, control,
      CampusTCPTwoExchangeMonitor.Allowed] using allowed
  by_cases write : ∃ actor bytes, actual.event = .write actor bytes
  · obtain ⟨actor, bytes, event⟩ := write
    have fields : sender.other = actor ∧ reverseLower ++ reverseUpper = bytes := by
      simpa only [CampusTCPTwoExchangeMonitor.Allowed, CampusTCPTwoExchangeMonitor.allowed, value.needWrite, event,
        CampusTCPTwoExchangeMonitor.serves, CampusTCPTwoExchangeMonitor.writeDemand,
        config, CampusTCPTwoTransferNative.Checks.monitorConfig, CampusTCPTwoTransferMonitor.Config.at,
        CampusTCPTwoExchangeSetup.config, CampusTCPTwoProgressSetup.config,
        CampusTCPTwoExchangeMonitor.Config.reverseBytes, Bool.and_eq_true, actor_beq, beq_iff_eq] using inner
    exact .inl (by rw [event, ← fields.1, ← fields.2])
  by_cases clock : ∃ actor millis, actual.event = .advanceClock actor millis
  · exact .inr clock
  cases event : actual.event <;>
    simp_all [CampusTCPTwoExchangeMonitor.Allowed, CampusTCPTwoExchangeMonitor.allowed, value.needWrite]

inductive Advanced (value : After forward current monitor) (actual : Step input) where
  | clock (actor : Actor) (millis : Nat) (clocked : Clocked value actor millis actual)
  | write (start : Started value actual)

variable {value : After forward current monitor}

def Advanced.move (advance : Advanced value actual) : Move current actual :=
  match advance with
  | .clock _ _ clocked => clocked.move
  | .write start => start.boundary.write.move

def Advanced.recorded (advance : Advanced value actual) :
    CampusTCPTwoTransferRecorded.Recorded cut cfg advance.move.after (W.observe cfg monitor actual) :=
  match advance with
  | .clock _ _ clocked => clocked.next.recorded
  | .write start => start.boundary.recorded

theorem Advanced.finished (advance : Advanced value actual) : (W.observe cfg monitor actual).mode = .finished := by
  cases advance with
  | clock actor millis clocked => exact clocked.next.finished
  | write start =>
    rw [start.boundary.observed]
    exact value.finished

theorem Advanced.healthy (advance : Advanced value actual) : (W.observe cfg monitor actual).mode ≠ .invalid := by
  rw [advance.finished]
  decide

theorem step (value : After forward current monitor)
    (endpointReserve : CampusTCPTwoReverseReserves.Initial initial reverseLower reverseUpper)
    (gatewayReserve : CampusTCPTwoReverseGeometry.Initial initial reverseLower reverseUpper)
    (lowerNonempty : reverseLower ≠ []) (upperNonempty : reverseUpper ≠ [])
    (actual : Step input) (before : actual.before = current.report.final)
    (allowed : W.Allowed cfg current.report.final monitor actual.event) : Nonempty (Advanced value actual) := by
  rcases needWrite_event value actual allowed with event | ⟨actor, millis, event⟩
  · obtain ⟨start⟩ := CampusTCPTwoTransferCurrentReverseGeometry.start_actual value endpointReserve gatewayReserve
      lowerNonempty upperNonempty actual before event
    exact ⟨.write start⟩
  · obtain ⟨clocked⟩ := CampusTCPTwoTransferPostRead.Step.clock value actual before event allowed
    exact ⟨.clock actor millis clocked⟩

end Netlib.Check.CampusTCPTwoTransferCurrentReverseStep
