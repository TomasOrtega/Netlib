import Netlib.Check.CampusTCPTwoExchangeEvidence

namespace Netlib.Check.CampusTCPTwoExchangeEvidence

open Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPRoundPhaseBase (Move)
open CampusTCPTwoProgressStart

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current : Cut input complete} {sender : Actor} {gateway : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {native : NativeEnv cut gateway initial.gatewayState.session.entry} {quantum allowance : Nat}
variable {reverseLower reverseUpper : List UInt8} {monitor : M.Monitor}

theorem needWrite_write (forward : L.Complete initial native quantum allowance current monitor.forward)
    (mode : monitor.mode = .needWrite)
    (endpointReserve : CampusTCPTwoReverseReserves.Initial initial reverseLower reverseUpper)
    (gatewayReserve : CampusTCPTwoReverseGeometry.Initial initial reverseLower reverseUpper)
    (lowerNonempty : reverseLower ≠ []) (upperNonempty : reverseUpper ≠ [])
    (actual : Step input) (before : actual.before = current.report.final)
    (event : actual.event = .write sender.other (reverseLower ++ reverseUpper))
    (allowed : CampusTCPTwoExchangeMonitor.Allowed
      (CampusTCPTwoExchangeSetup.config initial native quantum allowance reverseLower reverseUpper)
      current.report.final monitor actual.event) :
    ∃ move : Move current actual, Nonempty (Evidence initial native quantum allowance reverseLower reverseUpper move.after
      (CampusTCPTwoExchangeMonitor.observe
        (CampusTCPTwoExchangeSetup.config initial native quantum allowance reverseLower reverseUpper) monitor actual)) := by
  obtain ⟨start⟩ := CampusTCPTwoReverseGeometry.start_actual forward endpointReserve gatewayReserve
    lowerNonempty upperNonempty actual before event
  let move := start.boundary.write.move
  have checked : (actual.result.supported && actual.result.passed &&
      CampusTCPTwoExchangeMonitor.allowed
        (CampusTCPTwoExchangeSetup.config initial native quantum allowance reverseLower reverseUpper)
        actual.before monitor actual.event) = true := by
    rw [move.supported, move.passed, before]
    exact allowed
  refine ⟨move, ?_⟩
  simp only [CampusTCPTwoExchangeMonitor.observe, checked, ite_true]
  simp only [mode, event]
  exact ⟨.reverse forward start
    (CampusTCPTwoProgressEvidence.Evidence.ofInitial start.reverseInitial start.reverseNative quantum
      (allowance - monitor.forward.drops.length)) rfl
    (by change CampusTCPTwoProgressMonitor.Mode.originals ≠ .done; decide)⟩

theorem needWrite_clock (forward : L.Complete initial native quantum allowance current monitor.forward)
    (mode : monitor.mode = .needWrite) (budget : allowance ≤ 2)
    (actual : Step input) (before : actual.before = current.report.final)
    (event : actual.event = .advanceClock actor millis)
    (allowed : CampusTCPTwoExchangeMonitor.Allowed
      (CampusTCPTwoExchangeSetup.config initial native quantum allowance reverseLower reverseUpper)
      current.report.final monitor actual.event) :
    ∃ move : Move current actual, Nonempty (Evidence initial native quantum allowance reverseLower reverseUpper move.after
      (CampusTCPTwoExchangeMonitor.observe
        (CampusTCPTwoExchangeSetup.config initial native quantum allowance reverseLower reverseUpper) monitor actual)) := by
  let cfg := CampusTCPTwoExchangeSetup.config initial native quantum allowance reverseLower reverseUpper
  have localAllowed : CampusTCPTwoProgressMonitor.Allowed cfg.forward current.report.final monitor.forward actual.event := by
    simpa only [CampusTCPTwoExchangeMonitor.Allowed, CampusTCPTwoExchangeMonitor.allowed, mode, event,
      CampusTCPTwoProgressMonitor.Allowed] using allowed
  obtain ⟨move, ⟨next⟩⟩ := (CampusTCPTwoProgressEvidence.Evidence.done forward).step budget actual before localAllowed
  have localChecked : (actual.result.supported && actual.result.passed &&
      CampusTCPTwoProgressMonitor.allowed cfg.forward actual.before monitor.forward actual.event) = true := by
    rw [move.supported, move.passed, before]
    exact localAllowed
  have observed : CampusTCPTwoProgressMonitor.observe cfg.forward monitor.forward actual = monitor.forward := by
    simp only [CampusTCPTwoProgressMonitor.observe, localChecked, ite_true]
    simp only [event]
  have nextValue : L.Evidence initial native quantum allowance move.after monitor.forward := by
    have selected : L.Evidence initial native quantum allowance move.after
        (CampusTCPTwoProgressMonitor.observe cfg.forward monitor.forward actual) := next
    rw [observed] at selected
    exact selected
  obtain ⟨finished⟩ := CampusTCPTwoProgressInvariant.done_evidence nextValue forward.mode
  have checked : (actual.result.supported && actual.result.passed &&
      CampusTCPTwoExchangeMonitor.allowed cfg actual.before monitor actual.event) = true := by
    rw [move.supported, move.passed, before]
    exact allowed
  change ∃ move : Move current actual, Nonempty (Evidence initial native quantum allowance reverseLower reverseUpper move.after
    (CampusTCPTwoExchangeMonitor.observe cfg monitor actual))
  refine ⟨move, ?_⟩
  simp only [CampusTCPTwoExchangeMonitor.observe, checked, ite_true]
  simp only [mode, event]
  exact ⟨.needWrite finished (by change monitor.mode = .needWrite; exact mode)⟩

private theorem actor_beq (left right : Actor) : (left == right) = true ↔ left = right := by
  cases left <;> cases right <;> decide

theorem needWrite_event (mode : monitor.mode = .needWrite) (actual : Step input)
    (allowed : CampusTCPTwoExchangeMonitor.Allowed
      (CampusTCPTwoExchangeSetup.config initial native quantum allowance reverseLower reverseUpper)
      current.report.final monitor actual.event) :
    actual.event = .write sender.other (reverseLower ++ reverseUpper) ∨
      ∃ actor millis, actual.event = .advanceClock actor millis := by
  classical
  by_cases write : ∃ actor bytes, actual.event = .write actor bytes
  · obtain ⟨actor, bytes, event⟩ := write
    have fields : sender.other = actor ∧ reverseLower ++ reverseUpper = bytes := by
      simpa only [CampusTCPTwoExchangeMonitor.Allowed, CampusTCPTwoExchangeMonitor.allowed, mode, event,
        CampusTCPTwoExchangeMonitor.serves, CampusTCPTwoExchangeMonitor.writeDemand,
        CampusTCPTwoExchangeSetup.config, CampusTCPTwoExchangeMonitor.Config.reverseBytes,
        CampusTCPTwoProgressSetup.config, Bool.and_eq_true, actor_beq, beq_iff_eq] using allowed
    exact .inl (by rw [event, ← fields.1, ← fields.2])
  by_cases clock : ∃ actor millis, actual.event = .advanceClock actor millis
  · exact .inr clock
  cases event : actual.event <;>
    simp_all [CampusTCPTwoExchangeMonitor.Allowed, CampusTCPTwoExchangeMonitor.allowed]

theorem needWrite_step (forward : L.Complete initial native quantum allowance current monitor.forward)
    (mode : monitor.mode = .needWrite) (budget : allowance ≤ 2)
    (endpointReserve : CampusTCPTwoReverseReserves.Initial initial reverseLower reverseUpper)
    (gatewayReserve : CampusTCPTwoReverseGeometry.Initial initial reverseLower reverseUpper)
    (lowerNonempty : reverseLower ≠ []) (upperNonempty : reverseUpper ≠ [])
    (actual : Step input) (before : actual.before = current.report.final)
    (allowed : CampusTCPTwoExchangeMonitor.Allowed
      (CampusTCPTwoExchangeSetup.config initial native quantum allowance reverseLower reverseUpper)
      current.report.final monitor actual.event) :
    ∃ move : Move current actual, Nonempty (Evidence initial native quantum allowance reverseLower reverseUpper move.after
      (CampusTCPTwoExchangeMonitor.observe
        (CampusTCPTwoExchangeSetup.config initial native quantum allowance reverseLower reverseUpper) monitor actual)) := by
  rcases needWrite_event mode actual allowed with event | ⟨actor, millis, event⟩
  · exact needWrite_write forward mode endpointReserve gatewayReserve lowerNonempty upperNonempty actual before event allowed
  · exact needWrite_clock forward mode budget actual before event allowed

end Netlib.Check.CampusTCPTwoExchangeEvidence
