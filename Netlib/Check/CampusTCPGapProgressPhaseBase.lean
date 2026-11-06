import Netlib.Check.CampusTCPRecoveryRoundPhaseBase

/-!
# Actual cut frames for held-gap progress

The initial cut already contains packet and application history.
Every later cut retains that history and the fixed environment.
-/

namespace Netlib.Check.CampusTCPGapProgressPhaseBase

open Protocol.TCP CampusTCPModel CampusTCPEnabled CampusTCPRoundGuards
open CampusTCPRound (Cut)
export CampusTCPRoundPhaseBase (Move)
export CampusTCPRecoveryRoundPhaseBase (At)

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {initial current : Cut input complete}

structure Anchor (initial current : Cut input complete) : Prop where
  guards : Guards current.endpoints
  retained : initial.report.steps <+: current.report.steps
  environment : CampusTCPRoundEnvironment.environment initial.report.final =
    CampusTCPRoundEnvironment.environment current.report.final

theorem Anchor.refl (cut : Cut input complete) (guards : Guards cut.endpoints) : Anchor cut cut :=
  ⟨guards, List.prefix_refl _, rfl⟩

theorem Anchor.member (anchor : Anchor initial current) (member : actual ∈ initial.report.steps) :
    actual ∈ current.report.steps := anchor.retained.subset member

theorem Anchor.clock (anchor : Anchor initial current) (actual : Step input)
    (before : actual.before = current.report.final) (actor : Actor) (millis : Nat)
    (event : actual.event = .advanceClock actor millis)
    (recovery : Recovery.State) (runtime : (endpoint current.endpoints actor).recovery = some recovery)
    (monotone : recovery.now ≤ millis)
    (timely : Endpoint.AckTimeReady (endpoint current.endpoints actor) millis) :
    ∃ move : Move current actual, At current move.after ∧ Anchor initial move.after := by
  obtain ⟨move, placement, guards⟩ := Netlib.Check.CampusTCPRecoveryRoundPhaseBase.At.clock
    (Netlib.Check.CampusTCPRecoveryRoundPhaseBase.At.refl current) actual before actor millis event anchor.guards
    recovery runtime monotone timely
  exact ⟨move, placement, guards, anchor.retained.trans move.retained,
    anchor.environment.trans placement.frame.environment.symm⟩

end Netlib.Check.CampusTCPGapProgressPhaseBase
