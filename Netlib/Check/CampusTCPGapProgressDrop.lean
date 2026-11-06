import Netlib.Check.CampusTCPGapProgressState
import Netlib.Check.CampusTCPRecoveryRoundDrop

/-!
# Actual selected packet drops in held-gap progress

The existing custody operation consumes the pending identity.
The same actual move retains endpoint, gateway, and stream facts.
-/

namespace Netlib.Check.CampusTCPGapProgressDrop

open CampusTCPModel CampusTCPEnabled Protocol.TCP
open CampusTCPRound (Cut)
namespace D
export CampusTCPRecoveryRoundDrop (Facts Append enabled append)
end D
namespace M
export CampusTCPGapProgressMonitor (Config Monitor nextDemand observe)
end M

variable {input : Input} {complete : H.Completed input.active input.passive}
  {cut current : Cut input complete} {sender : Actor} {lower upper : List UInt8}
  {initial : CampusTCPGapProgressStart.GapInitial cut sender lower upper}
  {retries : Nat} {released : Bool} {id : Nat} {actual : Step input}

def live_after (live : CampusTCPGapProgressState.Live initial current retries released)
    (appended : D.Append current id actual) :
    CampusTCPGapProgressState.Live initial appended.move.after retries released := by
  apply live.reindex appended.move.retained
  · rw [appended.move.final, appended.facts.environment]
  · intro actor
    rw [appended.endpoints]
  · rw [appended.endpoints]
  · rw [appended.move.final]
    exact appended.facts.beforeService .standby

theorem observe_selected (facts : D.Facts before id actual) (config : M.Config) (monitor : M.Monitor)
    (action : CampusTCPRoundMonitor.Action)
    (next : M.nextDemand config before monitor = some (.resolution action id)) :
    M.observe config monitor actual = { monitor with waiting := true, drops := monitor.drops ++ [id] } := by
  simp only [M.observe, facts.supported, facts.passed, Bool.and_self, facts.event, facts.beforeEq,
    next, beq_self_eq_true, ite_true]

end Netlib.Check.CampusTCPGapProgressDrop
