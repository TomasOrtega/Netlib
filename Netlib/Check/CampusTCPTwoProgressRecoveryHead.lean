import Netlib.Check.CampusTCPTwoProgressMonitor
import Netlib.Check.CampusTCPTwoProgressRetry

/-!
# Current head and normalization facts

Equal current ledgers select the same head.
Normalization cannot create an active recovery path.
-/

namespace Netlib.Check.CampusTCPTwoProgressRecoveryHead

open Protocol.TCP CampusTCPModel CampusTCPEnabled

theorem normalize_nonwaiting_eq (cfg : CampusTCPTwoProgressMonitor.Config) (state : State input)
    (raw : CampusTCPTwoProgressMonitor.Monitor)
    (mode : (CampusTCPTwoProgressMonitor.normalize cfg state raw).mode = .recovery)
    (waiting : (CampusTCPTwoProgressMonitor.normalize cfg state raw).waiting = false) :
    CampusTCPTwoProgressMonitor.normalize cfg state raw = raw := by
  unfold CampusTCPTwoProgressMonitor.normalize at mode waiting ⊢
  dsimp only at mode waiting ⊢
  repeat' first
    | (solve | rfl)
    | (solve | simp_all [CampusTCPTwoProgressMonitor.Monitor.invalid])
    | split at *

theorem head_eq (first : CampusTCPTwoProgressRetry.HeadRange sent part head rest)
    (second : CampusTCPTwoProgressRetry.HeadRange sent other otherHead otherRest) : head = otherHead :=
  (List.cons.inj (first.ledger.symm.trans second.ledger)).1

end Netlib.Check.CampusTCPTwoProgressRecoveryHead
