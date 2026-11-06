import Netlib.Check.CampusTCPTwoProgressPhaseNormalize
import Netlib.Check.CampusTCPTwoProgressHandoffRTO

/-!
# Fixed caps for pending recovery work

The cap refers to the actual sender state.
It stays fixed when recovery clocks advance.
-/

namespace Netlib.Check.CampusTCPTwoProgressRecoveryCap

open Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart
open CampusTCPTwoProgressPhaseBase (Core)
open CampusTCPTwoProgressSetup (config)

namespace M
export CampusTCPTwoProgressMonitor (Monitor Config)
end M
namespace G
export CampusTCPGapProgressMonitor (senderRecovery)
end G
namespace S
export CampusTCPTwoProgressSender (Stage)
end S

def PendingCap (cfg : M.Config) (capacity : Nat) (state : State input) (monitor : M.Monitor) : Prop :=
  ∀ recovery, G.senderRecovery cfg.toConfig state = some recovery → recovery.outstanding ≠ [] →
    recovery.rto ≤ 2 ^ monitor.retries * capacity

theorem PendingCap.same_runtime {cfg : M.Config} {capacity : Nat} {before after : State input}
    {monitor updated : M.Monitor} (prior : PendingCap cfg capacity before monitor)
    (runtime : G.senderRecovery cfg.toConfig after = G.senderRecovery cfg.toConfig before)
    (counts : updated.retries = monitor.retries) : PendingCap cfg capacity after updated := by
  intro recovery selected pending
  rw [counts]
  exact prior recovery (runtime.symm.trans selected) pending

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current after : Cut input complete} {sender : Actor} {gateway : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {native : NativeEnv cut gateway initial.gatewayState.session.entry} {quantum allowance capacity : Nat}
variable {monitor updated : M.Monitor} {sent next : S.Stage initial}
variable {received nextReceived : CampusTCPTwoProgressReceiver.Stage}

theorem at_core (core : Core initial native quantum allowance current monitor sent received)
    (prior : PendingCap (config initial native quantum allowance) capacity current.report.final monitor)
    (pending : sent.ledger ≠ []) : core.live.senderFlight.recovery.rto ≤ 2 ^ monitor.retries * capacity :=
  prior _ (CampusTCPTwoProgressPhaseNormalize.sender_runtime core) (by rw [core.live.senderFlight.ledger]; exact pending)

theorem of_core (core : Core initial native quantum allowance current monitor sent received)
    (bounded : sent.ledger ≠ [] → core.live.senderFlight.recovery.rto ≤ 2 ^ monitor.retries * capacity) :
    PendingCap (config initial native quantum allowance) capacity current.report.final monitor := by
  intro recovery runtime pending
  have same : recovery = core.live.senderFlight.recovery :=
    Option.some.inj (runtime.symm.trans (CampusTCPTwoProgressPhaseNormalize.sender_runtime core))
  subst recovery
  exact bounded (by rw [← core.live.senderFlight.ledger]; exact pending)

theorem same_core (core : Core initial native quantum allowance current monitor sent received)
    (nextCore : Core initial native quantum allowance after updated next nextReceived)
    (prior : PendingCap (config initial native quantum allowance) capacity current.report.final monitor)
    (rto : nextCore.live.senderFlight.recovery.rto = core.live.senderFlight.recovery.rto)
    (pending : next.ledger ≠ [] → sent.ledger ≠ []) (counts : updated.retries = monitor.retries) :
    PendingCap (config initial native quantum allowance) capacity after.report.final updated := by
  apply of_core nextCore
  intro nonempty
  rw [rto, counts]
  exact at_core core prior (pending nonempty)

theorem empty_core (core : Core initial native quantum allowance current monitor sent received)
    (empty : sent.ledger = []) : PendingCap (config initial native quantum allowance) capacity current.report.final monitor :=
  of_core core (fun pending => False.elim (pending empty))

theorem from_handoff {span : Nat}
    (prior : CampusTCPTwoProgressHandoffRTO.PendingRTO initial current monitor.retries span) :
    PendingCap (config initial native quantum allowance) (CampusTCPTwoProgressHandoffRTO.cap initial span)
      current.report.final monitor := by
  intro recovery runtime pending
  have selected : (endpoint current.endpoints sender).recovery = some recovery := by
    simpa only [G.senderRecovery, current.connection, config] using runtime
  exact prior recovery selected pending

end Netlib.Check.CampusTCPTwoProgressRecoveryCap
