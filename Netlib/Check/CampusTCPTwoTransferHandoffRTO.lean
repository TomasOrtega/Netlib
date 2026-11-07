import Netlib.Check.CampusTCPTwoTransferOriginalBounded

/-!
# Pending RTO cap at the actual original exit

The actual prefix clocks bound the retained current RTO envelope.
The cap applies only while a sender record remains outstanding.
-/

namespace Netlib.Check.CampusTCPTwoTransferHandoffRTO

open Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart
open CampusTCPTwoTransferNative (Checks Routing)
open CampusTCPTwoTransferLocatedCore (Core config)
open CampusTCPTwoTransferOriginalBounded (Exited)

namespace W
export CampusTCPTwoTransferMonitor (Config Monitor)
end W
namespace G
export CampusTCPGapProgressMonitor (senderRecovery)
end G
namespace S
export CampusTCPTwoProgressSender (Stage)
end S
namespace R
export CampusTCPTwoProgressReceiver (Stage)
end R

def PendingCap (cfg : W.Config) (capacity : Nat) (state : State input) (monitor : W.Monitor) : Prop :=
  ∀ recovery, G.senderRecovery cfg.exchange.forward.toConfig state = some recovery → recovery.outstanding ≠ [] →
    recovery.rto ≤ 2 ^ monitor.exchange.forward.retries * capacity

theorem PendingCap.same_runtime {cfg : W.Config} {capacity : Nat} {before after : State input}
    {monitor updated : W.Monitor} (prior : PendingCap cfg capacity before monitor)
    (runtime : G.senderRecovery cfg.exchange.forward.toConfig after = G.senderRecovery cfg.exchange.forward.toConfig before)
    (counts : updated.exchange.forward.retries = monitor.exchange.forward.retries) :
    PendingCap cfg capacity after updated := by
  intro recovery selected pending
  rw [counts]
  exact prior recovery (runtime.symm.trans selected) pending

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current after : Cut input complete} {sender : Actor} {gateway location nextLocation : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {checks : Checks cut initial.gatewayState.session.entry} {routing : Routing cut gateway}
variable {quantum allowance capacity : Nat} {reverseLower reverseUpper : List UInt8}
variable {monitor updated : W.Monitor} {sent next : S.Stage initial} {received nextReceived : R.Stage}

local notation "cfg" => config initial checks routing quantum allowance reverseLower reverseUpper

def cap (initial : TwoWriteInitial cut sender gateway lower upper) (span : Nat) : Nat :=
  RTOEnvelope.cap initial.senderState.idle.recovery.rto initial.senderState.idle.recovery.estimator span

theorem cap_positive (initial : TwoWriteInitial cut sender gateway lower upper) (span : Nat) : 0 < cap initial span := by
  have floor := RTOEnvelope.cap_floor initial.senderState.idle.recovery.rto initial.senderState.idle.recovery.estimator span
  change 1000 ≤ cap initial span at floor
  omega

theorem sender_runtime (core : Core initial checks routing quantum allowance reverseLower reverseUpper current monitor location sent received) :
    G.senderRecovery (cfg).exchange.forward.toConfig current.report.final = some core.live.senderFlight.recovery := by
  simpa only [G.senderRecovery, current.connection, config, CampusTCPTwoTransferNative.Checks.monitorConfig,
    CampusTCPTwoExchangeSetup.config, CampusTCPTwoProgressSetup.config] using core.live.senderFlight.runtime

theorem at_core (core : Core initial checks routing quantum allowance reverseLower reverseUpper current monitor location sent received)
    (prior : PendingCap cfg capacity current.report.final monitor) (pending : sent.ledger ≠ []) :
    core.live.senderFlight.recovery.rto ≤ 2 ^ monitor.exchange.forward.retries * capacity :=
  prior _ (sender_runtime core) (by rw [core.live.senderFlight.ledger]; exact pending)

theorem of_core (core : Core initial checks routing quantum allowance reverseLower reverseUpper current monitor location sent received)
    (bounded : sent.ledger ≠ [] → core.live.senderFlight.recovery.rto ≤ 2 ^ monitor.exchange.forward.retries * capacity) :
    PendingCap cfg capacity current.report.final monitor := by
  intro recovery runtime pending
  have same : recovery = core.live.senderFlight.recovery := Option.some.inj (runtime.symm.trans (sender_runtime core))
  subst recovery
  exact bounded (by rw [← core.live.senderFlight.ledger]; exact pending)

theorem same_core (core : Core initial checks routing quantum allowance reverseLower reverseUpper current monitor location sent received)
    (nextCore : Core initial checks routing quantum allowance reverseLower reverseUpper after updated nextLocation next nextReceived)
    (prior : PendingCap cfg capacity current.report.final monitor)
    (rto : nextCore.live.senderFlight.recovery.rto = core.live.senderFlight.recovery.rto)
    (pending : next.ledger ≠ [] → sent.ledger ≠ [])
    (counts : updated.exchange.forward.retries = monitor.exchange.forward.retries) :
    PendingCap cfg capacity after.report.final updated := by
  apply of_core nextCore
  intro nonempty
  rw [rto, counts]
  exact at_core core prior (pending nonempty)

theorem empty_core (core : Core initial checks routing quantum allowance reverseLower reverseUpper current monitor location sent received)
    (empty : sent.ledger = []) : PendingCap cfg capacity current.report.final monitor :=
  of_core core (fun pending => False.elim (pending empty))

theorem core_pending_cap (core : Core initial checks routing quantum allowance reverseLower reverseUpper current monitor location sent received)
    (span : Nat) (clock : (endpoint current.endpoints sender).now ≤ (endpoint cut.endpoints sender).now + span) :
    PendingCap cfg (cap initial span) current.report.final monitor := by
  apply of_core core
  intro pending
  have bound := core.rtoPending pending
  have now : core.live.senderFlight.recovery.now = (endpoint current.endpoints sender).now := by
    simp only [Endpoint.State.now, core.live.senderFlight.runtime, Option.map_some, Option.getD_some]
  have age : core.live.senderFlight.recovery.now - (endpoint cut.endpoints sender).now ≤ span := by omega
  exact Nat.le_trans bound (Nat.mul_le_mul_left _ (RTOEnvelope.cap_mono _ _ _ _ age))

variable {steps : List (Step input)} {slot horizon : Nat}

theorem Exited.pending_cap (value : Exited initial checks routing quantum allowance reverseLower reverseUpper steps slot)
    (within : slot ≤ horizon) :
    PendingCap cfg (cap initial (horizon * quantum)) value.point.current.report.final
      (CampusTCPTwoTransferMonitor.monitorAt cfg .initial steps slot) := by
  apply core_pending_cap value.point.evidence.core
  exact Nat.le_trans (value.point.now_le sender) (Nat.add_le_add_left (Nat.mul_le_mul_right quantum within) _)

theorem Exited.retry_bound (value : Exited initial checks routing quantum allowance reverseLower reverseUpper steps slot) :
    (CampusTCPTwoTransferMonitor.monitorAt cfg .initial steps slot).exchange.forward.retries ≤ allowance :=
  Nat.le_trans value.point.evidence.core.losses.count value.point.evidence.core.lossBound

end Netlib.Check.CampusTCPTwoTransferHandoffRTO
