import Netlib.Check.CampusTCPTwoProgressRecoveryCap
import Netlib.Check.CampusTCPTwoProgressEvidenceData
import Netlib.Check.CampusTCPTwoProgressEvidenceDrop
import Netlib.Check.CampusTCPTwoProgressSuffixAge

namespace Netlib.Check.CampusTCPTwoProgressRecoveryCapData

open Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPRoundPhaseBase (Move)
open CampusTCPTwoProgressStart CampusTCPTwoProgressPhaseBase
open CampusTCPTwoProgressPhaseState CampusTCPTwoProgressEvidence
open CampusTCPTwoProgressRecoveryCap
open CampusTCPTwoProgressSetup (config)

namespace M
export CampusTCPTwoProgressMonitor (Monitor observe dropTarget)
end M
namespace G
export CampusTCPGapProgressMonitor (nextAction senderRecovery)
end G
namespace F
export CampusTCPTwoProgressMonitorFacts (counters ordinary_counters drop_counters)
end F

private def QuietEvent : Event → Prop
  | .assign .. | .serve .. | .dropPacket .. => True
  | _ => False

private theorem quiet_application (before : State input) (event : Event) (effect : Effect input)
    (quiet : QuietEvent event) (computed : processCore input before event = .ok effect) :
    effect.application = none := by
  cases event with
  | assign index ingress | serve id observed | dropPacket id =>
    simp only [processCore] at computed
    repeat' first
      | (solve | cases computed; rfl)
      | (cases computed)
      | (split at computed)
      | (dsimp only [CampusTCPModel.get, Except.mapError, bind, Except.bind, pure, Except.pure,
          throw, throwThe, MonadExceptOf.throw] at computed)
  | _ => cases quiet

private theorem Step.quiet_application (actual : Step input) (quiet : QuietEvent actual.event) :
    actual.result.application = none := by
  obtain ⟨effect, custody, computed, result⟩ := actual.processed
  simpa only [result] using
    CampusTCPTwoProgressRecoveryCapData.quiet_application actual.before actual.event effect quiet computed

private theorem chain_empty {before after : Endpoint.State} (chain : ApplicationTrace.Chain before [] after) : after = before := by
  cases chain
  rfl

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current : Cut input complete} {sender : Actor} {gateway : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {native : NativeEnv cut gateway initial.gatewayState.session.entry} {quantum allowance capacity : Nat}
variable {monitor : M.Monitor} {sent : CampusTCPTwoProgressSender.Stage initial}
variable {received : CampusTCPTwoProgressReceiver.Stage}
variable {core : Core initial native quantum allowance current monitor sent received}
variable {actual : Step input}

private theorem Move.quiet_runtime (move : Move current actual) (cfg : CampusTCPTwoProgressMonitor.Config)
    (quiet : QuietEvent actual.event) :
    G.senderRecovery cfg.toConfig move.after.report.final = G.senderRecovery cfg.toConfig current.report.final := by
  have chain := CampusTCPTwoProgressSuffixAge.Move.application_chain move cfg.sender
  rw [Step.quiet_application actual quiet] at chain
  simp only [CampusTCPRecoveryRoundOrigins.localSteps] at chain
  have same := chain_empty chain
  simp only [G.senderRecovery, move.after.connection, current.connection, same]

theorem action_retries (cfg : CampusTCPTwoProgressMonitor.Config) (monitor : M.Monitor) (actual : Step input)
    (action : CampusTCPRoundMonitor.Action) (event : actual.event = action.event) :
    (M.observe cfg monitor actual).retries = monitor.retries := by
  have ordinary := F.ordinary_counters cfg monitor actual
  have frame : F.counters (M.observe cfg monitor actual) = F.counters monitor := by
    unfold M.observe
    split
    · rw [event]
      cases action <;> exact ordinary
    · rfl
  exact congrArg Prod.fst frame

theorem drop_retries (cfg : CampusTCPTwoProgressMonitor.Config) (monitor : M.Monitor) (actual : Step input)
    (id : Nat) (target : CampusTCPTwoProgressMonitor.DropTarget)
    (selected : M.dropTarget cfg actual.before monitor id = some target) (event : actual.event = .dropPacket id) :
    (M.observe cfg monitor actual).retries = monitor.retries := by
  unfold M.observe
  split
  · rw [event]
    exact congrArg Prod.fst (F.drop_counters cfg monitor actual id selected)
  · rfl

theorem retry_cap_hop (active : Active core) (_nonoriginal : monitor.mode ≠ .originals)
    (prior : PendingCap (config initial native quantum allowance) capacity current.report.final monitor)
    (action : CampusTCPRoundMonitor.Action)
    (next : G.nextAction (config initial native quantum allowance).toConfig current.report.final monitor.retry.toGap = some action) :
    ∃ hop : Hop initial native quantum allowance current monitor action.event,
      PendingCap (config initial native quantum allowance) capacity hop.move.after.report.final
        (M.observe (config initial native quantum allowance) monitor hop.actual) := by
  cases active.retry with
  | done phase => simp [G.nextAction, CampusTCPTwoProgressMonitor.Lane.toGap, phase] at next
  | active part head rest selection work =>
    cases work with
    | ingress path source =>
      have selected : action = .assign path.output.index (native.ingress sender) := by
        apply Option.some.inj (next.symm.trans _)
        cases sender <;> exact path.action (config initial native quantum allowance)
      obtain ⟨hop⟩ := CampusTCPTwoProgressEvidence.retry_hop active action next
      refine ⟨hop, prior.same_runtime (Move.quiet_runtime hop.move _ ?_) (action_retries _ _ _ action hop.selected)⟩
      rw [hop.selected, selected]
      trivial
    | ticket path source =>
      have selected : action = .serve path.ticket.id := Option.some.inj (next.symm.trans (path.action _))
      obtain ⟨hop⟩ := CampusTCPTwoProgressEvidence.retry_hop active action next
      refine ⟨hop, prior.same_runtime (Move.quiet_runtime hop.move _ ?_) (action_retries _ _ _ action hop.selected)⟩
      rw [hop.selected, selected]
      trivial
    | link path source covered =>
      obtain ⟨part, ⟨record⟩⟩ := CampusTCPTwoProgressPhaseReceiveState.retry_at active path.phase
      have selected : action = .deliver record.path.index record.path.emission.bytes true :=
        Option.some.inj (next.symm.trans (record.path.action _))
      subst action
      let hop := data_received_hop record
      refine ⟨hop, same_core core record.value.next prior ?_ (fun pending => pending) ?_⟩
      · exact congrArg Recovery.State.rto (CampusTCPTwoProgressPhaseReceiveState.receive_sender_recovery record.value)
      · exact action_retries _ _ _ (.deliver record.path.index record.path.emission.bytes true) record.value.value.delivery.event

theorem drop_cap_hop (active : Active core) (_nonoriginal : monitor.mode ≠ .originals)
    (prior : PendingCap (config initial native quantum allowance) capacity current.report.final monitor)
    (id : Nat) (target : CampusTCPTwoProgressMonitor.DropTarget)
    (selected : M.dropTarget (config initial native quantum allowance) current.report.final monitor id = some target) :
    ∃ hop : Hop initial native quantum allowance current monitor (.dropPacket id),
      PendingCap (config initial native quantum allowance) capacity hop.move.after.report.final
        (M.observe (config initial native quantum allowance) monitor hop.actual) := by
  obtain ⟨hop⟩ := CampusTCPTwoProgressEvidence.drop_hop active id target selected
  refine ⟨hop, prior.same_runtime (Move.quiet_runtime hop.move _ ?_) ?_⟩
  · rw [hop.selected]
    trivial
  · exact drop_retries _ _ hop.actual id target (by rw [hop.move.beforeEq]; exact selected) hop.selected

end Netlib.Check.CampusTCPTwoProgressRecoveryCapData
