import Netlib.Protocol.ConntrackLifecycleEnabled
import Netlib.Protocol.TCP.WireForwarding

/-!
# Forwarding from current route and filter conditions

A real existing attachment and a live TTL suffice for ordinary wire forwarding.
No successful lifecycle processing or packet output is an input condition.
-/

namespace Netlib.Protocol.TCP.WireForwarding

open Packet

structure ForwardReady (pipeline : ConntrackLifecycle.Pipeline) (input : Input)
    (prepared : ConntrackLifecycle.Prepared input.lifecycle) (hop : String) : Prop where
  existing : prepared.attachment.fresh = false
  route : Routing.nextHop pipeline.routes (destination input prepared).destination = some hop
  forward : StatefulACL.Policy.evaluate pipeline.forwardDefault pipeline.forward prepared.attachment.classification
    (destination input prepared) = .permit
  late : StatefulACL.Policy.evaluate pipeline.lateDefault pipeline.late prepared.attachment.classification
    ((ConntrackLifecycle.sourceStage prepared.attachment.entry prepared.attachment.direction).apply
      (destination input prepared)) = .permit
  ttl : 1 < input.packet.ip.packet.ttl.toNat

theorem process_existing_enabled (pipeline : ConntrackLifecycle.Pipeline) (input : Input)
    (valid : TCPRewrite.SourceValid input.packet) (prepared : ConntrackLifecycle.Prepared input.lifecycle)
    (hop : String) (ready : ForwardReady pipeline input prepared hop) :
    ∃ outcome emission, process pipeline input valid prepared = .ok outcome ∧
      outcome.output = some emission ∧ outcome.state = prepared.state ∧
      outcome.attachment = prepared.attachment ∧ outcome.nextHop = some hop ∧
      outcome.disposition = .forwarded ∧
      emission.target = prepared.attachment.entry.flow.output prepared.attachment.direction := by
  obtain ⟨model, processed, unchanged, attachment, forwarded, nextHop, target⟩ :=
    ConntrackLifecycle.process_existing_forwarded pipeline prepared hop ready.existing ready.route ready.forward ready.late
  obtain ⟨outcome, computed⟩ := process_completes pipeline input valid prepared model processed
  have finished := computed
  rw [process_long pipeline input valid prepared ready.ttl] at finished
  obtain ⟨actual, actualProcessed, same⟩ := finish_realizes pipeline input valid prepared outcome finished
  have actualEq : actual = model := Except.ok.inj (actualProcessed.symm.trans processed)
  subst actual
  have outDisposition : outcome.disposition = .forwarded := by
    rw [same]
    change lifecycleDisposition model.disposition = .forwarded
    rw [forwarded]
    rfl
  obtain ⟨emission, emitted⟩ := Option.isSome_iff_exists.mp
    ((process_forwarded_iff pipeline input valid prepared outcome computed).mpr outDisposition)
  obtain ⟨emittedModel, emittedProcessed, _, _, actualTarget⟩ :=
    finish_output pipeline input valid prepared outcome finished emission emitted
  have emittedSame : emittedModel = model := Except.ok.inj (emittedProcessed.symm.trans processed)
  rw [emittedSame] at actualTarget
  have targetEq : emission.target = prepared.attachment.entry.flow.output prepared.attachment.direction :=
    Option.some.inj (actualTarget.symm.trans target)
  exact ⟨outcome, emission, computed, emitted, by rw [same]; exact unchanged,
    by rw [same]; exact attachment, by rw [same]; exact nextHop, outDisposition, targetEq⟩

end Netlib.Protocol.TCP.WireForwarding
