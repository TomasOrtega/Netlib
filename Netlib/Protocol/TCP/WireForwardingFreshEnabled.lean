import Netlib.Protocol.ConntrackLifecycleFreshEnabled
import Netlib.Protocol.TCP.WireForwardingEnabled

/-!
# Wire output from a fresh permitted flow

Current tuple, route, filter, and TTL guards derive the output.
Ordinary confirmation keeps the actual candidate binding.
-/

namespace Netlib.Protocol.TCP.WireForwarding

open Packet

structure FreshForwardReady (pipeline : ConntrackLifecycle.Pipeline) (input : Input)
    (prepared : ConntrackLifecycle.Prepared input.lifecycle) (hop : String) : Prop where
  fresh : prepared.attachment.fresh = true
  original : prepared.attachment.direction = .original
  classification : prepared.attachment.classification = .new
  keys : ConntrackLifecycle.FreshKeys prepared.state prepared.attachment.entry
  route : Routing.nextHop pipeline.routes (destination input prepared).destination = some hop
  forward : StatefulACL.Policy.evaluate pipeline.forwardDefault pipeline.forward .new
    (destination input prepared) = .permit
  late : StatefulACL.Policy.evaluate pipeline.lateDefault pipeline.late .new
    ((ConntrackLifecycle.sourceStage prepared.attachment.entry .original).apply (destination input prepared)) = .permit
  ttl : 1 < input.packet.ip.packet.ttl.toNat

theorem process_fresh_enabled (pipeline : ConntrackLifecycle.Pipeline) (input : Input)
    (valid : TCPRewrite.SourceValid input.packet) (prepared : ConntrackLifecycle.Prepared input.lifecycle)
    (hop : String) (ready : FreshForwardReady pipeline input prepared hop) :
    ∃ outcome emission, process pipeline input valid prepared = .ok outcome ∧
      outcome.output = some emission ∧
      outcome.state.records = prepared.state.records ++ [⟨prepared.attachment.entry, false⟩] ∧
      outcome.attachment = prepared.attachment ∧ outcome.nextHop = some hop ∧
      outcome.disposition = .forwarded ∧ emission.target = prepared.attachment.entry.flow.output .original := by
  have native : ConntrackLifecycle.FreshForwardConditions pipeline input.lifecycle.packet prepared.attachment.entry hop := by
    refine ⟨?_, ?_, ?_⟩
    · simpa only [destination, Input.lifecycle, ready.original] using ready.route
    · simpa only [destination, Input.lifecycle, ready.original] using ready.forward
    · simpa only [destination, Input.lifecycle, ready.original] using ready.late
  obtain ⟨model, processed, confirmed, attachment, forwarded, nextHop, target⟩ :=
    ConntrackLifecycle.process_fresh_forwarded pipeline prepared hop ready.fresh ready.original
      ready.classification ready.keys native
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
  have targetEq : emission.target = prepared.attachment.entry.flow.output .original :=
    Option.some.inj (actualTarget.symm.trans target)
  exact ⟨outcome, emission, computed, emitted, by rw [same]; exact confirmed,
    by rw [same]; exact attachment, by rw [same]; exact nextHop, outDisposition, targetEq⟩

end Netlib.Protocol.TCP.WireForwarding
