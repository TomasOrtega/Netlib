import Netlib.Protocol.ICMPForwarding

namespace Netlib.Protocol.ICMPForwarding

open Packet

structure GenerationFacts (context : Context) (input : Input)
    (outcome : MTUForwarding.Outcome input.transit.packet) (identification : InternetChecksum.Word)
    (emission : Emission input.transit.packet) : Prop where
  reason : cause outcome = some emission.kind
  eligible : eligible context input = true
  route : context.returnPath input.transit.packet.ip.packet.source = some emission.path
  identification : emission.identification = identification
  attachment : emission.attachment = outcome.attachment
  destination : emission.destinationTarget = outcome.afterDestination
  output : StatefulACL.Policy.evaluate context.outputDefault context.output .related emission.beforeSource = .permit
  late : StatefulACL.Policy.evaluate context.lateDefault context.late .related emission.afterSource = .permit

theorem generate_output (context : Context) (input : Input)
    (outcome : MTUForwarding.Outcome input.transit.packet) (identification : InternetChecksum.Word)
    (valid : UDPRewrite.SourceValid input.transit.packet) (emission : Emission input.transit.packet)
    (sent : (generate context input outcome identification valid).output = some emission) :
    GenerationFacts context input outcome identification emission := by
  unfold generate at sent
  split at sent
  · cases sent
  · rename_i kind reason
    split at sent
    · cases sent
    · rename_i allowed
      split at sent
      · cases sent
      · rename_i path route
        dsimp only at sent
        split at sent
        · cases sent
        · rename_i output
          split at sent
          · cases sent
          · rename_i late
            cases sent
            refine ⟨reason, by simpa using allowed, route, rfl, rfl, rfl, ?_, ?_⟩
            · cases action : StatefulACL.Policy.evaluate context.outputDefault context.output .related
                (Emission.beforeSource ⟨kind, path, identification, outcome.attachment, outcome.afterDestination, valid⟩) <;>
                simp_all
            · cases action : StatefulACL.Policy.evaluate context.lateDefault context.late .related
                (Emission.afterSource ⟨kind, path, identification, outcome.attachment, outcome.afterDestination, valid⟩) <;>
                simp_all

theorem generate_sent (context : Context) (input : Input)
    (outcome : MTUForwarding.Outcome input.transit.packet) (identification : InternetChecksum.Word)
    (valid : UDPRewrite.SourceValid input.transit.packet) (kind : ICMP.Kind) (path : ReturnPath)
    (reason : cause outcome = some kind) (allowed : eligible context input = true)
    (route : context.returnPath input.transit.packet.ip.packet.source = some path)
    (output : StatefulACL.Policy.evaluate context.outputDefault context.output .related
      (Emission.beforeSource ⟨kind, path, identification, outcome.attachment, outcome.afterDestination, valid⟩) = .permit)
    (late : StatefulACL.Policy.evaluate context.lateDefault context.late .related
      (Emission.afterSource ⟨kind, path, identification, outcome.attachment, outcome.afterDestination, valid⟩) = .permit) :
    (generate context input outcome identification valid).output =
      some ⟨kind, path, identification, outcome.attachment, outcome.afterDestination, valid⟩ := by
  simp [generate, reason, allowed, route, output, late]

theorem generate_output_iff (context : Context) (input : Input)
    (outcome : MTUForwarding.Outcome input.transit.packet) (identification : InternetChecksum.Word)
    (valid : UDPRewrite.SourceValid input.transit.packet) (emission : Emission input.transit.packet) :
    (generate context input outcome identification valid).output = some emission ↔
      GenerationFacts context input outcome identification emission := by
  constructor
  · exact generate_output context input outcome identification valid emission
  · intro facts
    have same : (⟨emission.kind, emission.path, identification, outcome.attachment, outcome.afterDestination, valid⟩ :
        Emission input.transit.packet) = emission := by
      cases emission
      simp only [Emission.mk.injEq, true_and]
      exact ⟨facts.identification.symm, facts.attachment.symm, facts.destination.symm⟩
    rw [← same]
    apply generate_sent context input outcome identification valid _ _ facts.reason facts.eligible facts.route
    · simpa only [same] using facts.output
    · simpa only [same] using facts.late

theorem step_generated (pipeline : Pipeline) (before : ConntrackLifecycle.State) (input : Input)
    (identification : InternetChecksum.Word) (outcome : Outcome input.transit.packet)
    (accepted : step pipeline before input identification = .ok outcome) :
    ∃ valid, outcome.control = generate pipeline.control input outcome.transit identification valid := by
  unfold step at accepted
  split at accepted
  · cases accepted
  · cases accepted
    exact ⟨_, rfl⟩

theorem step_output (pipeline : Pipeline) (before : ConntrackLifecycle.State) (input : Input)
    (identification : InternetChecksum.Word) (outcome : Outcome input.transit.packet)
    (accepted : step pipeline before input identification = .ok outcome)
    (emission : Emission input.transit.packet) (sent : outcome.control.output = some emission) :
    GenerationFacts pipeline.control input outcome.transit identification emission := by
  obtain ⟨valid, generated⟩ := step_generated pipeline before input identification outcome accepted
  rw [generated] at sent
  exact generate_output pipeline.control input outcome.transit identification valid emission sent

theorem step_output_iff (pipeline : Pipeline) (before : ConntrackLifecycle.State) (input : Input)
    (identification : InternetChecksum.Word) (outcome : Outcome input.transit.packet)
    (accepted : step pipeline before input identification = .ok outcome)
    (emission : Emission input.transit.packet) :
    outcome.control.output = some emission ↔
      GenerationFacts pipeline.control input outcome.transit identification emission := by
  obtain ⟨valid, generated⟩ := step_generated pipeline before input identification outcome accepted
  rw [generated]
  exact generate_output_iff pipeline.control input outcome.transit identification valid emission

private theorem wire_finish_attachment (pipeline : ConntrackLifecycle.Pipeline) (input : WireForwarding.Input)
    (valid : UDPRewrite.SourceValid input.packet) (prepared : ConntrackLifecycle.Prepared input.lifecycle)
    (outcome : WireForwarding.Outcome input.packet)
    (accepted : WireForwarding.finish pipeline input valid prepared = .ok outcome) :
    outcome.attachment = prepared.attachment := by
  obtain ⟨model, processed, same⟩ := WireForwarding.finish_realizes pipeline input valid prepared outcome accepted
  rw [same]
  exact ConntrackLifecycle.process_attachment pipeline prepared model processed

private theorem wire_process_attachment (pipeline : ConntrackLifecycle.Pipeline) (input : WireForwarding.Input)
    (valid : UDPRewrite.SourceValid input.packet) (prepared : ConntrackLifecycle.Prepared input.lifecycle)
    (outcome : WireForwarding.Outcome input.packet)
    (accepted : WireForwarding.process pipeline input valid prepared = .ok outcome) :
    outcome.attachment = prepared.attachment := by
  unfold WireForwarding.process at accepted
  split at accepted
  · exact wire_finish_attachment pipeline input valid prepared outcome accepted
  · split at accepted
    · cases accepted; rfl
    · exact wire_finish_attachment pipeline input valid prepared outcome accepted

private theorem mtu_early_attachment (pipeline : MTUForwarding.Pipeline) (input : MTUForwarding.Input)
    (valid : UDPRewrite.SourceValid input.packet) (prepared : ConntrackLifecycle.Prepared input.lifecycle)
    (early : WireForwarding.route pipeline.forwarding input prepared = none ∨ input.packet.ip.packet.ttl.toNat ≤ 1)
    (outcome : MTUForwarding.Outcome input.packet)
    (accepted : MTUForwarding.early pipeline input valid prepared early = .ok outcome) :
    outcome.attachment = prepared.attachment := by
  unfold MTUForwarding.early at accepted
  split at accepted
  · cases accepted
  · rename_i parent processed
    cases accepted
    exact wire_process_attachment pipeline.forwarding input valid prepared parent processed

private theorem mtu_finish_attachment (pipeline : MTUForwarding.Pipeline) (input : MTUForwarding.Input)
    (valid : UDPRewrite.SourceValid input.packet) (prepared : ConntrackLifecycle.Prepared input.lifecycle)
    (mtu : MTUForwarding.MTU) (allowed : IPv4Fragmentation.Allowed input.packet.ip.packet mtu)
    (outcome : MTUForwarding.Outcome input.packet)
    (accepted : MTUForwarding.finish pipeline input valid prepared mtu allowed = .ok outcome) :
    outcome.attachment = prepared.attachment := by
  unfold MTUForwarding.finish at accepted
  split at accepted
  · cases accepted
  · rename_i parent processed
    cases accepted
    exact wire_finish_attachment pipeline.forwarding input valid prepared parent processed

private theorem mtu_process_attachment (pipeline : MTUForwarding.Pipeline) (input : MTUForwarding.Input)
    (valid : UDPRewrite.SourceValid input.packet) (prepared : ConntrackLifecycle.Prepared input.lifecycle)
    (outcome : MTUForwarding.Outcome input.packet)
    (accepted : MTUForwarding.process pipeline input valid prepared = .ok outcome) :
    outcome.attachment = prepared.attachment := by
  unfold MTUForwarding.process at accepted
  split at accepted
  · exact mtu_early_attachment pipeline input valid prepared _ outcome accepted
  · split at accepted
    · exact mtu_early_attachment pipeline input valid prepared _ outcome accepted
    · dsimp only at accepted
      split at accepted
      · cases accepted; rfl
      · exact mtu_finish_attachment pipeline input valid prepared _ _ outcome accepted

theorem step_attachment (pipeline : Pipeline) (before : ConntrackLifecycle.State) (input : Input)
    (identification : InternetChecksum.Word) (outcome : Outcome input.transit.packet)
    (accepted : step pipeline before input identification = .ok outcome) :
    outcome.transit.attachment.entry.Compatible ∧
      outcome.transit.attachment.entry.flow.input outcome.transit.attachment.direction = input.transit.packet.header := by
  have transit := step_transit pipeline before input identification outcome accepted
  obtain ⟨_, _, valid, prepared, _, processed⟩ :=
    MTUForwarding.step_prepared pipeline.forwarding before input.transit outcome.transit transit
  rw [mtu_process_attachment pipeline.forwarding input.transit valid prepared outcome.transit processed]
  exact ⟨prepared.compatible, congrArg Prod.snd prepared.attached⟩

theorem Emission.quote_restored (emission : Emission source)
    (attached : emission.attachment.entry.flow.input emission.attachment.direction = source.header) :
    emission.quote.packet = emission.initialQuote.packet := by
  have target : emission.restoreTarget = IPv4Quote.header emission.initialQuote := by
    rw [Emission.restoreTarget, attached, Emission.initialQuote,
      IPv4Quote.make_header source emission.valid emission.length
        (quoteLength_bounds source emission.valid emission.path).1]
    rfl
  rw [Emission.quote, target, Emission.destinationQuote]
  exact ICMPNAT.patch_roundtrip_packet emission.initialQuote emission.initialQuote_valid _

theorem step_quote_restored (pipeline : Pipeline) (before : ConntrackLifecycle.State) (input : Input)
    (identification : InternetChecksum.Word) (outcome : Outcome input.transit.packet)
    (accepted : step pipeline before input identification = .ok outcome)
    (emission : Emission input.transit.packet) (sent : outcome.control.output = some emission) :
    emission.quote.packet = (IPv4Quote.make input.transit.packet emission.length).packet := by
  apply emission.quote_restored
  rw [(step_output pipeline before input identification outcome accepted emission sent).attachment]
  exact (step_attachment pipeline before input identification outcome accepted).2

def Emission.destinationDatagram (emission : Emission source) : UDP.Datagram :=
  { source.datagram with
    sourcePort := emission.destinationTarget.sourcePort
    destinationPort := emission.destinationTarget.destinationPort
    checksum := ChecksumRewrite.update source.datagram.checksum
      (ICMPNAT.tupleTotal source.header) (ICMPNAT.tupleTotal emission.destinationTarget) }

theorem Emission.destinationDatagram_accepts (emission : Emission source) :
    UDP.checksumAccepts emission.destinationTarget.source emission.destinationTarget.destination
      emission.destinationDatagram = true := by
  have original := (UDP.decode_fields _ _ _ _ emission.valid.1.2).2.1
  simpa only [Emission.destinationDatagram, ICMPNAT.tupleTotal, UDP.DecodedIPv4.header,
    ChecksumRewrite.udpTupleTotal] using
    ChecksumRewrite.update_udp_accepts source.ip.packet.source source.ip.packet.destination
      emission.destinationTarget.source emission.destinationTarget.destination source.datagram
      emission.destinationTarget.sourcePort emission.destinationTarget.destinationPort original

theorem Emission.destinationQuote_payload (emission : Emission source) :
    emission.destinationQuote.packet.payload = emission.destinationDatagram.encodeBytes.take (emission.length - 20) := by
  have header := IPv4Quote.make_header source emission.valid emission.length
    (quoteLength_bounds source emission.valid emission.path).1
  have payload := (UDP.decode_fields _ _ _ _ emission.valid.1.2).2.2
  have minimum : 8 ≤ emission.length - 20 := by
    have := (quoteLength_bounds source emission.valid emission.path).1
    change 28 ≤ emission.length at this
    omega
  obtain ⟨tail, length⟩ := Nat.exists_eq_add_of_le minimum
  simp only [Emission.destinationQuote, ICMPNAT.patch_payload, Emission.initialQuote, header]
  change ICMPNAT.patchPayload source.header
      { emission.destinationTarget with protocol := Packet.Protocol.udp }
      (source.ip.packet.payload.take (emission.length - 20)) = _
  rw [← payload, length, Nat.add_comm 8 tail]
  simp [UDP.Datagram.encodeBytes, InternetChecksum.wordBytes, ICMPNAT.patchPayload,
    InternetChecksum.read16_bytes, Emission.destinationDatagram, ICMPNAT.tupleTotal,
    UDP.Datagram.lengthWord, UDP.Datagram.wireLength]

theorem Emission.quote_normalized (emission : Emission source)
    (attached : emission.attachment.entry.flow.input emission.attachment.direction = source.header) :
    emission.quote = ICMPNAT.recompute emission.initialQuote := by
  have target : emission.restoreTarget = IPv4Quote.header emission.initialQuote := by
    rw [Emission.restoreTarget, attached, Emission.initialQuote,
      IPv4Quote.make_header source emission.valid emission.length
        (quoteLength_bounds source emission.valid emission.path).1]
    rfl
  rw [Emission.quote, target, Emission.destinationQuote]
  exact ICMPNAT.patch_roundtrip emission.initialQuote emission.initialQuote_valid _

private theorem checked_checksum_dual_zero (first suffix : List UInt8)
    (even : first.length % 2 = 0) (left right : InternetChecksum.Word)
    (leftValid : InternetChecksum.valid (first ++ InternetChecksum.wordBytes left ++ suffix) = true)
    (rightValid : InternetChecksum.valid (first ++ InternetChecksum.wordBytes right ++ suffix) = true) :
    left = right ∨ left = 0 ∧ right = 65535 ∨ left = 65535 ∧ right = 0 := by
  rw [InternetChecksum.valid_iff] at leftValid rightValid
  simp only [InternetChecksum.sum, InternetChecksum.total_insert first suffix left even] at leftValid
  simp only [InternetChecksum.sum, InternetChecksum.total_insert first suffix right even] at rightValid
  have leftResidue := InternetChecksum.fold_mod (InternetChecksum.total (first ++ suffix) + left.val)
  have rightResidue := InternetChecksum.fold_mod (InternetChecksum.total (first ++ suffix) + right.val)
  rw [leftValid] at leftResidue
  rw [rightValid] at rightResidue
  have leftBound := left.isLt
  have rightBound := right.isLt
  have result : left.val = right.val ∨ left.val = 0 ∧ right.val = 65535 ∨ left.val = 65535 ∧ right.val = 0 := by omega
  rcases result with same | ⟨zero, full⟩ | ⟨full, zero⟩
  · exact .inl (Fin.ext same)
  · exact .inr (.inl ⟨Fin.ext zero, Fin.ext full⟩)
  · exact .inr (.inr ⟨Fin.ext full, Fin.ext zero⟩)

theorem Emission.quote_checksum (emission : Emission source)
    (attached : emission.attachment.entry.flow.input emission.attachment.direction = source.header) :
    emission.quote.checksum = source.ip.checksum ∨
      emission.quote.checksum = 0 ∧ source.ip.checksum = 65535 ∨
      emission.quote.checksum = 65535 ∧ source.ip.checksum = 0 := by
  have exactPacket := emission.quote_restored attached
  have declared : emission.quote.declaredLength = emission.initialQuote.declaredLength := by
    simp only [Emission.quote, Emission.destinationQuote, ICMPNAT.patch_declaredLength]
  have quoteHeader : IPv4Quote.headerBytes emission.quote =
      IPv4.headerBytes source.ip.packet emission.quote.checksum := by
    simp only [IPv4Quote.headerBytes, IPv4Quote.headerPrefix, exactPacket, declared,
      Emission.initialQuote, IPv4Quote.make, IPv4.headerBytes, IPv4.headerPrefix, IPv4.headerSuffix]
  have quoteValid := emission.quote_valid.2.2.2.2
  rw [quoteHeader] at quoteValid
  apply checked_checksum_dual_zero (IPv4.headerPrefix source.ip.packet) (IPv4.headerSuffix source.ip.packet)
    (by simp [IPv4.headerPrefix]) emission.quote.checksum source.ip.checksum quoteValid emission.valid.2.2

theorem cause_some (outcome : MTUForwarding.Outcome source) (kind : ICMP.Kind)
    (reason : cause outcome = some kind) :
    (outcome.disposition = .ttlExpired ∧ kind = .timeExceeded) ∨
      ∃ mtu, outcome.disposition = .mtuExceeded ∧ outcome.selectedMTU = some mtu ∧
        kind = .fragmentationNeeded ⟨mtu.val, mtu.property.2⟩ := by
  cases disposition : outcome.disposition <;> cases selected : outcome.selectedMTU <;>
    simp_all [cause]

private theorem mtu_early_expired (pipeline : MTUForwarding.Pipeline) (input : MTUForwarding.Input)
    (valid : UDPRewrite.SourceValid input.packet) (prepared : ConntrackLifecycle.Prepared input.lifecycle)
    (early : WireForwarding.route pipeline.forwarding input prepared = none ∨ input.packet.ip.packet.ttl.toNat ≤ 1)
    (outcome : MTUForwarding.Outcome input.packet)
    (accepted : MTUForwarding.early pipeline input valid prepared early = .ok outcome)
    (expired : outcome.disposition = .ttlExpired) :
    outcome.state = prepared.state ∧ outcome.output = none ∧ outcome.afterSource = none ∧
      outcome.selectedMTU = none ∧
      (WireForwarding.route pipeline.forwarding input prepared).isSome = true ∧ input.packet.ip.packet.ttl.toNat ≤ 1 := by
  unfold MTUForwarding.early at accepted
  split at accepted
  · cases accepted
  · rename_i parent processed
    cases accepted
    have low : parent.disposition = .ttlExpired := by
      cases disposition : parent.disposition <;>
        simp_all [MTUForwarding.ofDroppedParent, MTUForwarding.parentDisposition]
    obtain ⟨routed, lowTTL, same⟩ := WireForwarding.process_ttlExpired pipeline.forwarding input valid prepared parent processed low
    change parent.state = prepared.state ∧ (none : Option (MTUForwarding.Emission input.packet)) = none ∧ parent.afterSource = none ∧
      (none : Option MTUForwarding.MTU) = none ∧ _
    exact ⟨by rw [same]; rfl, rfl, by rw [same]; rfl, rfl, routed, lowTTL⟩

private theorem mtu_finish_not_expired (pipeline : MTUForwarding.Pipeline) (input : MTUForwarding.Input)
    (valid : UDPRewrite.SourceValid input.packet) (prepared : ConntrackLifecycle.Prepared input.lifecycle)
    (mtu : MTUForwarding.MTU) (allowed : IPv4Fragmentation.Allowed input.packet.ip.packet mtu)
    (outcome : MTUForwarding.Outcome input.packet)
    (accepted : MTUForwarding.finish pipeline input valid prepared mtu allowed = .ok outcome) :
    outcome.disposition ≠ .ttlExpired := by
  unfold MTUForwarding.finish at accepted
  split at accepted
  · cases accepted
  · rename_i parent processed
    cases accepted
    obtain ⟨model, _, same⟩ := WireForwarding.finish_realizes pipeline.forwarding input valid prepared parent processed
    rw [same]
    change MTUForwarding.parentDisposition (WireForwarding.lifecycleDisposition model.disposition) ≠ .ttlExpired
    cases model.disposition <;> decide

private theorem mtu_process_expired (pipeline : MTUForwarding.Pipeline) (input : MTUForwarding.Input)
    (valid : UDPRewrite.SourceValid input.packet) (prepared : ConntrackLifecycle.Prepared input.lifecycle)
    (outcome : MTUForwarding.Outcome input.packet)
    (accepted : MTUForwarding.process pipeline input valid prepared = .ok outcome)
    (expired : outcome.disposition = .ttlExpired) :
    outcome.state = prepared.state ∧ outcome.output = none ∧ outcome.afterSource = none ∧
      outcome.selectedMTU = none ∧
      (WireForwarding.route pipeline.forwarding input prepared).isSome = true ∧ input.packet.ip.packet.ttl.toNat ≤ 1 := by
  unfold MTUForwarding.process at accepted
  split at accepted
  · exact mtu_early_expired pipeline input valid prepared _ outcome accepted expired
  · split at accepted
    · exact mtu_early_expired pipeline input valid prepared _ outcome accepted expired
    · dsimp only at accepted
      split at accepted
      · cases accepted; cases expired
      · exact False.elim (mtu_finish_not_expired pipeline input valid prepared _ _ outcome accepted expired)

theorem step_emission_prepared (pipeline : Pipeline) (before : ConntrackLifecycle.State) (input : Input)
    (identification : InternetChecksum.Word) (outcome : Outcome input.transit.packet)
    (accepted : step pipeline before input identification = .ok outcome)
    (emission : Emission input.transit.packet) (sent : outcome.control.output = some emission) :
    ∃ prepared : ConntrackLifecycle.Prepared input.transit.lifecycle,
      ConntrackLifecycle.prepare before input.transit.lifecycle = .ok prepared ∧
      outcome.transit.attachment = prepared.attachment ∧ outcome.transit.state = prepared.state ∧
      outcome.transit.output = none ∧ outcome.transit.afterSource = none := by
  have ordinary := step_transit pipeline before input identification outcome accepted
  obtain ⟨_, _, valid, prepared, attached, processed⟩ :=
    MTUForwarding.step_prepared pipeline.forwarding before input.transit outcome.transit ordinary
  refine ⟨prepared, attached, mtu_process_attachment pipeline.forwarding input.transit valid prepared outcome.transit processed, ?_⟩
  have facts := step_output pipeline before input identification outcome accepted emission sent
  rcases cause_some outcome.transit emission.kind facts.reason with expired | ⟨mtu, blocked, _⟩
  · exact (mtu_process_expired pipeline.forwarding input.transit valid prepared outcome.transit processed expired.1).imp_right
      (fun result => ⟨result.1, result.2.1⟩)
  · obtain ⟨hop, _, _, _, _, same⟩ :=
      MTUForwarding.process_mtuExceeded pipeline.forwarding input.transit valid prepared outcome.transit processed blocked
    rw [same]
    exact ⟨rfl, rfl, rfl⟩

theorem step_emission_model (pipeline : Pipeline) (before : ConntrackLifecycle.State) (input : Input)
    (identification : InternetChecksum.Word) (outcome : Outcome input.transit.packet)
    (accepted : step pipeline before input identification = .ok outcome)
    (emission : Emission input.transit.packet) (sent : outcome.control.output = some emission) :
    outcome.transit.state.model = before.model := by
  obtain ⟨prepared, attached, _, state, _⟩ :=
    step_emission_prepared pipeline before input identification outcome accepted emission sent
  rw [state]
  exact ConntrackLifecycle.prepare_model before input.transit.lifecycle prepared attached

theorem step_emission_fresh (pipeline : Pipeline) (before : ConntrackLifecycle.State) (input : Input)
    (identification : InternetChecksum.Word) (outcome : Outcome input.transit.packet)
    (accepted : step pipeline before input identification = .ok outcome)
    (emission : Emission input.transit.packet) (sent : outcome.control.output = some emission)
    (fresh : outcome.transit.attachment.fresh = true) : outcome.transit.state = before := by
  obtain ⟨prepared, attached, attachment, state, _⟩ :=
    step_emission_prepared pipeline before input identification outcome accepted emission sent
  rw [attachment] at fresh
  exact state.trans (ConntrackLifecycle.prepare_fresh before input.transit.lifecycle prepared attached fresh).1

theorem step_emission_reply (pipeline : Pipeline) (before : ConntrackLifecycle.State) (input : Input)
    (identification : InternetChecksum.Word) (outcome : Outcome input.transit.packet)
    (accepted : step pipeline before input identification = .ok outcome)
    (emission : Emission input.transit.packet) (sent : outcome.control.output = some emission)
    (reply : outcome.transit.attachment.direction = .reply) :
    outcome.transit.attachment.classification = .established ∧ outcome.transit.attachment.fresh = false ∧
      outcome.transit.state = before.markReply outcome.transit.attachment.entry.flow := by
  obtain ⟨prepared, attached, attachment, state, _⟩ :=
    step_emission_prepared pipeline before input identification outcome accepted emission sent
  rw [attachment] at reply ⊢
  obtain ⟨classification, fresh, marked⟩ :=
    ConntrackLifecycle.prepare_reply before input.transit.lifecycle prepared attached reply
  exact ⟨classification, fresh, state.trans marked⟩

theorem step_emission_cached (pipeline : Pipeline) (before : ConntrackLifecycle.State) (input : Input)
    (identification : InternetChecksum.Word) (outcome : Outcome input.transit.packet)
    (accepted : step pipeline before input identification = .ok outcome)
    (emission : Emission input.transit.packet) (sent : outcome.control.output = some emission)
    (cached : outcome.transit.attachment.fresh = false) (original : outcome.transit.attachment.direction = .original) :
    outcome.transit.state = before := by
  obtain ⟨prepared, attached, attachment, state, _⟩ :=
    step_emission_prepared pipeline before input identification outcome accepted emission sent
  rw [attachment] at cached original
  obtain ⟨_, _, _, _, unchanged⟩ :=
    ConntrackLifecycle.prepare_existing_original before input.transit.lifecycle prepared attached cached original
  exact state.trans unchanged

theorem step_timeExceeded (pipeline : Pipeline) (before : ConntrackLifecycle.State) (input : Input)
    (identification : InternetChecksum.Word) (outcome : Outcome input.transit.packet)
    (accepted : step pipeline before input identification = .ok outcome)
    (emission : Emission input.transit.packet) (sent : outcome.control.output = some emission)
    (kind : emission.kind = .timeExceeded) :
    ∃ prepared : ConntrackLifecycle.Prepared input.transit.lifecycle,
      ConntrackLifecycle.prepare before input.transit.lifecycle = .ok prepared ∧
      (WireForwarding.route pipeline.forwarding.forwarding input.transit prepared).isSome = true ∧
      input.transit.packet.ip.packet.ttl.toNat ≤ 1 ∧ outcome.transit.selectedMTU = none := by
  have facts := step_output pipeline before input identification outcome accepted emission sent
  rcases cause_some outcome.transit emission.kind facts.reason with expired | ⟨mtu, _, _, reason⟩
  · obtain ⟨_, _, valid, prepared, attached, processed⟩ := MTUForwarding.step_prepared pipeline.forwarding before input.transit
      outcome.transit (step_transit pipeline before input identification outcome accepted)
    obtain ⟨_, _, _, selected, routed, low⟩ :=
      mtu_process_expired pipeline.forwarding input.transit valid prepared outcome.transit processed expired.1
    exact ⟨prepared, attached, routed, low, selected⟩
  · rw [kind] at reason
    cases reason

theorem step_fragmentationNeeded (pipeline : Pipeline) (before : ConntrackLifecycle.State) (input : Input)
    (identification : InternetChecksum.Word) (outcome : Outcome input.transit.packet)
    (accepted : step pipeline before input identification = .ok outcome)
    (emission : Emission input.transit.packet) (sent : outcome.control.output = some emission)
    (mtu : InternetChecksum.Word) (kind : emission.kind = .fragmentationNeeded mtu) :
    ∃ prepared : ConntrackLifecycle.Prepared input.transit.lifecycle, ∃ hop,
      ConntrackLifecycle.prepare before input.transit.lifecycle = .ok prepared ∧
      WireForwarding.route pipeline.forwarding.forwarding input.transit prepared = some hop ∧
      1 < input.transit.packet.ip.packet.ttl.toNat ∧ input.transit.packet.ip.packet.dontFragment = true ∧
      (pipeline.forwarding.mtu hop).val < input.transit.packet.ip.packet.wireLength ∧
      mtu.val = (pipeline.forwarding.mtu hop).val := by
  have facts := step_output pipeline before input identification outcome accepted emission sent
  rcases cause_some outcome.transit emission.kind facts.reason with expired | ⟨selected, blocked, selectedEq, reason⟩
  · rw [kind] at expired
    cases expired.2
  · obtain ⟨prepared, hop, attached, routed, live, df, large, same⟩ :=
      MTUForwarding.step_mtuExceeded pipeline.forwarding before input.transit outcome.transit
        (step_transit pipeline before input identification outcome accepted) blocked
    rw [same] at selectedEq
    have selectedSame : pipeline.forwarding.mtu hop = selected := Option.some.inj selectedEq
    have wordSame : mtu = ⟨selected.val, selected.property.2⟩ := ICMP.Kind.fragmentationNeeded.inj (kind.symm.trans reason)
    exact ⟨prepared, hop, attached, routed, live, df, large, by rw [wordSame, selectedSame]⟩

theorem Emission.outer_addresses (emission : Emission source)
    (attached : emission.attachment.entry.flow.input emission.attachment.direction = source.header) :
    emission.packet.source = (if emission.attachment.entry.changesDestination emission.attachment.direction then
      source.ip.packet.destination else emission.path.source) ∧
      emission.packet.destination = source.ip.packet.source := by
  have sourceEq := congrArg Header.source attached
  have destinationEq := congrArg Header.destination attached
  cases direction : emission.attachment.direction <;>
    cases sourceNAT : emission.attachment.entry.sourceNAT <;>
    cases destinationNAT : emission.attachment.entry.destinationNAT <;>
    simp_all [Emission.packet, Emission.afterSource, Emission.beforeSource, Emission.initialHeader,
      addressSource, addressDestination, opposite, NetfilterNAT.Entry.rewrite, NetfilterNAT.Entry.changesSource,
      NetfilterNAT.Entry.changesDestination, FlowNAT.Entry.input, FlowNAT.Entry.output, Header.reverse,
      Rewrite.apply, UDP.DecodedIPv4.header]

end Netlib.Protocol.ICMPForwarding
