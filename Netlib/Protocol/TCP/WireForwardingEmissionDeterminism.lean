import Netlib.Protocol.TCP.WireForwarding

/-!
# Deterministic bytes for the same TCP rewrite

Generated packets and their encoding equations determine the whole emission.
-/

namespace Netlib.Protocol.TCP.WireForwarding

open Packet

variable {input firstInput secondInput : TCP.DecodedIPv4}

theorem Emission.generated_bytes (emission : Emission input) (valid : TCPRewrite.SourceValid input) :
    emission.bytes = TCPRewrite.wireBytes input emission.target (decrementTTL input) := by
  have encoded := emission.rewritten.encoded
  rw [emission.rewritten.generated] at encoded
  exact Except.ok.inj (encoded.symm.trans
    (TCPRewrite.transformed_encoded input emission.target (decrementTTL input) valid emission.transport))

theorem Source.emission_bytes (source : Source) (emission : Emission source.packet) :
    emission.bytes = TCPRewrite.wireBytes source.packet emission.target (decrementTTL source.packet) :=
  emission.generated_bytes source.valid

theorem Emission.decoded_eq_of_target (first second : Emission input) (same : first.target = second.target) :
    first.decoded = second.decoded := by
  change first.rewritten.packet = second.rewritten.packet
  rw [first.rewritten.generated, second.rewritten.generated, same]

theorem Emission.bytes_eq_of_target (first second : Emission input) (same : first.target = second.target) :
    first.bytes = second.bytes := by
  have encoded := first.encoded
  rw [first.decoded_eq_of_target second same] at encoded
  exact Except.ok.inj (encoded.symm.trans second.encoded)

theorem Emission.eq_of_target (first second : Emission input) (same : first.target = second.target) : first = second := by
  rcases first with ⟨firstTarget, ⟨firstPacket, firstBytes, firstGenerated, firstEncoded⟩⟩
  rcases second with ⟨secondTarget, ⟨secondPacket, secondBytes, secondGenerated, secondEncoded⟩⟩
  change firstTarget = secondTarget at same
  subst secondTarget
  have packetEq : firstPacket = secondPacket := firstGenerated.trans secondGenerated.symm
  cases packetEq
  have bytesEq : firstBytes = secondBytes := Except.ok.inj (firstEncoded.symm.trans secondEncoded)
  cases bytesEq
  rfl

theorem Emission.header_eq_of_target (first second : Emission input) (same : first.target = second.target) :
    first.decoded.header = second.decoded.header :=
  congrArg TCP.DecodedIPv4.header (first.decoded_eq_of_target second same)

theorem Emission.segment_eq_of_target (first second : Emission input) (same : first.target = second.target) :
    first.decoded.segment = second.decoded.segment :=
  congrArg TCP.DecodedIPv4.segment (first.decoded_eq_of_target second same)

theorem Emission.asInput_eq_of_target (first second : Emission input) (same : first.target = second.target) :
    first.asInput = second.asInput :=
  congrArg Emission.asInput (first.eq_of_target second same)

theorem Emission.fields_eq_of_input_target (first : Emission firstInput) (second : Emission secondInput)
    (inputEq : firstInput = secondInput) (targetEq : first.target = second.target) :
    first.decoded = second.decoded ∧ first.bytes = second.bytes ∧
      first.decoded.header = second.decoded.header ∧ first.decoded.segment = second.decoded.segment ∧
      first.asInput = second.asInput := by
  subst secondInput
  exact ⟨first.decoded_eq_of_target second targetEq, first.bytes_eq_of_target second targetEq,
    first.header_eq_of_target second targetEq, first.segment_eq_of_target second targetEq,
    first.asInput_eq_of_target second targetEq⟩

end Netlib.Protocol.TCP.WireForwarding
