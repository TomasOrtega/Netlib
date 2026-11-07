import Netlib.Check.TCPHandshakeRecoveryEvaluate

/-!
# Actual startup receive records

The selected source is an event-stamped output occurrence.
The receipt keeps the actual checked receiver bytes.
-/

namespace Netlib.Check.TCPHandshakeRecovery

theorem evaluate_receive_receipt (computed : evaluate before index (.receive source bytes path policy) = .ok effect) :
    ∃ receipt, effect.receipt = some receipt ∧ before.source source = some receipt.source ∧
      receipt.source.index = source ∧ receipt.delivery.input.bytes = bytes := by
  exact evaluate_receive_receipt_details computed

theorem Step.receive_receipt (actual : Step active passive)
    (event : actual.event = .receive source bytes path policy) :
    ∃ receipt, actual.result.receipt = some receipt ∧ actual.before.source source = some receipt.source ∧
      receipt.source.index = source ∧ receipt.delivery.input.bytes = bytes ∧ receipt.index = actual.index := by
  have computed := actual.computed
  rw [event] at computed
  obtain ⟨receipt, recorded, selected, index, raw⟩ := evaluate_receive_receipt computed
  exact ⟨receipt, recorded, selected, index, raw, actual.records.receiptIndex receipt recorded⟩

end Netlib.Check.TCPHandshakeRecovery
