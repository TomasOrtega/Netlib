import Netlib.Protocol.TCP.AdmissionExecution

/-!
# Data admission through either execution mode

Each recovery-only control has an empty payload.
A nonempty payload therefore retains a genuine ordinary admission result.
-/

namespace Netlib.Protocol.TCP.AdmissionStartupRecovery

open Admission

theorem StutterAllowed.empty_payload (allowed : StutterAllowed phase attachment segment observations) :
    segment.payload = [] := by
  cases phase with
  | empty => exact False.elim allowed
  | syn entry clientISS clientWindow clientMSS =>
    rcases allowed.2.2 with ⟨_, control, _⟩ | ⟨_, bare⟩
    · exact control.1.2.2
    · exact bare.1.2.2
  | synAck entry clientISS clientWindow serverISS serverWindow clientMSS serverMSS =>
    rcases allowed.2.2 with ⟨_, control, _⟩ | ⟨_, reply⟩
    · exact control.1.2.2
    · rcases reply with ⟨control, _⟩ | ⟨bare, _, _⟩
      · exact control.1.2.2
      · exact bare.1.2.2
  | data session =>
    rcases allowed.2.2 with ⟨_, control⟩ | ⟨_, control⟩
    · exact control.1.2.2
    · exact control.1.2.2

end Netlib.Protocol.TCP.AdmissionStartupRecovery

namespace Netlib.Protocol.TCP.AdmissionExecution

open Admission

theorem Result.nonempty_legacy (value : Result mode before input lifecycle prepared)
    (nonempty : input.packet.segment.payload ≠ []) :
    Admission.Allowed before.phase prepared.attachment input.packet.segment before.observations := by
  rcases Result.legacy_or_stutter value with legacy | ⟨_, stutter⟩
  · exact legacy
  · exact False.elim (nonempty stutter.empty_payload)

def Result.nonemptyLegacy (value : Result mode before input lifecycle prepared)
    (nonempty : input.packet.segment.payload ≠ []) : Admission.Result before input lifecycle prepared :=
  Result.asLegacy value (Result.nonempty_legacy value nonempty)

theorem Result.nonemptyLegacy_state (value : Result mode before input lifecycle prepared)
    (nonempty : input.packet.segment.payload ≠ []) :
    (Result.nonemptyLegacy value nonempty).state = Result.state value := Result.asLegacy_state value _

theorem Result.nonemptyLegacy_commit (value : Result mode before input lifecycle prepared)
    (nonempty : input.packet.segment.payload ≠ []) (tracker : ConntrackLifecycle.State) :
    commit value tracker = Admission.commit (Result.nonemptyLegacy value nonempty) tracker := Result.asLegacy_commit value _ tracker

end Netlib.Protocol.TCP.AdmissionExecution
