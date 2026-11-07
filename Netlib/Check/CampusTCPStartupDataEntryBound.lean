import Netlib.Check.CampusTCPStartupBound
import Netlib.Check.CampusTCPStartupDrainBound
import Netlib.Check.CampusTCPStartupFirstComplete
import Netlib.Check.CampusTCPStartupQueueBound
import Netlib.Check.CampusTCPStartupSetupBound
import Netlib.Check.CampusTCPStartupActionsProfile

/-!
# One bounded actual startup data entry

Completion, queue drain, and five setup steps use the same whole service check.
-/

namespace Netlib.Check.CampusTCPStartupDataEntryBound

open Packet Protocol Protocol.TCP CampusTCPModel
open CampusTCPRecoveryStartupServiceEnabled (PathsAligned)
open CampusTCPRecoveryStartupReceiveFields (PassiveTarget)

namespace E
export CampusTCPStartupTransferExecution (initial actions Serviced check check_correct)
end E
namespace B
export CampusTCPStartupBound (start base completionBound)
end B
namespace Z
export CampusTCPStartupZeroLossBound (capacity extension)
end Z

variable {input : Input} {events : List CampusTCPModel.Event} {whole : Report input events}
variable {config : CampusTCPStartupTransferMonitor.Config} {bound : Nat}

def setupSlots (config : CampusTCPStartupTransferMonitor.Config) (bound : Nat) : Nat :=
  let completed := B.completionBound config bound
  completed + (6 * completed + 6) * bound

theorem completion_le_setup : B.completionBound config bound ≤ setupSlots config bound := by
  exact Nat.le_add_right _ _

theorem start_lt_completion (positive : 0 < bound) : B.start config < B.completionBound config bound := by
  have capacityPositive : 0 < Z.capacity config.transfer.quantum (B.start config) := by
    unfold Z.capacity
    omega
  have extra : 0 < Z.extension config.transfer.quantum bound (B.start config) := Nat.mul_pos capacityPositive positive
  have first : B.start config < B.base config bound := by unfold B.base; omega
  exact Nat.lt_of_lt_of_le first (Theory.FiniteLossProgress.base_le_horizon _ _ _)

theorem drain_horizon_le (before : start ≤ completed) (potential : pending ≤ 6 * completed) :
    start + (pending + 1) * bound ≤ completed + (6 * completed + 6) * bound := by
  have product := Nat.mul_le_mul_right bound (by omega : pending + 1 ≤ 6 * completed + 6)
  omega

theorem entry_horizon_le (positive : 0 < bound) (before : start ≤ completed) (potential : pending ≤ 6 * completed)
    (finish : slot < start + (pending + 1) * bound) :
    slot + 6 ≤ completed + (6 * completed + 6) * bound := by
  have product := Nat.mul_le_mul_right bound (by omega : pending + 1 ≤ 6 * completed + 1)
  have reserve := Nat.mul_le_mul_left 5 (by omega : 1 ≤ bound)
  simp only [Nat.mul_one] at reserve
  have split : (6 * completed + 6) * bound = (6 * completed + 1) * bound + 5 * bound := by
    have parts : 6 * completed + 6 = (6 * completed + 1) + 5 := by omega
    rw [parts, Nat.add_mul]
  omega

variable (profile : CampusTCPStartupNative.Profile (input.contextFor .primary)
  (beforeService input (CampusTCPSchedule.stateAt input.initial whole.steps config.startup.preparation.length) .primary)
  input.zone (Handshake.outbound input.active config.startup.remote))

theorem entry_by (prep : CampusTCPStartupProfile.Prep config.startup)
    (actions : E.actions config input.initial (E.initial config) whole.steps = true)
    (paths : PathsAligned config profile) (valid : input.passive.Valid) (target : PassiveTarget profile.entry input.passive)
    (positive : 0 < config.transfer.quantum) (boundPositive : 0 < bound)
    (service : E.Serviced config input.initial (E.initial config) whole.steps bound)
    (enough : setupSlots config bound < whole.steps.length) :
    ∃ slot, ∃ _entry : CampusTCPStartupEntry.Entry config whole slot, slot + 1 ≤ setupSlots config bound := by
  let completed := B.completionBound config bound
  have completedWithin : completed ≤ whole.steps.length := Nat.le_trans completion_le_setup (Nat.le_of_lt enough)
  have complete := CampusTCPStartupBound.complete profile prep actions paths valid target positive boundPositive service completedWithin
  have firstAvailable : config.startup.preparation.length + 1 < whole.steps.length :=
    Nat.lt_of_lt_of_le (start_lt_completion (config := config) boundPositive) completedWithin
  obtain ⟨found⟩ := CampusTCPStartupFirstComplete.locate profile prep actions paths valid target firstAvailable completedWithin complete
  let current := CampusTCPSchedule.Report.cut whole found.slot found.within
  have nocopy := CampusTCPStartupActionsProfile.Report.no_copy whole prep actions
  have currentNocopy : ∀ actual ∈ current.steps, ∀ id, actual.event ≠ .copyPacket id := by
    intro actual member id
    exact nocopy actual (List.mem_of_mem_take member) id
  have length : current.steps.length = found.slot := by
    simp only [current, CampusTCPSchedule.Report.cut, List.length_take, Nat.min_eq_left found.within]
  have pending : CampusTCPStartupDrainBound.potentialAt whole found.slot ≤ 6 * completed := by
    have queues := CampusTCPStartupQueueBound.Report.potential_le_steps current currentNocopy
    rw [length] at queues
    exact Nat.le_trans queues (Nat.mul_le_mul_left 6 found.bound)
  have drainDeadline := drain_horizon_le found.bound pending (bound := bound)
  have drainAvailable : found.slot + (CampusTCPStartupDrainBound.potentialAt whole found.slot + 1) * bound ≤ whole.steps.length :=
    Nat.le_trans drainDeadline (Nat.le_of_lt enough)
  obtain ⟨finish⟩ := CampusTCPStartupDrainBound.finish_by profile prep actions service paths valid target
    found.monitor found.ending found.drive found.phase drainAvailable
  have entryBound := entry_horizon_le boundPositive found.bound pending finish.bound
  have setupAvailable : finish.slot + 1 + 5 < whole.steps.length := by
    change finish.slot + 6 ≤ setupSlots config bound at entryBound
    omega
  obtain ⟨setup⟩ := CampusTCPStartupSetupBound.enter actions setupAvailable ⟨.setup .clientRecovery, none⟩ finish.setup rfl
  exact ⟨finish.slot + 5, setup.entry, by change finish.slot + 6 ≤ setupSlots config bound at entryBound; omega⟩

theorem entry_by_checked (prep : CampusTCPStartupProfile.Prep config.startup)
    (actions : E.actions config input.initial (E.initial config) whole.steps = true)
    (checked : E.check config input.initial (E.initial config) whole.steps bound = true)
    (paths : PathsAligned config profile) (valid : input.passive.Valid) (target : PassiveTarget profile.entry input.passive)
    (positive : 0 < config.transfer.quantum) (boundPositive : 0 < bound)
    (enough : setupSlots config bound < whole.steps.length) :
    ∃ slot, ∃ _entry : CampusTCPStartupEntry.Entry config whole slot, slot + 1 ≤ setupSlots config bound :=
  entry_by profile prep actions paths valid target positive boundPositive
    ((E.check_correct _ _ _ _ _).mp checked) enough

end Netlib.Check.CampusTCPStartupDataEntryBound
