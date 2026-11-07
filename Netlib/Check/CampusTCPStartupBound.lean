import Netlib.Check.CampusTCPStartupZeroLossBound
import Netlib.Check.CampusTCPStartupDriveEntry
import Netlib.Check.CampusTCPStartupDropBound
import Netlib.Theory.FiniteLossProgress

/-!
# Startup completion under the original whole-report loss allowance

The recurrence extends the actual prefix. It never counts expiries as drops.
-/

namespace Netlib.Check.CampusTCPStartupBound

open Packet Protocol Protocol.TCP CampusTCPModel
open CampusTCPRecoveryStartupServiceEnabled (PathsAligned)
open CampusTCPRecoveryStartupReceiveFields (PassiveTarget)

namespace E
export CampusTCPStartupTransferExecution (initial monitorAt actions Serviced)
end E
namespace U
export CampusTCPStartupDriveUntilComplete (Completed)
end U
namespace Z
export CampusTCPStartupZeroLossBound (capacity extension)
end Z
namespace L
export CampusTCPStartupLossInterval (lossAt)
end L
namespace F
export Theory.FiniteLossProgress (horizon base_le_horizon completion)
end F

variable {input : Input} {events : List CampusTCPModel.Event} {whole : Report input events}
variable {config : CampusTCPStartupTransferMonitor.Config} {bound : Nat}

def start (config : CampusTCPStartupTransferMonitor.Config) : Nat := config.startup.preparation.length + 1

def base (config : CampusTCPStartupTransferMonitor.Config) (bound : Nat) : Nat :=
  start config + Z.extension config.transfer.quantum bound (start config)

def completionBound (config : CampusTCPStartupTransferMonitor.Config) (bound : Nat) : Nat :=
  F.horizon (base config bound) (Z.extension config.transfer.quantum bound) config.transfer.lossAllowance

variable (profile : CampusTCPStartupNative.Profile (input.contextFor .primary)
  (beforeService input (CampusTCPSchedule.stateAt input.initial whole.steps config.startup.preparation.length) .primary)
  input.zone (Handshake.outbound input.active config.startup.remote))

theorem complete (prep : CampusTCPStartupProfile.Prep config.startup)
    (actions : E.actions config input.initial (E.initial config) whole.steps = true)
    (paths : PathsAligned config profile) (valid : input.passive.Valid) (target : PassiveTarget profile.entry input.passive)
    (positive : 0 < config.transfer.quantum) (boundPositive : 0 < bound)
    (service : E.Serviced config input.initial (E.initial config) whole.steps bound)
    (within : completionBound config bound ≤ whole.steps.length) :
    U.Completed whole (completionBound config bound) := by
  classical
  have baseOrder : base config bound ≤ completionBound config bound :=
    F.base_le_horizon _ _ _
  have baseWithin := Nat.le_trans baseOrder within
  have capacityPositive : 0 < Z.capacity config.transfer.quantum (start config) := by
    unfold Z.capacity
    omega
  have extensionPositive : 0 < Z.extension config.transfer.quantum bound (start config) := by
    exact Nat.mul_pos capacityPositive boundPositive
  have started : start config < base config bound := by unfold base; omega
  have available : start config < whole.steps.length := Nat.lt_of_lt_of_le started baseWithin
  obtain ⟨initialMonitor, starting, startMode⟩ := CampusTCPStartupDriveEntry.first_drive actions available
  by_cases done : U.Completed whole (completionBound config bound)
  · exact done
  obtain ⟨lastMonitor, ending, _⟩ := CampusTCPStartupDriveUntilComplete.drive_at profile prep actions paths valid target
    (start config) initialMonitor starting startMode (by omega) within done
  have budget : L.lossAt whole (completionBound config bound) ≤ config.transfer.lossAllowance :=
    CampusTCPStartupDropBound.Report.cut_drop_bound whole prep actions within ending
  refine F.completion (base config bound) whole.steps.length (Z.extension config.transfer.quantum bound)
    (L.lossAt whole) (U.Completed whole) ?_ ?_ ?_ ?_ config.transfer.lossAllowance within budget
  · intro first last order inside
    exact CampusTCPStartupLossInterval.monotone whole order inside
  · intro first last order inside closed
    exact closed.mono order
  · intro inside zero
    have count := CampusTCPStartupLossInterval.monotone whole (Nat.le_of_lt started) inside
    have equal : L.lossAt whole (start config) = L.lossAt whole (base config bound) := by omega
    exact CampusTCPStartupZeroLossBound.complete profile prep actions paths valid target positive service
      initialMonitor starting startMode inside equal
  · intro current order inside equal
    by_cases closed : U.Completed whole current
    · exact closed.mono (Nat.le_add_right _ _)
    · obtain ⟨monitor, currentAt, mode⟩ := CampusTCPStartupDriveUntilComplete.drive_at profile prep actions paths valid target
        (start config) initialMonitor starting startMode (by omega) (by omega) closed
      exact CampusTCPStartupZeroLossBound.complete profile prep actions paths valid target positive service
        monitor currentAt mode inside equal.symm

end Netlib.Check.CampusTCPStartupBound
