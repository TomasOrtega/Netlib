import Netlib.Check.CampusTCPStartupSelection

/-!
# The actual preparation, recovery, and endpoint setup

The monitor protects one current path or timer wait.
Only its expiry or a phase advance releases a protected timer.
-/

namespace Netlib.Check.CampusTCPStartupMonitor

open CampusTCPModel

namespace P
export CampusTCPStartupSelection (Protection phaseRank choose retain timerDemand demand allowed)
end P
namespace W
export CampusTCPStartupTransferMonitor (Config)
end W

inductive Setup where
  | clientRecovery | serverRecovery | clientAck | serverAck | write
  deriving BEq, DecidableEq

def Setup.event (config : W.Config) : Setup → Event
  | .clientRecovery => .enableStartupRecovery .client
  | .serverRecovery => .enableStartupRecovery .server
  | .clientAck => .enableAck .client
  | .serverAck => .enableAck .server
  | .write => .write .client (config.transfer.lower ++ config.transfer.upper)

inductive Mode where
  | preparation (index : Nat)
  | opening
  | drive
  | setup (stage : Setup)
  | data
  | invalid
  deriving BEq, DecidableEq

def Setup.after : Setup → Mode
  | .clientRecovery => .setup .serverRecovery
  | .serverRecovery => .setup .clientAck
  | .clientAck => .setup .serverAck
  | .serverAck => .setup .write
  | .write => .data

structure Monitor where
  mode : Mode
  protection : Option P.Protection := none
  deriving BEq, DecidableEq

def initial (config : W.Config) : Monitor :=
  ⟨if config.startup.preparation.isEmpty then .opening else .preparation 0, none⟩

def nextDemand (config : W.Config) (state : State input) (monitor : Monitor) : Option Event :=
  match monitor.mode with
  | .preparation index => config.startup.preparation[index]?
  | .opening => some (.openRecovering config.startup.remote true)
  | .drive => P.demand config state monitor.protection
  | .setup stage => some (stage.event config)
  | .data | .invalid => none

def allowed (config : W.Config) (state : State input) (monitor : Monitor) (event : Event) : Bool :=
  match monitor.mode with
  | .drive => P.allowed config state monitor.protection event
  | .preparation _ | .opening | .setup _ => decide (nextDemand config state monitor = some event)
  | .data | .invalid => false

def expired (quantum : Nat) (state : State input) (held : Option P.Protection) (event : Event) : Bool :=
  match held, event with
  | some (.timer selected), .startupTimeout actor _ true =>
    decide (selected = actor ∧ P.timerDemand quantum state actor = some event)
  | _, _ => false

def advanceProtection (config : W.Config) (monitor : Monitor) (actual : Step input) : Option P.Protection :=
  let held := P.retain actual.before monitor.protection
  if P.phaseRank actual.before < P.phaseRank actual.result.state then P.choose actual.result.state
  else if expired config.transfer.quantum actual.before held actual.event then P.choose actual.result.state
  else P.retain actual.result.state held

def observe (config : W.Config) (monitor : Monitor) (actual : Step input) : Monitor :=
  if actual.result.supported && actual.result.passed && allowed config actual.before monitor actual.event then
    match monitor.mode with
    | .preparation index =>
      ⟨if index + 1 < config.startup.preparation.length then .preparation (index + 1) else .opening, none⟩
    | .opening => ⟨.drive, P.choose actual.result.state⟩
    | .drive =>
      if actual.event = .finishStartup then ⟨.setup .clientRecovery, none⟩
      else ⟨.drive, advanceProtection config monitor actual⟩
    | .setup stage => ⟨stage.after, none⟩
    | .data | .invalid => ⟨.invalid, none⟩
  else ⟨.invalid, none⟩

theorem expired_clock (millis : Nat) : expired quantum state held (.startupClock actor millis) = false := by
  cases held with
  | none => rfl
  | some held => cases held <;> rfl

theorem advanceProtection_timer_clock
    (before : P.retain actual.before monitor.protection = some (.timer actor))
    (event : actual.event = .startupClock selected millis)
    (phase : P.phaseRank actual.result.state ≤ P.phaseRank actual.before)
    (current : CampusTCPStartupSelection.criticalTimer actual.result.state = some actor) :
    advanceProtection config monitor actual = some (.timer actor) := by
  simp only [advanceProtection, before, Nat.not_lt.mpr phase, ↓reduceIte, event, expired_clock]
  exact CampusTCPStartupSelection.retain_timer current

theorem setup_write (accepted : actual.result.supported = true) (passed : actual.result.passed = true)
    (event : actual.event = .write .client (config.transfer.lower ++ config.transfer.upper)) :
    observe config ⟨.setup .write, none⟩ actual = ⟨.data, none⟩ := by
  simp only [observe, accepted, passed, allowed, nextDemand, Setup.event, event, decide_true,
    Bool.and_self, ↓reduceIte, Setup.after]

end Netlib.Check.CampusTCPStartupMonitor
