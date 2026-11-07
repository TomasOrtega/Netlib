import Netlib.Check.CampusTCPTwoTransferMonitor

/-!
# Raw inputs for one startup and transfer monitor

The handoff retains the same state's archive and spent packet losses.
Data uses the inherited timer intervals and the remaining whole-report allowance.
-/

namespace Netlib.Check.CampusTCPStartupTransferConfig

open CampusTCPModel CampusTCPEnabled

namespace W
export CampusTCPTwoTransferMonitor (Config Demand Control serves drainServes)
end W

structure Config where
  lower : List UInt8
  upper : List UInt8
  reverseLower : List UInt8
  reverseUpper : List UInt8
  quantum : Nat
  lossAllowance : Nat
  ingress : Gateway → Actor → I.InterfaceRef
  executionNS : I.NamespaceRef

structure Handoff (active passive : Protocol.TCP.Handshake.Local) where
  archive : RecoveryArchive active passive
  startupDrops : Nat

def Handoff.activeRTO (handoff : Handoff active passive) : Nat := handoff.archive.activeData.rto

def Handoff.passiveRTO (handoff : Handoff active passive) : Nat := handoff.archive.passiveData.rto

def snapshot (state : State input) : Option (Handoff input.active input.passive) :=
  state.recoveryArchive.map (fun archive => ⟨archive, state.custody.dropped⟩)

def Config.data (config : Config) (handoff : Handoff active passive) : W.Config where
  exchange := {
    forward := {
      sender := .client
      bytes := config.lower ++ config.upper
      clientIngress := config.ingress .primary .client
      serverIngress := config.ingress .primary .server
      quantum := config.quantum
      initialRTO := handoff.activeRTO
      initialRemaining := 0
      lossAllowance := config.lossAllowance - handoff.startupDrops
      lowerCount := config.lower.length
      upperCount := config.upper.length }
    reverseLower := config.reverseLower
    reverseUpper := config.reverseUpper
    reverseRTO := handoff.passiveRTO }
  ingress := config.ingress
  executionNS := config.executionNS

def Config.transferServes (config : Config) : W.Control → Event → Bool
  | .pause, .pause | .capture, .stageCheckpoint | .fence, .fencePrimary | .resume, .resume => true
  | .install, .installCheckpoint ns => ns == config.executionNS
  | .clientRoute, .switchRoute .client .standby | .serverRoute, .switchRoute .server .standby => true
  | _, _ => false

def Config.serves (config : Config) : W.Demand → Event → Bool
  | .exchange demand, event => CampusTCPTwoExchangeMonitor.serves demand event
  | .transfer control, event => config.transferServes control event
  | .drain ticket, event => W.drainServes ticket event

variable {input : Input} {state : State input} {handoff : Handoff input.active input.passive}

theorem snapshot_fields (selected : snapshot state = some handoff) :
    state.recoveryArchive = some handoff.archive ∧ handoff.startupDrops = state.custody.dropped := by
  cases present : state.recoveryArchive with
  | none => simp only [snapshot, present, Option.map_none, reduceCtorEq] at selected
  | some archive =>
    simp only [snapshot, present, Option.map_some, Option.some.injEq] at selected
    subst handoff
    exact ⟨rfl, rfl⟩

theorem snapshot_of_archive (state : State input) (present : state.recoveryArchive = some archive) :
    snapshot state = some ⟨archive, state.custody.dropped⟩ := by
  simp only [snapshot, present, Option.map_some]

theorem Config.data_fields (config : Config) (handoff : Handoff active passive) :
    (config.data handoff).exchange.forward.sender = .client ∧
      (config.data handoff).exchange.forward.bytes = config.lower ++ config.upper ∧
      (config.data handoff).exchange.forward.initialRemaining = 0 ∧
      (config.data handoff).exchange.forward.initialRTO = handoff.archive.activeData.rto ∧
      (config.data handoff).exchange.reverseRTO = handoff.archive.passiveData.rto ∧
      (config.data handoff).exchange.forward.lossAllowance = config.lossAllowance - handoff.startupDrops ∧
      (config.data handoff).ingress = config.ingress ∧ (config.data handoff).executionNS = config.executionNS :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem Config.data_coordinates (config : Config) (handoff : Handoff active passive) :
    (config.data handoff).exchange.forward.lowerCount = config.lower.length ∧
      (config.data handoff).exchange.forward.upperCount = config.upper.length ∧
      (config.data handoff).exchange.forward.quantum = config.quantum ∧
      (config.data handoff).exchange.reverseLower = config.reverseLower ∧
      (config.data handoff).exchange.reverseUpper = config.reverseUpper ∧
      (config.data handoff).exchange.forward.clientIngress = config.ingress .primary .client ∧
      (config.data handoff).exchange.forward.serverIngress = config.ingress .primary .server :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem Config.selected_allowance (config : Config) (selected : snapshot state = some handoff) :
    (config.data handoff).exchange.forward.lossAllowance = config.lossAllowance - state.custody.dropped := by
  change config.lossAllowance - handoff.startupDrops = _
  rw [(snapshot_fields selected).2]

theorem Config.data_serves (config : Config) (handoff : Handoff active passive) (demand : W.Demand) (event : Event) :
    W.serves (config.data handoff) demand event = config.serves demand event := by
  cases demand with
  | exchange demand | drain ticket => rfl
  | transfer control => cases control <;> cases event <;> rfl

theorem Config.data_serves_eq (config : Config) (handoff : Handoff active passive) :
    W.serves (config.data handoff) = config.serves := by
  funext demand event
  exact config.data_serves handoff demand event

theorem Config.serves_independent (config : Config) (first second : Handoff active passive)
    (demand : W.Demand) (event : Event) :
    W.serves (config.data first) demand event = W.serves (config.data second) demand event :=
  (config.data_serves first demand event).trans (config.data_serves second demand event).symm

end Netlib.Check.CampusTCPStartupTransferConfig
