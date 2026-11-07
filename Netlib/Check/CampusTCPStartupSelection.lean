import Netlib.Check.CampusTCPStartupJobs
import Netlib.Check.CampusTCPStartupTransferMonitor
import Netlib.Check.CampusTCPStartupClockBounds

/-!
# Protected startup work from the actual current state

A path retains its original output index through the three queue stages.
New retries do not replace a selected live path or timer wait.
-/

namespace Netlib.Check.CampusTCPStartupSelection

open CampusTCPModel

namespace J
export CampusTCPStartupJobs (Job Key inventory)
end J
namespace W
export CampusTCPStartupTransferMonitor (Config)
end W

inductive Protection where
  | path (outputIndex : Nat)
  | timer (actor : Actor)
  deriving BEq, DecidableEq

def phaseRank (state : State input) : Nat :=
  match state.connection with
  | .recovering current =>
    match current.phase with
    | .idle => 0
    | .opened _ => 1
    | .answered _ => 2
    | .acknowledged .. => 3
    | .complete .. => 4
  | _ => 0

def useful (rank : Nat) (job : J.Job input) : Bool :=
  match rank with
  | 1 => decide (job.actor = .client ∧ job.kind = .syn)
  | 2 => decide (job.actor = .server ∧ job.kind = .synAck)
  | 3 => decide ((job.actor = .client ∧ job.kind = .finalAck) ∨
      (job.actor = .server ∧ job.kind = .synAck))
  | 4 => true
  | _ => false

def path (state : State input) (index : Nat) : Option (J.Job input) :=
  (J.inventory state).find? (fun job => decide (job.outputIndex = index))

def criticalPath (state : State input) : Option (J.Job input) :=
  if phaseRank state = 3 then
    ((J.inventory state).find? (fun job => decide (job.actor = .client ∧ job.kind = .finalAck))).or
      ((J.inventory state).find? (useful 3))
  else (J.inventory state).find? (useful (phaseRank state))

def criticalTimer (state : State input) : Option Actor :=
  match phaseRank state with
  | 1 => some .client
  | 2 | 3 => some .server
  | _ => none

def choose (state : State input) : Option Protection :=
  match criticalPath state with
  | some job => some (.path job.outputIndex)
  | none => (criticalTimer state).map Protection.timer

def retain (state : State input) (held : Option Protection) : Option Protection :=
  match held with
  | some (.path index) =>
    match path state index with
    | some job => if useful (phaseRank state) job then held else choose state
    | none => choose state
  | some (.timer actor) =>
    if criticalTimer state = some actor then held else choose state
  | none => choose state

def timer (state : State input) (actor : Actor) : Option Protocol.TCP.HandshakeTimer.State :=
  match state.connection with
  | .recovering current => some (current.timer actor.recoverySide)
  | _ => none

def timerDemand (quantum : Nat) (state : State input) (actor : Actor) : Option Event :=
  match timer state actor with
  | none => none
  | some current =>
    match current.status with
    | .pending flight =>
      if current.now < flight.deadline then
        some (.startupClock actor (min (current.now + quantum) flight.deadline))
      else some (.startupTimeout actor flight.retries true)
    | _ => none

def Job.event (config : W.Config) (job : J.Job input) : Event :=
  match job with
  | .ingress _ index .. => .assign index (config.transfer.ingress .primary job.actor)
  | .ticket item .. => .serve item.id none
  | .link _ index _ emission .. => .deliver index emission.bytes true

def demand (config : W.Config) (state : State input) (held : Option Protection) : Option Event :=
  match retain state held with
  | some (.path index) => (path state index).map (Job.event config)
  | some (.timer actor) => timerDemand config.transfer.quantum state actor
  | none => if phaseRank state = 4 then some .finishStartup else none

def dropAllowed (allowance : Nat) (state : State input) (id : Nat) : Bool :=
  decide (state.custody.dropped < allowance) &&
    state.custody.pending.any (fun item => decide (item.id = id) && item.value.payload.isRecovery)

def jobAllowed (config : W.Config) (state : State input) (event : Event) : Bool :=
  (J.inventory state).any (fun job => decide (Job.event config job = event))

def timeoutAllowed (state : State input) (actor : Actor) (generation : Nat) : Bool :=
  match timer state actor with
  | none => false
  | some current =>
    match current.status with
    | .pending flight => decide (generation = flight.retries ∧ flight.deadline ≤ current.now)
    | _ => false

def clockAllowed (config : W.Config) (state : State input) (held : Option Protection)
    (actor : Actor) (millis : Nat) : Bool :=
  match timer state actor with
  | none => false
  | some current =>
    decide (current.now ≤ millis ∧ millis ≤ current.now + config.transfer.quantum) &&
      match retain state held with
      | some (.timer selected) =>
        if selected = actor then
          decide (millis = current.now) || decide (timerDemand config.transfer.quantum state actor = some (.startupClock actor millis))
        else true
      | _ => true

def allowed (config : W.Config) (state : State input) (held : Option Protection) (event : Event) : Bool :=
  match event with
  | .startupClock actor millis => clockAllowed config state held actor millis
  | .startupTimeout actor generation true => timeoutAllowed state actor generation
  | .dropPacket id => dropAllowed config.transfer.lossAllowance state id
  | .finishStartup => decide (demand config state held = some .finishStartup)
  | _ => jobAllowed config state event

theorem retain_live_path (present : path state index = some job) (relevant : useful (phaseRank state) job = true) :
    retain state (some (.path index)) = some (.path index) := by
  simp only [retain, present, relevant, ↓reduceIte]

theorem retain_timer (current : criticalTimer state = some actor) :
    retain state (some (.timer actor)) = some (.timer actor) := by
  simp only [retain, current, ↓reduceIte]

theorem selected_member (selected : path state index = some job) : job ∈ J.inventory state :=
  List.mem_of_find?_eq_some selected

theorem selected_index (selected : path state index = some job) : job.outputIndex = index :=
  of_decide_eq_true (List.find?_some (p := fun current : J.Job _ => decide (current.outputIndex = index)) selected)

theorem path_same (packets : after.custody.pending = before.custody.pending)
    (work : after.work.pending = before.work.pending) : path after index = path before index := by
  unfold path
  rw [CampusTCPStartupJobs.inventory_same packets work]

theorem clock_guard (permitted : clockAllowed config state held actor millis = true) :
    CampusTCPStartupClockBounds.ClockGuard config.transfer.quantum state (.startupClock actor millis) := by
  cases selected : timer state actor with
  | none => simp only [clockAllowed, selected, Bool.false_eq_true] at permitted
  | some current =>
    simp only [clockAllowed, selected, Bool.and_eq_true] at permitted
    have bounded := (of_decide_eq_true permitted.1).2
    cases connection : state.connection with
    | recovering control =>
      simp only [timer, connection, Option.some.injEq] at selected
      subst current
      simpa only [CampusTCPStartupClockBounds.ClockGuard, connection] using bounded
    | _ => simp only [timer, connection] at selected; cases selected

end Netlib.Check.CampusTCPStartupSelection
