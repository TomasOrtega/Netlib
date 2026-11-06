import Netlib.Check.CampusTCPTwoProgressOriginalPath

/-!
# Two original sends from the accepted-write cut

The lower original can wait at ingress or have an actual loss.
The upper send retains that same lower packet or loss.
-/

namespace Netlib.Check.CampusTCPTwoProgressPreparation

open Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart
open CampusTCPTwoProgressPhaseBase (Core)
open CampusTCPTwoProgressSetup (config)

namespace M
export CampusTCPTwoProgressMonitor (Monitor Lane)
end M
namespace S
export CampusTCPTwoProgressSender (Original)
end S
namespace P
export CampusTCPTwoProgressPaths (DataIngress)
end P
namespace Send
export CampusTCPTwoProgressPhaseSend (First Second)
end Send
namespace O
export CampusTCPTwoProgressOriginalPath (source)
end O
namespace L
export CampusTCPTwoProgressLossHistory (Book Loss)
end L

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current : Cut input complete} {sender : Actor} {gateway : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {native : NativeEnv cut gateway initial.gatewayState.session.entry} {quantum allowance : Nat}
variable {monitor : M.Monitor} {actual : Step input} {actor : Actor} {millis : Nat}

structure Written (initial : TwoWriteInitial cut sender gateway lower upper)
    (native : NativeEnv cut gateway initial.gatewayState.session.entry) (quantum allowance : Nat)
    (current : Cut input complete) (monitor : M.Monitor) where
  core : Core initial native quantum allowance current monitor .written .empty
  mode : monitor.mode = .originals
  lowerPending : monitor.lower.phase = .needSend
  upperPending : monitor.upper.phase = .needSend
  ack : monitor.ack = none
  waiting : monitor.waiting = false
  retry : monitor.retry.phase = .done
  retries : monitor.retries = 0

def Written.ofInitial (initial : TwoWriteInitial cut sender gateway lower upper)
    (native : NativeEnv cut gateway initial.gatewayState.session.entry) (quantum allowance : Nat) :
    Written initial native quantum allowance cut .initial :=
  ⟨Core.ofInitial initial native quantum allowance, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

def Written.clock (value : Written initial native quantum allowance current monitor)
    (clocked : CampusTCPTwoProgressClock.Clocked cut current (config initial native quantum allowance)
      monitor actor millis actual)
    (allowed : CampusTCPTwoProgressMonitor.Allowed (config initial native quantum allowance) current.report.final monitor
      (.advanceClock actor millis)) : Written initial native quantum allowance clocked.move.after monitor :=
  { value with core := value.core.clock clocked allowed }

inductive LowerPath (initial : TwoWriteInitial cut sender gateway lower upper)
    (current : Cut input complete) (first : S.Original initial .lower) (lane : M.Lane)
    (book : L.Book initial cfg) where
  | ingress (path : P.DataIngress initial current .lower lane) (produced : path.output.produced = O.source first)
  | lost (phase : lane.phase = .done) (position : Nat) (loss : L.Loss initial cfg)
      (found : book.losses[position]? = some loss) (produced : loss.source = O.source first)
      (cause : book.lower = some position)

structure PendingUpper (initial : TwoWriteInitial cut sender gateway lower upper)
    (native : NativeEnv cut gateway initial.gatewayState.session.entry) (quantum allowance : Nat)
    (current : Cut input complete) (monitor : M.Monitor) (first : S.Original initial .lower) where
  core : Core initial native quantum allowance current monitor (.lower first) .empty
  mode : monitor.mode = .originals
  lowerPath : LowerPath initial current first monitor.lower core.losses.book
  upperPending : monitor.upper.phase = .needSend
  ack : monitor.ack = none
  waiting : monitor.waiting = false
  retry : monitor.retry.phase = .done
  retries : monitor.retries = 0

theorem LowerPath.phase {cfg : CampusTCPTwoProgressMonitor.Config} {first : S.Original initial .lower}
    {lane : M.Lane} {book : L.Book initial cfg} (path : LowerPath initial current first lane book) :
    lane.phase = .dataIngress ∨ lane.phase = .done := by
  cases path with
  | ingress path _ => exact Or.inl path.phase
  | lost phase _ _ _ _ _ => exact Or.inr phase

structure First (before : Written initial native quantum allowance current monitor) (actual : Step input) where
  value : Send.First before.core actual
  next : PendingUpper initial native quantum allowance value.value.facts.move.after
    (CampusTCPTwoProgressMonitor.observe (config initial native quantum allowance) monitor actual) value.value.original
  sameCore : next.core = value.next

theorem first_at (before : Written initial native quantum allowance current monitor) : ∃ actual, Nonempty (First before actual) := by
  obtain ⟨actual, ⟨value⟩⟩ := CampusTCPTwoProgressPhaseSend.first_at before.core before.mode before.lowerPending
  let updated := CampusTCPTwoProgressMonitor.observe (config initial native quantum allowance) monitor actual
  have frames : updated.mode = .originals ∧ updated.upper.phase = .needSend ∧ updated.ack = none ∧
      updated.waiting = false ∧ updated.retry.phase = .done ∧ updated.retries = 0 := by
    dsimp only [updated]
    rw [value.observed]
    exact ⟨before.mode, before.upperPending, before.ack, before.waiting, before.retry, before.retries⟩
  let next : PendingUpper initial native quantum allowance value.value.facts.move.after updated value.value.original := {
    core := value.next
    mode := frames.1
    lowerPath := .ingress value.path (CampusTCPTwoProgressOriginalPath.first_source value)
    upperPending := frames.2.1
    ack := frames.2.2.1
    waiting := frames.2.2.2.1
    retry := frames.2.2.2.2.1
    retries := frames.2.2.2.2.2 }
  exact ⟨actual, ⟨⟨value, next, rfl⟩⟩⟩

variable {first : S.Original initial .lower}

def PendingUpper.clock (value : PendingUpper initial native quantum allowance current monitor first)
    (clocked : CampusTCPTwoProgressClock.Clocked cut current (config initial native quantum allowance)
      monitor actor millis actual)
    (allowed : CampusTCPTwoProgressMonitor.Allowed (config initial native quantum allowance) current.report.final monitor
      (.advanceClock actor millis)) : PendingUpper initial native quantum allowance clocked.move.after monitor first := by
  let core := value.core.clock clocked allowed
  have book : core.losses.book = value.core.losses.book := rfl
  refine ⟨core, value.mode, ?_, value.upperPending, value.ack, value.waiting, value.retry, value.retries⟩
  cases value.lowerPath with
  | ingress path produced => exact .ingress (path.clock clocked.placement) produced
  | lost phase position loss found produced cause =>
    exact .lost phase position loss (by rw [book]; exact found) produced (by rw [book]; exact cause)

structure Both (before : PendingUpper initial native quantum allowance current monitor first) (actual : Step input) where
  value : Send.Second before.core actual
  lowerPath : LowerPath initial value.value.facts.move.after first
    (CampusTCPTwoProgressMonitor.observe (config initial native quantum allowance) monitor actual).lower value.next.losses.book
  upperSource : value.path.output.produced = O.source value.value.original
  mode : (CampusTCPTwoProgressMonitor.observe (config initial native quantum allowance) monitor actual).mode = .originals
  ack : (CampusTCPTwoProgressMonitor.observe (config initial native quantum allowance) monitor actual).ack = none
  waiting : (CampusTCPTwoProgressMonitor.observe (config initial native quantum allowance) monitor actual).waiting = false
  retry : (CampusTCPTwoProgressMonitor.observe (config initial native quantum allowance) monitor actual).retry.phase = .done
  retries : (CampusTCPTwoProgressMonitor.observe (config initial native quantum allowance) monitor actual).retries = 0

theorem second_at (before : PendingUpper initial native quantum allowance current monitor first) :
    ∃ actual, Nonempty (Both before actual) := by
  obtain ⟨actual, ⟨value⟩⟩ := CampusTCPTwoProgressPhaseSend.second_at before.core before.mode before.lowerPath.phase before.upperPending
  have lowerPath : LowerPath initial value.value.facts.move.after first
      (CampusTCPTwoProgressMonitor.observe (config initial native quantum allowance) monitor actual).lower value.next.losses.book := by
    cases before.lowerPath with
    | ingress path produced => exact .ingress (value.retain_lower path) produced
    | lost phase position loss found produced cause =>
      refine .lost (by rw [value.lower_frame]; exact phase) position loss ?_ produced ?_
      · rw [value.book]; exact found
      · rw [value.book]; exact cause
  refine ⟨actual, ⟨⟨value, lowerPath, CampusTCPTwoProgressOriginalPath.second_source value, ?_, ?_, ?_, ?_, ?_⟩⟩⟩
  all_goals rw [value.observed]
  · exact before.mode
  · exact before.ack
  · exact before.waiting
  · exact before.retry
  · exact before.retries

end Netlib.Check.CampusTCPTwoProgressPreparation
