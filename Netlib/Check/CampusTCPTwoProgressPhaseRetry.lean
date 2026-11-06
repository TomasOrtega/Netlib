import Netlib.Check.CampusTCPTwoProgressPhaseBase
import Netlib.Check.CampusTCPTwoProgressRetry
import Netlib.Check.CampusTCPTwoProgressTimer
import Netlib.Check.CampusTCPTwoProgressPaths

/-!
# Actual retries funded by retained losses

The current head and timer supply both timeout guards.
Each retry spends one recorded cause in the same actual suffix.
-/

namespace Netlib.Check.CampusTCPTwoProgressPhaseRetry

open Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart
open CampusTCPTwoProgressPhaseBase (Core OriginalTimes emitted)
open CampusTCPTwoProgressSetup (config)

namespace M
export CampusTCPTwoProgressMonitor (Monitor Lane Allowed observe nextDemand timerTarget)
end M
namespace S
export CampusTCPTwoProgressSender (Stage Part Original)
end S
namespace R
export CampusTCPTwoProgressReceiver (Stage)
end R
namespace L
export CampusTCPTwoProgressLossHistory (Head Loss Book Spent Supports History)
end L
namespace Retry
export CampusTCPTwoProgressRetry (HeadRange Retry)
end Retry
namespace F
export CampusTCPTwoProgressMonitorFacts (allowed_iff serves_timeout observe_timeout)
end F

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current : Cut input complete} {sender : Actor} {gateway : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {native : NativeEnv cut gateway initial.gatewayState.session.entry} {quantum allowance : Nat}
variable {monitor : M.Monitor} {sent : S.Stage initial} {received : R.Stage} {actual : Step input}
variable {part : S.Part} {head : Recovery.Outstanding} {rest : List Recovery.Outstanding} {position target : Nat}

def currentHead (core : Core initial native quantum allowance current monitor sent received)
    (selected : Retry.HeadRange sent part head rest) : L.Head initial current part where
  recovery := core.live.senderFlight.recovery
  runtime := core.live.senderFlight.runtime
  entry := head
  tail := rest
  ledger := core.live.senderFlight.ledger.trans selected.ledger
  identity := selected.identity core.live.senderFlight
  position := by cases selected <;> exact congrArg Recovery.Outstanding.start core.live.senderFlight.headFixed
  count := selected.count core.live.senderFlight

private theorem timer_fields (core : Core initial native quantum allowance current monitor sent received)
    (selected : Retry.HeadRange sent part head rest)
    (timer : M.timerTarget core.live.senderFlight.recovery = some target)
    (due : target ≤ core.live.senderFlight.recovery.now) :
    ∃ deadline, core.live.senderFlight.recovery.deadline = some deadline ∧
      deadline ≤ core.live.senderFlight.recovery.now ∧ head.lastAt + core.live.senderFlight.recovery.rto ≤ core.live.senderFlight.recovery.now := by
  obtain ⟨entry, tail, deadline, ledger, armed, _⟩ := CampusTCPTwoProgressTimer.target_some timer
  obtain ⟨sameHead, sameTail⟩ := List.cons.inj ((core.live.senderFlight.ledger.trans selected.ledger).symm.trans ledger)
  subst entry tail
  exact ⟨deadline, armed, CampusTCPTwoProgressTimer.due_fields (core.live.senderFlight.ledger.trans selected.ledger) armed timer due⟩

private theorem timeout_allowed (core : Core initial native quantum allowance current monitor sent received)
    (mode : monitor.mode = .recovery) (ack : monitor.ack = none) (waiting : monitor.waiting = true)
    (timer : M.timerTarget core.live.senderFlight.recovery = some target) (due : target ≤ core.live.senderFlight.recovery.now) :
    M.Allowed (config initial native quantum allowance) current.report.final monitor (.timeout sender true) := by
  have runtime : CampusTCPGapProgressMonitor.senderRecovery (config initial native quantum allowance).toConfig current.report.final =
      some core.live.senderFlight.recovery := by
    change (match current.report.final.connection with
      | .application _ endpoints => (endpoint endpoints sender).recovery
      | _ => none) = _
    rw [current.connection]
    exact core.live.senderFlight.runtime
  have demand := CampusTCPTwoProgressTimer.timerDemand_of_target runtime timer
  rw [ite_eq_right (Nat.not_lt.mpr due)] at demand
  have next : M.nextDemand (config initial native quantum allowance) current.report.final monitor =
      some (.single (.timeout sender)) := by
    simp only [M.nextDemand, mode, ack, waiting, ite_true, demand, Option.map_some]
    rfl
  apply (F.allowed_iff _ _ _ _).mpr
  exact ⟨by rw [mode]; decide, .inl ⟨_, next, (F.serves_timeout _ _).mpr rfl⟩, rfl⟩

def ingressLane (lane : M.Lane) (index packetID : Nat) : M.Lane :=
  ⟨.dataIngress, { lane.refs with dataOutput := some index, dataIngressPacket := some packetID }⟩

private theorem retry_observed (core : Core initial native quantum allowance current monitor sent received)
    (value : Retry.Retry core.live part head rest actual)
    (allowed : M.Allowed (config initial native quantum allowance) current.report.final monitor actual.event) :
    M.observe (config initial native quantum allowance) monitor actual =
      { monitor with
        retry := ingressLane monitor.retry current.report.final.outputs.length value.packetID
        waiting := false
        retries := monitor.retries + 1 } := by
  rw [F.observe_timeout _ _ _ value.move.supported value.move.passed
    (by rw [value.move.beforeEq]; exact allowed) value.facts.event]
  have custody := value.custody
  rw [value.move.final] at custody
  have actor : value.facts.produced.actor = sender := by rw [value.facts.production]; rfl
  have self : (sender == sender) = true := by cases sender <;> rfl
  simp only [CampusTCPTwoProgressMonitor.observeTimeout, CampusTCPTwoProgressMonitor.Lane.ofGap,
    CampusTCPGapProgressMonitor.observeOutput, value.facts.output, actor, config,
    ite_true, self, value.move.beforeEq, custody, CampusTCPTwoProgressMonitor.Lane.toGap,
    CampusTCPTwoProgressMonitorFacts.phase_beq, reduceCtorEq, decide_false, Bool.false_eq_true,
    ite_false, ingressLane]

def spentEntry (core : Core initial native quantum allowance current monitor sent received)
    (value : Retry.Retry core.live part head rest actual)
    (loss : L.Loss initial (config initial native quantum allowance))
    (cause : core.losses.book.cause part = some position) (found : core.losses.book.losses[position]? = some loss) :
    L.Spent initial (config initial native quantum allowance) :=
  core.losses.spentEntry part position loss cause found (currentHead core value.selection) value.move value.facts.event

def updatedBook (core : Core initial native quantum allowance current monitor sent received)
    (value : Retry.Retry core.live part head rest actual)
    (loss : L.Loss initial (config initial native quantum allowance))
    (cause : core.losses.book.cause part = some position) (found : core.losses.book.losses[position]? = some loss) :
    L.Book initial (config initial native quantum allowance) :=
  match part with
  | .lower => { core.losses.book with lower := none, spent := core.losses.book.spent ++ [spentEntry core value loss cause found] }
  | .upper => { core.losses.book with upper := none, spent := core.losses.book.spent ++ [spentEntry core value loss cause found] }

private def consume (core : Core initial native quantum allowance current monitor sent received)
    (value : Retry.Retry core.live part head rest actual)
    (loss : L.Loss initial (config initial native quantum allowance))
    (cause : core.losses.book.cause part = some position) (found : core.losses.book.losses[position]? = some loss)
    (drops : (M.observe (config initial native quantum allowance) monitor actual).drops = monitor.drops)
    (retries : (M.observe (config initial native quantum allowance) monitor actual).retries = monitor.retries + 1) :
    L.History initial (config initial native quantum allowance) value.move.after (M.observe (config initial native quantum allowance) monitor actual) := by
  cases part
  · exact core.losses.consume_lower position loss cause found (currentHead core value.selection) value.move value.facts.event drops retries
  · exact core.losses.consume_upper position loss cause found (currentHead core value.selection) value.move value.facts.event drops retries

private theorem consume_book (core : Core initial native quantum allowance current monitor sent received)
    (value : Retry.Retry core.live part head rest actual)
    (loss : L.Loss initial (config initial native quantum allowance))
    (cause : core.losses.book.cause part = some position) (found : core.losses.book.losses[position]? = some loss)
    (drops : (M.observe (config initial native quantum allowance) monitor actual).drops = monitor.drops)
    (retries : (M.observe (config initial native quantum allowance) monitor actual).retries = monitor.retries + 1) :
    (consume core value loss cause found drops retries).book = updatedBook core value loss cause found := by
  cases part <;> rfl

private theorem core_cast_book (core : Core initial native quantum allowance current before sent received)
    (same : before = after) : (same ▸ core).losses.book = core.losses.book := by cases same; rfl

private theorem history_cast_book
    (history : L.History initial (config initial native quantum allowance) current before)
    (same : before = after) : (same ▸ history).book = history.book := by cases same; rfl

private theorem retry_recovery (core : Core initial native quantum allowance current monitor sent received)
    (value : Retry.Retry core.live part head rest actual) :
    value.next.senderFlight.recovery = Recovery.timeoutState core.live.senderFlight.recovery head rest := by
  have runtime : (endpoint value.move.after.endpoints sender).recovery =
      some (Recovery.timeoutState core.live.senderFlight.recovery head rest) := by
    rw [value.endpointsEq]
    exact value.facts.runtime
  exact Option.some.inj (value.next.senderFlight.runtime.symm.trans runtime)

private theorem duplicate_zero (core : Core initial native quantum allowance current monitor sent received)
    (value : Retry.Retry core.live part head rest actual) : value.next.senderFlight.recovery.duplicateAcks = 0 := by
  rw [retry_recovery core value]
  rfl

structure Retried (core : Core initial native quantum allowance current monitor sent received)
    (part : S.Part) (head : Recovery.Outstanding) (rest : List Recovery.Outstanding) (position : Nat) (actual : Step input) where
  value : Retry.Retry core.live part head rest actual
  loss : L.Loss initial (config initial native quantum allowance)
  cause : core.losses.book.cause part = some position
  found : core.losses.book.losses[position]? = some loss
  support : L.Supports loss part
  earlier : loss.move.after.report.steps <+: current.report.steps
  allowed : M.Allowed (config initial native quantum allowance) current.report.final monitor actual.event
  observed : M.observe (config initial native quantum allowance) monitor actual =
    { monitor with
      retry := ingressLane monitor.retry current.report.final.outputs.length value.packetID
      waiting := false
      retries := monitor.retries + 1 }
  next : Core initial native quantum allowance value.move.after (M.observe (config initial native quantum allowance) monitor actual)
    (sent.retry core.live.senderFlight.recovery.now) received
  book : next.losses.book = updatedBook core value loss cause found
  path : CampusTCPTwoProgressPaths.DataIngress initial value.move.after part
    (M.observe (config initial native quantum allowance) monitor actual).retry

private theorem finish (core : Core initial native quantum allowance current monitor sent received)
    (value : Retry.Retry core.live part head rest actual)
    (cause : core.losses.book.cause part = some position)
    (allowed : M.Allowed (config initial native quantum allowance) current.report.final monitor actual.event) :
    Nonempty (Retried core part head rest position actual) := by
  obtain ⟨loss, found, support, _⟩ := core.losses.valid.cause position cause
  have earlier := core.losses.lossesPast loss (List.mem_of_getElem? found)
  have observed := retry_observed core value allowed
  have drops : (M.observe (config initial native quantum allowance) monitor actual).drops = monitor.drops := by rw [observed]
  have retries : (M.observe (config initial native quantum allowance) monitor actual).retries = monitor.retries + 1 := by rw [observed]
  let joint : CampusTCPTwoProgressState.Live initial value.move.after (sent.retry core.live.senderFlight.recovery.now)
      (monitor.retries + 1) received :=
    { value.next with
      gatewayState := core.live.gatewayState.reframe (value.serviceFrame gateway)
      gatewayWindow := core.live.gatewayWindow }
  have quiet := CampusTCPTwoProgressWriteHistory.timeout_quiet value.facts.localStep value.facts.localEvent
  have emittedEq : emitted initial (sent.retry core.live.senderFlight.recovery.now) = emitted initial sent := by cases sent <;> rfl
  let healthy : Core initial native quantum allowance value.move.after
      { monitor with
        retry := ingressLane monitor.retry current.report.final.outputs.length value.packetID
        waiting := false
        retries := monitor.retries + 1 } (sent.retry core.live.senderFlight.recovery.now) received := {
    live := joint, senderWindow := value.reserve
    originals := (core.originals.retry _).retain_steps value.move.retained
    originalTimes := by cases value.selection <;> exact core.originalTimes
    writer := emittedEq.symm ▸ core.writer.quiet value.facts.localStep value.selectedSteps quiet.1 quiet.2
    losses := observed ▸ consume core value loss cause found drops retries
    lossBound := core.lossBound
    retired := by rw [← value.selection.retired]; exact core.retired
    gatewayAck := core.gatewayAck, covered := core.covered
    peerSettled := core.peerSettled, peerWindow := core.peerWindow
    duplicates := by rw [duplicate_zero core value]; decide
    emptyDuplicate := fun _ => duplicate_zero core value
    deadline := by
      change RecoveryDeadline.Bound value.next.senderFlight.recovery
      rw [retry_recovery core value]
      exact RecoveryDeadline.timeout _ _ _
    estimatorBeforeRetire := fun retired => by
      change value.next.senderFlight.recovery.estimator = _
      rw [retry_recovery core value]
      exact core.estimatorBeforeRetire ((value.selection.retired core.live.senderFlight.recovery.now).trans retired)
    rtoBeforeRetire := fun retired => by
      change value.next.senderFlight.recovery.rto = 2 ^ (monitor.retries + 1) * initial.senderState.idle.recovery.rto
      rw [retry_recovery core value]
      change 2 * core.live.senderFlight.recovery.rto = _
      rw [core.rtoBeforeRetire ((value.selection.retired core.live.senderFlight.recovery.now).trans retired), Nat.pow_succ]
      simp only [Nat.mul_assoc, Nat.mul_left_comm]
    rtoPending := fun _ => by
      change RTOEnvelope.Bound _ _ _ (monitor.retries + 1) value.next.senderFlight.recovery
      rw [retry_recovery core value]
      exact RTOEnvelope.timeout head rest (core.rtoPending (by rw [value.selection.ledger]; simp)) }
  have book : (observed.symm ▸ healthy).losses.book = updatedBook core value loss cause found := by
    rw [core_cast_book]
    exact (history_cast_book _ observed).trans (consume_book core value loss cause found drops retries)
  have path : CampusTCPTwoProgressPaths.DataIngress initial value.move.after part
      (ingressLane monitor.retry current.report.final.outputs.length value.packetID) := {
    output := {
      index := current.report.final.outputs.length, produced := value.facts.produced, stored := value.source
      actor := by rw [value.facts.production]; rfl
      application := by rw [value.facts.production]; trivial
      fields := value.fields }
    packetID := value.packetID
    custody := value.custody
    phase := rfl, outputRef := rfl, packetRef := rfl }
  exact ⟨⟨value, loss, cause, found, support, earlier, allowed, observed, observed.symm ▸ healthy, book,
    by rw [observed]; exact path⟩⟩

theorem lower_at {first : S.Original initial .lower} {second : S.Original initial .upper}
    (core : Core initial native quantum allowance current monitor (.both first second head) received)
    (mode : monitor.mode = .recovery) (ack : monitor.ack = none) (waiting : monitor.waiting = true)
    (budget : allowance ≤ 2) (cause : core.losses.book.cause .lower = some position)
    (timer : M.timerTarget core.live.senderFlight.recovery = some target) (due : target ≤ core.live.senderFlight.recovery.now) :
    ∃ actual, Nonempty (Retried core .lower head [second.entry] position actual) := by
  have credit := Nat.lt_of_lt_of_le (core.timeout_credit .lower position cause) budget
  obtain ⟨deadline, armed, deadlineDue, elapsed⟩ := timer_fields core (.lower first second head) timer due
  obtain ⟨actual, ⟨value⟩⟩ := CampusTCPTwoProgressRetry.lower_at core.live core.senderWindow credit armed deadlineDue elapsed
  exact ⟨actual, finish core value cause (by rw [value.facts.event]; exact timeout_allowed core mode ack waiting timer due)⟩

theorem upper_at {first : S.Original initial .lower} {second : S.Original initial .upper}
    (core : Core initial native quantum allowance current monitor (.tail first second head) received)
    (mode : monitor.mode = .recovery) (ack : monitor.ack = none) (waiting : monitor.waiting = true)
    (budget : allowance ≤ 2) (cause : core.losses.book.cause .upper = some position)
    (timer : M.timerTarget core.live.senderFlight.recovery = some target) (due : target ≤ core.live.senderFlight.recovery.now) :
    ∃ actual, Nonempty (Retried core .upper head [] position actual) := by
  have credit := Nat.lt_of_lt_of_le (core.timeout_credit .upper position cause) budget
  obtain ⟨deadline, armed, deadlineDue, elapsed⟩ := timer_fields core (.upper first second head) timer due
  obtain ⟨actual, ⟨value⟩⟩ := CampusTCPTwoProgressRetry.upper_at core.live core.senderWindow credit armed deadlineDue elapsed
  exact ⟨actual, finish core value cause (by rw [value.facts.event]; exact timeout_allowed core mode ack waiting timer due)⟩

theorem Retried.retries {core : Core initial native quantum allowance current monitor sent received}
    (record : Retried core part head rest position actual) :
    (M.observe (config initial native quantum allowance) monitor actual).retries = monitor.retries + 1 := by rw [record.observed]

theorem Retried.drops {core : Core initial native quantum allowance current monitor sent received}
    (record : Retried core part head rest position actual) :
    (M.observe (config initial native quantum allowance) monitor actual).drops = monitor.drops := by rw [record.observed]

end Netlib.Check.CampusTCPTwoProgressPhaseRetry
