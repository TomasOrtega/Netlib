import Netlib.Check.CampusTCPStartupJobs
import Netlib.Check.CampusTCPCustodyFacts
import Netlib.Check.CampusTCPStartupSelection

/-!
# One live path for each actual endpoint output

Without packet copies, assignment and service transfer the same output index.
New endpoint emissions use the fresh output-list index.
-/

namespace Netlib.Check.CampusTCPStartupJobUnique

open CampusTCPModel CampusTCPStartupJobs

variable {input : Input} {tag : Nat}

def transitIndex : Transit input → Nat
  | .ingress index _ => index
  | .link _ served _ _ => served.ticket.value.outputIndex

def packetIndex (item : PacketItem input) : Nat := transitIndex item.value.payload

def ticketIndex (item : TicketItem input) : Nat := item.value.outputIndex

def outputIndices (state : State input) : List Nat :=
  state.custody.pending.map packetIndex ++ state.work.pending.map ticketIndex

private def tagged (value tag : Nat) : Nat := if value == tag then 1 else 0
private def packetCount (custody : Custody input) (tag : Nat) : Nat := (custody.pending.map packetIndex).count tag
private def workCount (work : Work.State (Ticket input.active input.passive)) (tag : Nat) : Nat :=
  (work.pending.map ticketIndex).count tag
private def serviceCount (effect : Effect input) (tag : Nat) : Nat :=
  match effect.service with | none => 0 | some served => tagged served.ticket.value.outputIndex tag
private def freshCount (before : State input) (effect : Effect input) (tag : Nat) : Nat :=
  match effect.output with | none => 0 | some _ => tagged before.outputs.length tag
private def assigned : Event → Nat → Nat
  | .assign index _, tag => tagged index tag
  | _, _ => 0

def count (state : State input) (tag : Nat) : Nat := packetCount state.custody tag + workCount state.work tag

structure Linear (state : State input) : Prop where
  unique : ∀ tag, count state tag ≤ 1
  past : ∀ tag, 0 < count state tag → tag < state.outputs.length

private def Quiet (before : State input) (effect : Effect input) : Prop :=
  effect.state.work = before.work ∧ effect.service = none

private theorem quiet_bound (quiet : Quiet before effect) :
    workCount effect.state.work tag + serviceCount effect tag ≤ workCount before.work tag + assigned event tag := by
  rw [quiet.1]
  simp only [serviceCount, quiet.2, Nat.add_zero]
  omega

private theorem startup_quiet (computed : startup input before event = .ok effect) : Quiet before effect := by
  unfold startup at computed
  repeat' first
    | (solve | cases computed; exact ⟨rfl, rfl⟩)
    | (solve | cases computed)
    | (split at computed)
    | (dsimp only [pure, Except.pure] at computed)

private theorem application_quiet (computed : applyApplication input before actor event = .ok effect) : Quiet before effect := by
  unfold applyApplication at computed
  repeat' first
    | (solve | cases computed; exact ⟨rfl, rfl⟩)
    | (solve | cases computed)
    | (split at computed)
    | (dsimp only [parsed, Except.mapError, bind, Except.bind, pure, Except.pure] at computed)

private theorem recovery_quiet (computed : runRecovery input before event = .ok effect) : Quiet before effect := by
  unfold runRecovery at computed
  split at computed
  · cases computed; exact ⟨rfl, rfl⟩
  · cases computed; exact ⟨rfl, rfl⟩
  · split at computed
    · cases computed
    · rename_i current connected result evaluated
      cases result with
      | mk state decision output receipt application =>
        cases output <;> simp only [pure, Except.pure, Except.ok.injEq] at computed
        all_goals subst effect; exact ⟨rfl, rfl⟩

private theorem open_quiet (computed : openRecovering input before remote policy = .ok effect) : Quiet before effect := by
  unfold openRecovering at computed
  repeat' first
    | (solve | simpa only [Quiet] using (recovery_quiet computed))
    | (solve | cases computed; exact ⟨rfl, rfl⟩)
    | (solve | cases computed)
    | (split at computed)
    | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)

private theorem finish_quiet (computed : finishStartup input before = .ok effect) : Quiet before effect := by
  unfold finishStartup at computed
  repeat' first
    | (solve | cases computed; exact ⟨rfl, rfl⟩)
    | (solve | cases computed)
    | (split at computed)
    | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)

private theorem ack_quiet (computed : enableAck input before actor = .ok effect) : Quiet before effect := by
  unfold enableAck at computed
  repeat' first
    | (solve | exact application_quiet computed)
    | (solve | cases computed; exact ⟨rfl, rfl⟩)
    | (solve | cases computed)
    | (split at computed)
    | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)

private theorem enable_quiet (computed : enableStartupRecovery input before actor = .ok effect) : Quiet before effect := by
  unfold enableStartupRecovery at computed
  split at computed
  · cases computed; exact ⟨rfl, rfl⟩
  · exact application_quiet computed

private theorem process_work (computed : processCore input before event = .ok effect) :
    workCount effect.state.work tag + serviceCount effect tag ≤ workCount before.work tag + assigned event tag := by
  cases event with
  | «open» remote policy => exact quiet_bound (startup_quiet computed)
  | openRecovering remote policy => exact quiet_bound (open_quiet computed)
  | startupClock actor millis | startupTimeout actor generation policy => exact quiet_bound (recovery_quiet computed)
  | finishStartup => exact quiet_bound (finish_quiet computed)
  | enableStartupRecovery actor => exact quiet_bound (enable_quiet computed)
  | write actor bytes | send actor count policy | read actor count | emitAck actor policy
  | enableRecovery actor | advanceClock actor millis | timeout actor policy | dispatchAck actor policy =>
    exact quiet_bound (application_quiet computed)
  | enableAck actor => exact quiet_bound (ack_quiet computed)
  | copyPacket id | dropPacket id =>
    cases computed
    exact quiet_bound ⟨rfl, rfl⟩
  | authentication index =>
    simp only [processCore] at computed
    repeat' first
      | (solve | cases computed; exact quiet_bound ⟨rfl, rfl⟩)
      | (solve | cases computed)
      | (split at computed)
      | (dsimp only [pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at computed)
  | install id | stage id | installGuard id | installAt gateway id | stageAt gateway id | installGuardAt gateway id =>
    simp only [processCore, installConfiguration, stageAttachment, installIngress] at computed
    repeat' first
      | (solve | cases computed; cases gateway <;> exact quiet_bound ⟨rfl, rfl⟩)
      | (solve | cases computed; exact quiet_bound ⟨rfl, rfl⟩)
      | (solve | cases computed)
      | (split at computed)
      | (dsimp only [parsed, Except.mapError, bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at computed)
  | pause | stageCheckpoint | installCheckpoint ns | switchRoute actor gateway | fencePrimary | resume =>
    simp only [processCore, transferControl] at computed
    repeat' first
      | (solve | cases computed; exact quiet_bound ⟨rfl, rfl⟩)
      | (solve | cases computed)
      | (split at computed)
      | (dsimp only [Except.mapError, bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at computed)
  | assign index ingress =>
    simp only [processCore] at computed
    repeat' first
      | (solve | cases computed; simp only [assigned, workCount, serviceCount, Work.enqueue,
          List.map_append, List.count_append, List.map_cons, List.map_nil, List.count_cons,
          List.count_nil, Theory.Outstanding.newItem, ticketIndex, tagged, Nat.zero_add, Nat.add_zero, Nat.le_refl])
      | (solve | cases computed)
      | (split at computed)
      | (dsimp only [CampusTCPModel.get, bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at computed)
  | serve id observed =>
    simp only [processCore] at computed
    cases completed : Work.complete before.work id with
    | error reason => simp only [completed, Except.mapError, bind, Except.bind] at computed; cases computed
    | ok value =>
      have length := (value.pendingPerm.map ticketIndex).count_eq tag
      simp only [List.map_cons, List.count_cons] at length
      change workCount before.work tag = workCount value.state tag + tagged value.item.value.outputIndex tag at length
      simp only [completed, Except.mapError, bind, Except.bind] at computed
      repeat' first
        | (solve | cases computed; exact quiet_bound ⟨rfl, rfl⟩)
        | (solve | cases computed; change workCount value.state tag + tagged value.item.value.outputIndex tag ≤ workCount before.work tag + 0; omega)
        | (solve | cases computed)
        | (split at computed)
        | (dsimp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at computed)
  | deliver index bytes policy =>
    simp only [processCore] at computed
    repeat' first
      | (solve |
        have quiet := startup_quiet (input := input) (before := before) (by assumption)
        cases computed
        exact quiet_bound ⟨quiet.1, quiet.2⟩)
      | (solve |
        have quiet := application_quiet (input := input) (before := before) (by assumption)
        cases computed
        exact quiet_bound ⟨quiet.1, quiet.2⟩)
      | (solve |
        have quiet := recovery_quiet (input := input) (before := before) (by assumption)
        cases computed
        exact quiet_bound ⟨quiet.1, quiet.2⟩)
      | (solve | cases computed)
      | (split at computed)
      | (dsimp only [CampusTCPModel.get, parsed, Except.mapError, bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at computed)



private theorem resolved_count {custody : Custody input} (resolved : Theory.PacketCustody.Resolved custody packetID disposition) :
    packetCount custody tag = packetCount resolved.state tag + tagged (packetIndex resolved.item) tag := by
  have perm : (custody.pending.map packetIndex).Perm
      (packetIndex resolved.item :: resolved.state.pending.map packetIndex) := by
    simpa only [Theory.PacketCustody.State.pending, Theory.PacketCustody.Resolved.state,
      Theory.PacketCustody.Resolved.item, List.map_cons] using resolved.completed.pendingPerm.map packetIndex
  have counted := perm.count_eq tag
  simpa only [packetCount, List.count_cons, tagged] using counted

private theorem prepared_count (actual : Step input) (history : Theory.PacketCustody.History actual.before.custody)
    (nocopy : ∀ id, actual.event ≠ .copyPacket id)
    (prepared : prepareCustody actual.before actual.event = .ok custody) :
    packetCount custody tag + assigned actual.event tag ≤ packetCount actual.before.custody tag := by
  cases event : actual.event with
  | assign index ingress =>
    obtain ⟨id, resolved, selected, computed, predicate, _⟩ := CampusTCPCustodyFacts.Step.assign actual index ingress event history
    have equal : custody = resolved.state := by
      simpa only [event, prepareCustody, selected, computed, Except.mapError, bind, Except.bind,
        pure, Except.pure, Except.ok.injEq] using prepared.symm
    obtain ⟨produced, payload⟩ := CampusTCPCustodyFacts.ingress_stage _ _ predicate
    have count := resolved_count (tag := tag) resolved
    rw [packetIndex, payload] at count
    change packetCount actual.before.custody tag = packetCount resolved.state tag + tagged index tag at count
    rw [equal]
    simp only [assigned]
    omega
  | deliver index bytes policy =>
    obtain ⟨id, resolved, selected, computed, predicate, bytesEq, _⟩ := CampusTCPCustodyFacts.Step.deliver actual index bytes policy event history
    have equal : custody = resolved.state := by
      simpa only [event, prepareCustody, selected, computed, Except.mapError, bind, Except.bind,
        bytesEq, ↓reduceIte, pure, Except.pure, Except.ok.injEq] using prepared.symm
    have count := resolved_count (tag := tag) resolved
    rw [equal]
    simp only [assigned]
    omega
  | dropPacket id =>
    obtain ⟨resolved, computed, _⟩ := CampusTCPCustodyFacts.Step.drop actual id event
    have equal : custody = resolved.state := by
      simpa only [event, prepareCustody, computed, Except.mapError, bind, Except.bind,
        pure, Except.pure, Except.ok.injEq] using prepared.symm
    have count := resolved_count (tag := tag) resolved
    rw [equal]
    simp only [assigned]
    omega
  | copyPacket id => exact False.elim (nocopy id event)
  | _ =>
    have equal : custody = actual.before.custody := by
      simpa only [event, prepareCustody, pure, Except.pure, Except.ok.injEq] using prepared.symm
    simp only [equal, assigned, Nat.add_zero, Nat.le_refl]

private theorem mint_count (custody : Custody input) (payload : Transit input) (tag : Nat) :
    packetCount (Theory.PacketCustody.mint custody payload) tag =
      packetCount custody tag + tagged (transitIndex payload) tag := by
  simp only [packetCount, Theory.PacketCustody.mint_pending, List.map_append, List.count_append,
    List.map_cons, List.map_nil, List.count_cons, List.count_nil, packetIndex,
    Theory.PacketCustody.newItem, Theory.Outstanding.newItem, tagged, Nat.zero_add]

private theorem finish_count (before : State input) (effect : Effect input) (custody : Custody input) :
    packetCount (finishCustody before effect custody) tag ≤
      packetCount custody tag + freshCount before effect tag + serviceCount effect tag := by
  cases output : effect.output <;> cases service : effect.service <;>
    simp only [finishCustody, output, service, freshCount, serviceCount]
  all_goals repeat' first
    | (solve | omega)
    | (solve | simp only [mint_count, transitIndex]; omega)
    | split

private theorem step_count_bound (actual : Step input) (history : Theory.PacketCustody.History actual.before.custody)
    (nocopy : ∀ id, actual.event ≠ .copyPacket id) (tag : Nat) :
    count actual.result.state tag ≤ count actual.before tag + freshCount actual.before actual.result tag := by
  obtain ⟨effect, custody, computed, prepared, final⟩ := actual.transaction
  have work := process_work (tag := tag) computed
  have packets := prepared_count (tag := tag) actual history nocopy prepared
  have finished := finish_count (tag := tag) actual.before effect custody
  rw [final]
  change packetCount (finishCustody actual.before effect custody) tag + workCount effect.state.work tag ≤
    packetCount actual.before.custody tag + workCount actual.before.work tag + freshCount actual.before effect tag
  omega


theorem Linear.initial : Linear input.initial := by
  constructor
  · intro tag
    simp only [count, packetCount, workCount, Input.initial, Theory.PacketCustody.State.initial,
      Theory.PacketCustody.State.pending, Theory.Outstanding.State.initial, List.map_nil,
      List.count_nil, Nat.add_zero, Nat.zero_le]
  · intro tag positive
    simp only [count, packetCount, workCount, Input.initial, Theory.PacketCustody.State.initial,
      Theory.PacketCustody.State.pending, Theory.Outstanding.State.initial, List.map_nil,
      List.count_nil, Nat.add_zero, Nat.lt_irrefl] at positive

theorem Linear.step {actual : Step input} (prior : Linear actual.before) (history : Theory.PacketCustody.History actual.before.custody)
    (nocopy : ∀ id, actual.event ≠ .copyPacket id) : Linear actual.result.state := by
  constructor
  · intro tag
    have bound := step_count_bound actual history nocopy tag
    have unique := prior.unique tag
    cases output : actual.result.output with
    | none => simp only [freshCount, output] at bound; omega
    | some produced =>
      simp only [freshCount, output] at bound
      by_cases same : actual.before.outputs.length = tag
      · have empty : count actual.before tag = 0 := by
          by_cases positive : 0 < count actual.before tag
          · have past := prior.past tag positive
            omega
          · omega
        simp only [tagged, beq_iff_eq, same, ↓reduceIte] at bound
        omega
      · simp only [tagged, beq_iff_eq, same, ↓reduceIte] at bound
        omega
  · intro tag positive
    have bound := step_count_bound actual history nocopy tag
    have outputs := congrArg List.length (CampusTCPOrigins.output_history actual)
    cases output : actual.result.output with
    | none =>
      simp only [freshCount, output] at bound
      simp only [output, Option.toList_none, List.length_append, List.length_nil, Nat.add_zero] at outputs
      have oldPositive : 0 < count actual.before tag := by omega
      have past := prior.past tag oldPositive
      omega
    | some produced =>
      simp only [freshCount, output] at bound
      simp only [output, Option.toList_some, List.length_append, List.length_cons, List.length_nil] at outputs
      by_cases same : actual.before.outputs.length = tag
      · omega
      · simp only [tagged, beq_iff_eq, same, ↓reduceIte] at bound
        have oldPositive : 0 < count actual.before tag := by omega
        have past := prior.past tag oldPositive
        omega

theorem Trace.linear (trace : Trace input initial events steps final remaining)
    (prior : Linear initial) (history : Theory.PacketCustody.History initial.custody)
    (nocopy : ∀ actual ∈ steps, ∀ id, actual.event ≠ .copyPacket id) : Linear final := by
  induction trace with
  | done => exact prior
  | stop head blocked rest => exact prior.step history (nocopy head (by simp))
  | next head supported rest ih =>
    exact ih (prior.step history (nocopy head (by simp)))
      (CampusTCPCustodyFacts.Step.history head history)
      (fun actual member => nocopy actual (List.mem_cons_of_mem _ member))

theorem Report.linear (report : Report input events)
    (nocopy : ∀ actual ∈ report.steps, ∀ id, actual.event ≠ .copyPacket id) : Linear report.final :=
  Trace.linear report.trace Linear.initial .initial nocopy

theorem count_eq (state : State input) (tag : Nat) : count state tag = (outputIndices state).count tag := by
  simp only [count, outputIndices, packetCount, workCount, List.count_append]

private theorem nodup_of_counts (values : List Nat) (counts : ∀ tag, values.count tag ≤ 1) : values.Nodup := by
  induction values with
  | nil => exact .nil
  | cons head tail ih =>
    have current := counts head
    simp only [List.count_cons, beq_self_eq_true, ↓reduceIte] at current
    have absent : head ∉ tail := by
      intro member
      have positive := List.count_pos_iff.mpr member
      omega
    apply List.nodup_cons.mpr
    refine ⟨absent, ih ?_⟩
    intro tag
    have bound := counts tag
    simp only [List.count_cons] at bound
    omega

theorem Linear.outputIndices_nodup (linear : Linear state) : (outputIndices state).Nodup :=
  nodup_of_counts _ (fun tag => by rw [← count_eq]; exact linear.unique tag)

theorem Linear.output_index_lt (linear : Linear state) (member : tag ∈ outputIndices state) : tag < state.outputs.length := by
  apply linear.past tag
  rw [count_eq]
  exact List.count_pos_iff.mpr member

theorem Report.outputIndices_nodup (report : Report input events)
    (nocopy : ∀ actual ∈ report.steps, ∀ id, actual.event ≠ .copyPacket id) : (outputIndices report.final).Nodup :=
  (Report.linear report nocopy).outputIndices_nodup


private theorem packetJob_index (item : PacketItem input) (selected : packetJob item = some job) :
    job.outputIndex = packetIndex item := by
  unfold packetJob at selected
  split at selected
  · split at selected <;> cases selected
    all_goals simp_all only [Job.outputIndex, packetIndex, transitIndex]
  · split at selected <;> cases selected
    all_goals simp_all only [Job.outputIndex, packetIndex, transitIndex]

private theorem ticketJob_index (item : TicketItem input) (selected : ticketJob item = some job) :
    job.outputIndex = ticketIndex item := by
  unfold ticketJob at selected
  split at selected <;> cases selected <;> rfl

private theorem filtered_count (rows : List α) (extract : α → Option (Job input)) (indexOf : α → Nat)
    (consistent : ∀ row job, extract row = some job → job.outputIndex = indexOf row) :
    ((rows.filterMap extract).map Job.outputIndex).count tag ≤ (rows.map indexOf).count tag := by
  induction rows with
  | nil => simp
  | cons row rows ih =>
    cases selected : extract row with
    | none =>
      simp only [List.filterMap_cons, selected, List.map_cons, List.count_cons]
      omega
    | some job =>
      have index := consistent row job selected
      simp only [List.filterMap_cons, selected, List.map_cons, List.count_cons, index]
      omega

theorem inventory_count_le (state : State input) (tag : Nat) :
    ((inventory state).map Job.outputIndex).count tag ≤ count state tag := by
  have packets := filtered_count (tag := tag) state.custody.pending packetJob packetIndex (fun row job => packetJob_index row)
  have tickets := filtered_count (tag := tag) state.work.pending ticketJob ticketIndex (fun row job => ticketJob_index row)
  simpa only [inventory, List.map_append, List.count_append, count, packetCount, workCount] using
    Nat.add_le_add packets tickets

theorem Linear.inventory_nodup (linear : Linear state) : ((inventory state).map Job.outputIndex).Nodup :=
  nodup_of_counts _ (fun tag => Nat.le_trans (inventory_count_le state tag) (linear.unique tag))

private theorem job_eq_of_indices {jobs : List (Job input)}
    (unique : (jobs.map Job.outputIndex).Nodup) (first : left ∈ jobs) (second : right ∈ jobs)
    (same : left.outputIndex = right.outputIndex) : left = right := by
  induction jobs with
  | nil => cases first
  | cons head tail ih =>
    have pair := List.nodup_cons.mp (by simpa only [List.map_cons] using unique)
    rcases List.mem_cons.mp first with firstEq | firstTail
    · subst left
      rcases List.mem_cons.mp second with secondEq | secondTail
      · exact secondEq.symm
      · exact False.elim (pair.1 (List.mem_map.mpr ⟨right, secondTail, same.symm⟩))
    · rcases List.mem_cons.mp second with secondEq | secondTail
      · subst right
        exact False.elim (pair.1 (List.mem_map.mpr ⟨left, firstTail, same⟩))
      · exact ih pair.2 firstTail secondTail

theorem Linear.job_eq (linear : Linear state) (first : left ∈ inventory state) (second : right ∈ inventory state)
    (same : left.outputIndex = right.outputIndex) : left = right :=
  job_eq_of_indices linear.inventory_nodup first second same

theorem Linear.path_eq (linear : Linear state) (job : Job input) (member : job ∈ inventory state) :
    CampusTCPStartupSelection.path state job.outputIndex = some job := by
  cases selected : CampusTCPStartupSelection.path state job.outputIndex with
  | none =>
    have absent := List.find?_eq_none.mp selected job member
    exact False.elim (absent (by simp))
  | some found =>
    have same := linear.job_eq (CampusTCPStartupSelection.selected_member selected) member
      (CampusTCPStartupSelection.selected_index selected)
    subst found
    rfl

theorem Report.inventory_nodup (report : Report input events)
    (nocopy : ∀ actual ∈ report.steps, ∀ id, actual.event ≠ .copyPacket id) :
    ((inventory report.final).map Job.outputIndex).Nodup := (Report.linear report nocopy).inventory_nodup

end Netlib.Check.CampusTCPStartupJobUnique
