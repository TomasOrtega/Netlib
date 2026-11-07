import Netlib.Check.CampusTCPTwoProgressPathsFrames
import Netlib.Check.CampusTCPTwoProgressNetwork

namespace Netlib.Check.CampusTCPTwoProgressPathRetain

open Packet Protocol Protocol.TCP CampusTCPModel
namespace O
export Theory.Outstanding (Item State Completed)
end O
namespace C
export Theory.PacketCustody (Item State Resolved)
end C

private theorem find_erase_other {α : Type u} (items : List (O.Item α)) (predicate : O.Item α → Bool)
    (selected removed : Nat) (found : (items.find? predicate).map (·.id) = some selected)
    (different : selected ≠ removed) :
    ((items.eraseP (fun item => item.id == removed)).find? predicate).map (·.id) = some selected := by
  induction items with
  | nil => simp only [List.find?_nil, Option.map_none] at found; cases found
  | cons head tail ih =>
    by_cases hit : predicate head = true
    · have identity : head.id = selected := by simpa only [List.find?_cons, hit, ↓reduceIte, Option.map_some, Option.some.injEq] using found
      have untouched : head.id ≠ removed := identity ▸ different
      simp only [List.eraseP_cons, beq_iff_eq, untouched, ↓reduceIte, List.find?_cons, hit, Option.map_some]
      exact congrArg some identity
    · have later : (tail.find? predicate).map (·.id) = some selected := by simpa only [List.find?_cons, hit, Bool.false_eq_true, ↓reduceIte] using found
      by_cases erased : head.id = removed
      · simpa only [List.eraseP_cons, erased, beq_self_eq_true, ↓reduceIte] using later
      · simpa only [List.eraseP_cons, beq_iff_eq, erased, ↓reduceIte, List.find?_cons, hit, Bool.false_eq_true] using ih later

private theorem find_append {α : Type u} (items extra : List (O.Item α)) (predicate : O.Item α → Bool)
    (selected : Nat) (found : (items.find? predicate).map (·.id) = some selected) :
    ((items ++ extra).find? predicate).map (·.id) = some selected := by
  cases selectedItem : items.find? predicate with
  | none => simp only [selectedItem, Option.map_none] at found; cases found
  | some item => simpa only [List.find?_append, selectedItem, Option.or, Option.map_some] using found

theorem completed_other {before : O.State α} (completed : O.Completed before consumed) (item : O.Item α)
    (member : item ∈ before.pending) (different : item.id ≠ consumed) : item ∈ completed.state.pending := by
  rcases List.mem_cons.mp (completed.pendingPerm.mem_iff.mp member) with same | remaining
  · exact False.elim (different (same ▸ completed.selected))
  · exact remaining

theorem enqueue_other (before : O.State α) (value : α) (item : O.Item α)
    (member : item ∈ before.pending) : item ∈ (Theory.Outstanding.enqueue before value).pending :=
  List.mem_append_left _ member

theorem resolved_pending (before : C.State α) (id : Nat) (disposition : Theory.PacketCustody.Disposition)
    (resolved : C.Resolved before id disposition) (computed : Theory.PacketCustody.resolve before id disposition = .ok resolved) :
    resolved.state.pending = before.pending.eraseP (fun item => item.id == id) := by
  unfold Theory.PacketCustody.resolve at computed
  cases finished : Theory.Outstanding.complete before.work id with
  | error reason => simp [finished, Except.mapError, bind, Except.bind] at computed
  | ok completed =>
    simp only [finished, Except.mapError, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at computed
    cases computed
    exact Theory.Outstanding.complete_pending before.work id completed finished

theorem resolve_other (before : C.State α) (id : Nat) (disposition : Theory.PacketCustody.Disposition)
    (resolved : C.Resolved before id disposition) (computed : Theory.PacketCustody.resolve before id disposition = .ok resolved)
    (predicate : α → Bool) (selected : Nat) (found : before.pendingID predicate = some selected)
    (different : selected ≠ id) : resolved.state.pendingID predicate = some selected := by
  unfold Theory.PacketCustody.State.pendingID
  rw [resolved_pending before id disposition resolved computed]
  exact find_erase_other before.pending _ selected id found different

theorem pending_prefix (before after : C.State α) (retained : before.pending <+: after.pending)
    (predicate : α → Bool) (selected : Nat) (found : before.pendingID predicate = some selected) :
    after.pendingID predicate = some selected := by
  obtain ⟨extra, stored⟩ := retained
  unfold Theory.PacketCustody.State.pendingID
  rw [← stored]
  exact find_append before.pending extra _ selected found

theorem finish_pending (before : State input) (effect : Effect input) (custody : Custody input) :
    custody.pending <+: (finishCustody before effect custody).pending := by
  unfold finishCustody
  cases effect.output <;> cases effect.service <;> simp only
  · exact List.prefix_refl _
  · split
    · exact List.prefix_refl _
    · rw [Theory.PacketCustody.mint_pending]
      exact List.prefix_append _ _
  · rw [Theory.PacketCustody.mint_pending]
    exact List.prefix_append _ _
  · split
    · rw [Theory.PacketCustody.mint_pending]
      exact List.prefix_append _ _
    · rw [Theory.PacketCustody.mint_pending, Theory.PacketCustody.mint_pending]
      exact (List.prefix_append _ _).trans (List.prefix_append _ _)

def consumedPacket (before : State input) : CampusTCPModel.Event → Option Nat
  | .assign index _ => before.custody.pendingID (Transit.ingressAt index)
  | .deliver index _ _ => before.custody.pendingID (Transit.linkAt index)
  | .dropPacket id => some id
  | _ => none

theorem prepare_other (before : State input) (event : CampusTCPModel.Event) (custody : Custody input)
    (computed : prepareCustody before event = .ok custody) (predicate : Transit input → Bool)
    (selected : Nat) (found : before.custody.pendingID predicate = some selected)
    (different : consumedPacket before event ≠ some selected) : custody.pendingID predicate = some selected := by
  cases event <;> try (simp only [prepareCustody, pure, Except.pure, Except.ok.injEq] at computed; cases computed; exact found)
  case assign index ingress =>
    cases chosen : before.custody.pendingID (Transit.ingressAt index) with
    | none => simp [prepareCustody, chosen] at computed
    | some id =>
      cases resolution : Theory.PacketCustody.resolve before.custody id .assigned with
      | error reason => simp [prepareCustody, chosen, resolution, Except.mapError, bind, Except.bind] at computed
      | ok resolved =>
        simp only [prepareCustody, chosen, resolution, Except.mapError, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at computed
        cases computed
        exact resolve_other before.custody id .assigned resolved resolution predicate selected found (by
          intro same; apply different; simp only [consumedPacket, chosen, same])
  case deliver index bytes policy =>
    cases chosen : before.custody.pendingID (Transit.linkAt index) with
    | none => simp [prepareCustody, chosen] at computed
    | some id =>
      cases resolution : Theory.PacketCustody.resolve before.custody id .delivered with
      | error reason => simp [prepareCustody, chosen, resolution, Except.mapError, bind, Except.bind] at computed
      | ok resolved =>
        simp only [prepareCustody, chosen, resolution, Except.mapError, bind, Except.bind] at computed
        split at computed
        · simp only [pure, Except.pure, Except.ok.injEq] at computed
          cases computed
          exact resolve_other before.custody id .delivered resolved resolution predicate selected found (by
            intro same; apply different; simp only [consumedPacket, chosen, same])
        · cases computed
  case copyPacket id =>
    cases copied : Theory.PacketCustody.copy before.custody id with
    | error reason => simp [prepareCustody, copied, Except.mapError, bind, Except.bind] at computed
    | ok copy =>
      simp only [prepareCustody, copied, Except.mapError, bind, Except.bind, pure, Except.pure] at computed
      split at computed
      · cases computed
      · simp only [Except.ok.injEq] at computed
        cases computed
        apply pending_prefix before.custody copy.state _ predicate selected found
        rw [copy.pending]
        exact List.prefix_append _ _
  case dropPacket id =>
    cases resolution : Theory.PacketCustody.resolve before.custody id .dropped with
    | error reason => simp [prepareCustody, resolution, Except.mapError, bind, Except.bind] at computed
    | ok resolved =>
      simp only [prepareCustody, resolution, Except.mapError, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at computed
      cases computed
      exact resolve_other before.custody id .dropped resolved resolution predicate selected found (by
        intro same; exact different (congrArg some same.symm))

theorem Step.custody_other (actual : Step input) (predicate : Transit input → Bool) (selected : Nat)
    (found : actual.before.custody.pendingID predicate = some selected)
    (different : consumedPacket actual.before actual.event ≠ some selected) :
    actual.result.state.custody.pendingID predicate = some selected := by
  obtain ⟨effect, custody, _, computed, result⟩ := actual.transaction
  rw [result]
  exact pending_prefix custody _ (finish_pending actual.before effect custody) predicate selected
    (prepare_other actual.before actual.event custody computed predicate selected found different)

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {current : CampusTCPRound.Cut input complete} {actual : Step input}

theorem Move.outputs (move : CampusTCPRoundPhaseBase.Move current actual) :
    current.report.final.outputs <+: move.after.report.final.outputs := by
  rw [move.final, CampusTCPOrigins.output_history actual, move.beforeEq]
  exact List.prefix_append _ _

theorem Move.services (move : CampusTCPRoundPhaseBase.Move current actual) :
    current.report.final.services <+: move.after.report.final.services := by
  rw [move.final, CampusTCPOrigins.service_history actual, move.beforeEq]
  exact List.prefix_append _ _

theorem Move.custody_other (move : CampusTCPRoundPhaseBase.Move current actual)
    (predicate : Transit input → Bool) (selected : Nat)
    (found : current.report.final.custody.pendingID predicate = some selected)
    (different : consumedPacket current.report.final actual.event ≠ some selected) :
    move.after.report.final.custody.pendingID predicate = some selected := by
  rw [move.final]
  exact Step.custody_other actual predicate selected (by rw [move.beforeEq]; exact found)
    (by rw [move.beforeEq]; exact different)

def QuietWork : CampusTCPModel.Event → Prop
  | .write .. | .send .. | .dispatchAck .. | .advanceClock .. | .timeout .. | .read .. | .emitAck ..
    | .deliver .. | .copyPacket .. | .dropPacket .. => True
  | _ => False

private theorem startup_work (before : State input) (event : Check.TCPHandshake.Event) (effect : Effect input)
    (computed : startup input before event = .ok effect) : effect.state.work = before.work := by
  unfold startup at computed
  repeat' first
    | (solve | cases computed; rfl)
    | (cases computed)
    | (split at computed)
    | (dsimp only [bind, Except.bind, pure, Except.pure] at computed)

private theorem recovery_work (before : State input) (event : Check.TCPHandshakeRecovery.Event) (effect : Effect input)
    (computed : runRecovery input before event = .ok effect) : effect.state.work = before.work := by
  unfold runRecovery at computed
  cases connection : before.connection with
  | startup stage pending | application complete endpoints =>
    simp only [connection] at computed
    cases computed
    rfl
  | recovering current =>
    simp only [connection] at computed
    split at computed
    · cases computed
    · split at computed <;> cases computed <;> rfl

theorem Step.work_quiet (actual : Step input) (quiet : QuietWork actual.event) :
    actual.result.state.work = actual.before.work := by
  obtain ⟨effect, custody, computed, final⟩ := actual.processed
  suffices same : effect.state.work = actual.before.work by simpa only [final] using same
  cases event : actual.event <;> simp only [event, QuietWork] at quiet
  all_goals try contradiction
  all_goals rw [event] at computed
  all_goals simp only [processCore] at computed
  all_goals first
    | exact (CampusTCPTimedTimeout.application_frames _ _ _ _ computed).1
    | (cases computed; rfl)
    | repeat' first
      | (solve | cases computed; dsimp only; exact (CampusTCPTimedTimeout.application_frames _ _ _ _ (by assumption)).1)
      | (solve | cases computed; dsimp only; exact startup_work _ _ _ (by assumption))
      | (solve | cases computed; dsimp only; exact recovery_work _ _ _ (by assumption))
      | (cases computed)
      | (split at computed)
      | (dsimp only [CampusTCPModel.get, parsed, Except.mapError, bind, Except.bind, pure, Except.pure,
          throw, throwThe, MonadExceptOf.throw] at computed)

end Netlib.Check.CampusTCPTwoProgressPathRetain

namespace Netlib.Check.CampusTCPTwoProgressPaths

open Packet Protocol Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPRoundPhaseBase (Move)
open CampusTCPTwoProgressStart
namespace P
export CampusTCPTwoProgressPathRetain (consumedPacket QuietWork)
end P

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current : Cut input complete} {sender actor : Actor} {gateway : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {fields : Produced input.active input.passive → Prop} {ingress : I.InterfaceRef} {target : Header}
variable {actual : Step input} {native : NativeEnv cut gateway initial.gatewayState.session.entry}
variable {produced : Produced input.active input.passive}
variable {part : CampusTCPTwoProgressSender.Part} {lane : M.Lane} {count : Nat}

def Output.after_move (path : Output current actor fields) (move : Move current actual) :
    Output move.after actor fields := path.retain (CampusTCPTwoProgressPathRetain.Move.outputs move)

def Ingress.after_move (path : Ingress current actor fields) (move : Move current actual)
    (different : P.consumedPacket current.report.final actual.event ≠ some path.packetID) :
    Ingress move.after actor fields := path.retain (CampusTCPTwoProgressPathRetain.Move.outputs move)
      (CampusTCPTwoProgressPathRetain.Move.custody_other move _ path.packetID path.custody different)

def Link.after_move (path : Link current actor fields target) (move : Move current actual)
    (different : P.consumedPacket current.report.final actual.event ≠ some path.packetID) :
    Link move.after actor fields target := path.retain (CampusTCPTwoProgressPathRetain.Move.services move)
      (CampusTCPTwoProgressPathRetain.Move.custody_other move _ path.packetID path.custody different)

def TicketPath.after_quiet (path : TicketPath current actor fields gateway ingress) (move : Move current actual)
    (quiet : P.QuietWork actual.event) : TicketPath move.after actor fields gateway ingress :=
  path.retain (CampusTCPTwoProgressPathRetain.Move.outputs move) (by
    rw [move.final, CampusTCPTwoProgressPathRetain.Step.work_quiet actual quiet, move.beforeEq]
    exact path.pending)

def TicketPath.after_assignment (path : TicketPath current actor fields gateway ingress)
    (assigned : CampusTCPTwoProgressNetwork.AssignmentMove initial current index selectedIngress produced actual) :
    TicketPath assigned.move.after actor fields gateway ingress :=
  path.retain (CampusTCPTwoProgressPathRetain.Move.outputs assigned.move) (by
    rw [assigned.move.final, assigned.facts.work]
    exact CampusTCPTwoProgressPathRetain.enqueue_other _ _ path.ticket path.pending)

def TicketPath.after_service (path : TicketPath current actor fields gateway ingress)
    (service : CampusTCPTwoProgressNetwork.ServiceMove initial current item hit session actual served emission emitted)
    (different : path.ticket.id ≠ item.id) : TicketPath service.move.after actor fields gateway ingress :=
  path.retain (CampusTCPTwoProgressPathRetain.Move.outputs service.move) (by
    obtain ⟨completed, _, _, work⟩ := service.facts.completed
    rw [service.move.final, work]
    exact CampusTCPTwoProgressPathRetain.completed_other completed path.ticket
      (by rw [service.move.beforeEq]; exact path.pending) different)

def DataIngress.after_move (path : DataIngress initial current part lane) (move : Move current actual)
    (different : P.consumedPacket current.report.final actual.event ≠ some path.packetID) :
    DataIngress initial move.after part lane :=
  path.retain (CampusTCPTwoProgressPathRetain.Move.outputs move)
    (CampusTCPTwoProgressPathRetain.Move.custody_other move _ path.packetID path.custody different)

def AckIngress.after_move (path : AckIngress initial current count lane) (move : Move current actual)
    (different : P.consumedPacket current.report.final actual.event ≠ some path.packetID) :
    AckIngress initial move.after count lane :=
  path.retain (CampusTCPTwoProgressPathRetain.Move.outputs move)
    (CampusTCPTwoProgressPathRetain.Move.custody_other move _ path.packetID path.custody different)

def DataLink.after_move (path : DataLink initial current part lane) (move : Move current actual)
    (different : P.consumedPacket current.report.final actual.event ≠ some path.packetID) :
    DataLink initial move.after part lane :=
  path.retain (CampusTCPTwoProgressPathRetain.Move.services move)
    (CampusTCPTwoProgressPathRetain.Move.custody_other move _ path.packetID path.custody different)

def AckLink.after_move (path : AckLink initial current count lane) (move : Move current actual)
    (different : P.consumedPacket current.report.final actual.event ≠ some path.packetID) :
    AckLink initial move.after count lane :=
  path.retain (CampusTCPTwoProgressPathRetain.Move.services move)
    (CampusTCPTwoProgressPathRetain.Move.custody_other move _ path.packetID path.custody different)

def DataTicket.after_quiet (path : DataTicket initial native current part lane) (move : Move current actual)
    (quiet : P.QuietWork actual.event) : DataTicket initial native move.after part lane :=
  path.retain (CampusTCPTwoProgressPathRetain.Move.outputs move) (by
    rw [move.final, CampusTCPTwoProgressPathRetain.Step.work_quiet actual quiet, move.beforeEq]
    exact path.pending)

def DataTicket.after_assignment (path : DataTicket initial native current part lane)
    (assigned : CampusTCPTwoProgressNetwork.AssignmentMove initial current index selectedIngress produced actual) :
    DataTicket initial native assigned.move.after part lane :=
  path.retain (CampusTCPTwoProgressPathRetain.Move.outputs assigned.move) (by
    rw [assigned.move.final, assigned.facts.work]
    exact CampusTCPTwoProgressPathRetain.enqueue_other _ _ path.ticket path.pending)

def DataTicket.after_service (path : DataTicket initial native current part lane)
    (service : CampusTCPTwoProgressNetwork.ServiceMove initial current item hit session actual served emission emitted)
    (different : path.ticket.id ≠ item.id) : DataTicket initial native service.move.after part lane :=
  path.retain (CampusTCPTwoProgressPathRetain.Move.outputs service.move) (by
    obtain ⟨completed, _, _, work⟩ := service.facts.completed
    rw [service.move.final, work]
    exact CampusTCPTwoProgressPathRetain.completed_other completed path.ticket
      (by rw [service.move.beforeEq]; exact path.pending) different)

def AckTicket.after_quiet (path : AckTicket initial native current count lane) (move : Move current actual)
    (quiet : P.QuietWork actual.event) : AckTicket initial native move.after count lane :=
  path.retain (CampusTCPTwoProgressPathRetain.Move.outputs move) (by
    rw [move.final, CampusTCPTwoProgressPathRetain.Step.work_quiet actual quiet, move.beforeEq]
    exact path.pending)

def AckTicket.after_assignment (path : AckTicket initial native current count lane)
    (assigned : CampusTCPTwoProgressNetwork.AssignmentMove initial current index selectedIngress produced actual) :
    AckTicket initial native assigned.move.after count lane :=
  path.retain (CampusTCPTwoProgressPathRetain.Move.outputs assigned.move) (by
    rw [assigned.move.final, assigned.facts.work]
    exact CampusTCPTwoProgressPathRetain.enqueue_other _ _ path.ticket path.pending)

def AckTicket.after_service (path : AckTicket initial native current count lane)
    (service : CampusTCPTwoProgressNetwork.ServiceMove initial current item hit session actual served emission emitted)
    (different : path.ticket.id ≠ item.id) : AckTicket initial native service.move.after count lane :=
  path.retain (CampusTCPTwoProgressPathRetain.Move.outputs service.move) (by
    obtain ⟨completed, _, _, work⟩ := service.facts.completed
    rw [service.move.final, work]
    exact CampusTCPTwoProgressPathRetain.completed_other completed path.ticket
      (by rw [service.move.beforeEq]; exact path.pending) different)

@[simp] theorem Output.after_move_produced (path : Output current actor fields) (move : Move current actual) :
    (path.after_move move).produced = path.produced := rfl

@[simp] theorem Ingress.after_move_produced (path : Ingress current actor fields) (move : Move current actual)
    (different : P.consumedPacket current.report.final actual.event ≠ some path.packetID) :
    (path.after_move move different).output.produced = path.output.produced := rfl

@[simp] theorem Ingress.after_move_packetID (path : Ingress current actor fields) (move : Move current actual)
    (different : P.consumedPacket current.report.final actual.event ≠ some path.packetID) :
    (path.after_move move different).packetID = path.packetID := rfl

@[simp] theorem Link.after_move_packetID (path : Link current actor fields target) (move : Move current actual)
    (different : P.consumedPacket current.report.final actual.event ≠ some path.packetID) :
    (path.after_move move different).packetID = path.packetID := rfl

@[simp] theorem Link.after_move_served (path : Link current actor fields target) (move : Move current actual)
    (different : P.consumedPacket current.report.final actual.event ≠ some path.packetID) :
    (path.after_move move different).served = path.served := rfl

@[simp] theorem Link.after_move_produced (path : Link current actor fields target) (move : Move current actual)
    (different : P.consumedPacket current.report.final actual.event ≠ some path.packetID) :
    (path.after_move move different).served.ticket.value.produced = path.served.ticket.value.produced := rfl

@[simp] theorem TicketPath.after_quiet_ticket (path : TicketPath current actor fields gateway ingress)
    (move : Move current actual) (quiet : P.QuietWork actual.event) :
    (path.after_quiet move quiet).ticket = path.ticket := rfl

@[simp] theorem TicketPath.after_assignment_ticket (path : TicketPath current actor fields gateway ingress)
    (assigned : CampusTCPTwoProgressNetwork.AssignmentMove initial current index selectedIngress produced actual) :
    (path.after_assignment assigned).ticket = path.ticket := rfl

@[simp] theorem TicketPath.after_service_ticket (path : TicketPath current actor fields gateway ingress)
    (service : CampusTCPTwoProgressNetwork.ServiceMove initial current item hit session actual served emission emitted)
    (different : path.ticket.id ≠ item.id) : (path.after_service service different).ticket = path.ticket := rfl

end Netlib.Check.CampusTCPTwoProgressPaths
