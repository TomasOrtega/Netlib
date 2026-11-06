import Netlib.Check.CampusTCPTwoProgressPreparation
import Netlib.Check.CampusTCPTwoProgressPathDrop

/-!
# Loss of the lower original before the upper send

The loss resolves the actual exposed ingress item.
The upper send can then use the same loss and cause record.
-/

namespace Netlib.Check.CampusTCPTwoProgressPreparation

open Protocol.TCP CampusTCPModel CampusTCPEnabled
open CampusTCPRound (Cut)
open CampusTCPTwoProgressStart
open CampusTCPTwoProgressSetup (config)

namespace D
export CampusTCPTwoProgressPhaseDrop (Selected lowerBook)
end D
namespace PD
export CampusTCPTwoProgressPathDrop (Dropped Credited)
end PD

variable {input : Input} {complete : H.Completed input.active input.passive}
variable {cut current : Cut input complete} {sender : Actor} {gateway : Gateway} {lower upper : List UInt8}
variable {initial : TwoWriteInitial cut sender gateway lower upper}
variable {native : NativeEnv cut gateway initial.gatewayState.session.entry} {quantum allowance : Nat}
variable {monitor : M.Monitor} {actual : Step input} {first : S.Original initial .lower}

def droppedLower (monitor : M.Monitor) (id : Nat) : M.Monitor :=
  { monitor with drops := monitor.drops ++ [id], lower := { monitor.lower with phase := .done } }

structure LowerDropped (before : PendingUpper initial native quantum allowance current monitor first) (actual : Step input) where
  item : Theory.PacketCustody.Item (Transit input)
  selected : D.Selected before.core item .lower actual
  produced : selected.loss.source = O.source first
  observed : CampusTCPTwoProgressMonitor.observe (config initial native quantum allowance) monitor actual = droppedLower monitor item.id
  next : PendingUpper initial native quantum allowance selected.appended.move.after
    (CampusTCPTwoProgressMonitor.observe (config initial native quantum allowance) monitor actual) first
  book : next.core.losses.book = D.lowerBook selected

private theorem drop_target (before : PendingUpper initial native quantum allowance current monitor first)
    (path : P.DataIngress initial current .lower monitor.lower) (budget : monitor.drops.length < allowance) :
    CampusTCPTwoProgressMonitor.dropTarget (config initial native quantum allowance) current.report.final monitor path.packetID = some .lower := by
  simp only [CampusTCPTwoProgressMonitor.dropTarget, before.mode,
    show (CampusTCPTwoProgressMonitor.Mode.originals == .originals) = true from rfl,
    Bool.true_or, ite_true, config, budget, path.exposed_packet, beq_self_eq_true]

private theorem drop_observed (before : PendingUpper initial native quantum allowance current monitor first)
    (item : Theory.PacketCustody.Item (Transit input)) (selected : D.Selected before.core item .lower actual) :
    CampusTCPTwoProgressMonitor.observe (config initial native quantum allowance) monitor actual = droppedLower monitor item.id := by
  rw [selected.observed]
  simp only [CampusTCPTwoProgressMonitor.observeDrop, selected.appended.move.beforeEq, selected.selected]
  simp only [CampusTCPTwoProgressMonitor.normalize, before.mode, before.ack, before.upperPending,
    Option.isNone_none, CampusTCPTwoProgressMonitorFacts.phase_beq_self,
    show (CampusTCPRoundMonitor.Phase.needSend == .done) = false from rfl,
    Bool.and_false, Bool.false_eq_true, ite_false, droppedLower]

private theorem drop_at_path (before : PendingUpper initial native quantum allowance current monitor first)
    (path : P.DataIngress initial current .lower monitor.lower) (produced : path.output.produced = O.source first)
    (budget : monitor.drops.length < allowance) : ∃ actual, Nonempty (LowerDropped before actual) := by
  obtain ⟨actual, drop, ⟨credited⟩⟩ := CampusTCPTwoProgressPathDrop.original_ingress_at before.core path (drop_target before path budget)
  have observed := drop_observed before drop.item drop.selected
  let updated := CampusTCPTwoProgressMonitor.observe (config initial native quantum allowance) monitor actual
  let core := credited.result.next
  have book : core.losses.book = D.lowerBook drop.selected := credited.result.bookEq
  have source : drop.selected.loss.source = O.source first := drop.sourceEq.trans produced
  let next : PendingUpper initial native quantum allowance drop.selected.appended.move.after updated first := {
    core
    mode := by dsimp only [updated]; rw [observed]; exact before.mode
    lowerPath := .lost (by dsimp only [updated]; rw [observed]; rfl) before.core.losses.book.losses.length
      drop.selected.loss
      (by rw [book]; exact List.getElem?_concat_length)
      source (by rw [book]; rfl)
    upperPending := by dsimp only [updated]; rw [observed]; exact before.upperPending
    ack := by dsimp only [updated]; rw [observed]; exact before.ack
    waiting := by dsimp only [updated]; rw [observed]; exact before.waiting
    retry := by dsimp only [updated]; rw [observed]; exact before.retry
    retries := by dsimp only [updated]; rw [observed]; exact before.retries }
  exact ⟨actual, ⟨⟨drop.item, drop.selected, source, observed, next, book⟩⟩⟩

theorem PendingUpper.lower_drop_at (before : PendingUpper initial native quantum allowance current monitor first)
    (pending : monitor.lower.phase = .dataIngress) (budget : monitor.drops.length < allowance) :
    ∃ actual, Nonempty (LowerDropped before actual) := by
  cases before.lowerPath with
  | ingress path produced => exact drop_at_path before path produced budget
  | lost phase _ _ _ _ _ => rw [pending] at phase; cases phase

end Netlib.Check.CampusTCPTwoProgressPreparation
