import Netlib.Protocol.FlowNAT

/-!
# Status-aware tuple rewriting

Native source and destination NAT flags select which endpoint fields change.
Reply processing reverses those selections.
This proves the tuple algebra under explicit compatibility conditions, not C refinement or packet admission.
-/

namespace Netlib.Protocol.NetfilterNAT

open Packet
open FlowNAT (Direction)

def sourceURL : String := "https://raw.githubusercontent.com/torvalds/linux/v6.8/net/netfilter/nf_nat_core.c"

structure Entry where
  flow : FlowNAT.Entry
  sourceNAT : Bool
  destinationNAT : Bool
  deriving Repr, BEq, DecidableEq

namespace Entry

def Compatible (entry : Entry) : Prop :=
  entry.flow.WellFormed ∧
  (entry.sourceNAT = false → entry.flow.original.sourceEndpoint = entry.flow.reply.destinationEndpoint) ∧
  (entry.destinationNAT = false → entry.flow.original.destinationEndpoint = entry.flow.reply.sourceEndpoint)

instance (entry : Entry) : Decidable entry.Compatible := by
  unfold Compatible
  infer_instance

def check (entry : Entry) : Bool := decide entry.Compatible

theorem check_correct (entry : Entry) : entry.check = true ↔ entry.Compatible := by simp [check]

def changesSource (entry : Entry) : Direction → Bool
  | .original => entry.sourceNAT
  | .reply => entry.destinationNAT

def changesDestination (entry : Entry) : Direction → Bool
  | .original => entry.destinationNAT
  | .reply => entry.sourceNAT

def rewrite (entry : Entry) (direction : Direction) : Rewrite :=
  let output := entry.flow.output direction
  { source := if entry.changesSource direction then some output.source else none
    destination := if entry.changesDestination direction then some output.destination else none
    sourcePort := if entry.changesSource direction then some output.sourcePort else none
    destinationPort := if entry.changesDestination direction then some output.destinationPort else none }

private theorem source_unchanged (entry : Entry) (compatible : entry.Compatible) (direction : Direction)
    (unchanged : entry.changesSource direction = false) :
    (entry.flow.input direction).sourceEndpoint = (entry.flow.output direction).sourceEndpoint := by
  cases direction with
  | original => exact compatible.2.1 unchanged
  | reply => exact (compatible.2.2 unchanged).symm

private theorem destination_unchanged (entry : Entry) (compatible : entry.Compatible) (direction : Direction)
    (unchanged : entry.changesDestination direction = false) :
    (entry.flow.input direction).destinationEndpoint = (entry.flow.output direction).destinationEndpoint := by
  cases direction with
  | original => exact compatible.2.2 unchanged
  | reply => exact (compatible.2.1 unchanged).symm

private theorem header_eq {left right : Header}
    (source : left.sourceEndpoint = right.sourceEndpoint)
    (destination : left.destinationEndpoint = right.destinationEndpoint)
    (protocol : left.protocol = right.protocol) : left = right := by
  cases left
  cases right
  simp only [Header.sourceEndpoint, Header.destinationEndpoint, Endpoint.mk.injEq] at source destination
  rcases source with ⟨rfl, rfl⟩
  rcases destination with ⟨rfl, rfl⟩
  cases protocol
  rfl

theorem rewrite_correct (entry : Entry) (compatible : entry.Compatible) (direction : Direction) :
    (entry.rewrite direction).apply (entry.flow.input direction) = entry.flow.output direction := by
  apply header_eq
  · cases selected : entry.changesSource direction with
    | false =>
      simpa only [rewrite, selected, Bool.false_eq_true, ite_false, Rewrite.apply,
        Header.sourceEndpoint, Option.getD_none] using entry.source_unchanged compatible direction selected
    | true => simp [rewrite, selected, Rewrite.apply, Header.sourceEndpoint]
  · cases selected : entry.changesDestination direction with
    | false =>
      simpa only [rewrite, selected, Bool.false_eq_true, ite_false, Rewrite.apply,
        Header.destinationEndpoint, Option.getD_none] using entry.destination_unchanged compatible direction selected
    | true => simp [rewrite, selected, Rewrite.apply, Header.destinationEndpoint]
  · exact (entry.flow.output_protocol compatible.1 direction).symm

theorem no_nat_identity (entry : Entry) (source : entry.sourceNAT = false)
    (destination : entry.destinationNAT = false) (direction : Direction) (packet : Header) :
    (entry.rewrite direction).apply packet = packet := by
  cases direction <;> simp [rewrite, changesSource, changesDestination, source, destination, Rewrite.apply]

end Entry
end Netlib.Protocol.NetfilterNAT
