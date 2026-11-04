import Netlib.Packet.Processor

namespace NetlibTest.Processor

open Netlib Netlib.Packet

private def input : Header := ⟨167772161, 3405803786, Protocol.tcp, 50000, 80⟩

private def translated : Header := { input with destination := 3325256714, destinationPort := 443 }

private def destinationRewrite : Packet.Rewrite :=
  { destination := some translated.destination, destinationPort := some translated.destinationPort }

private def https : Match :=
  { protocol := some Protocol.tcp, destinationPorts := some (PortRange.single 443) }

private def policy : Packet.ACL := [⟨https, .permit⟩]

private def allocate : Packet.Processor Nat :=
  ⟨fun count packet => (count + 1, some (destinationRewrite.apply packet))⟩

private def countedFilter : Packet.Processor Nat :=
  ⟨fun count packet => (count + 1, if https.accepts packet then some packet else none)⟩

private def countedDrop : Packet.Processor Nat := ⟨fun count _ => (count + 7, none)⟩

private theorem allocate_preserves (bound : Nat) : allocate.Preserves (fun count => bound ≤ count) := by
  intro count packet before
  change bound ≤ count + 1
  omega

private theorem filter_preserves (bound : Nat) : countedFilter.Preserves (fun count => bound ≤ count) := by
  intro count packet before
  change bound ≤ count + 1
  omega

example : (allocate.seq (Packet.Processor.drop : Packet.Processor Nat)).Preserves (fun count => 5 ≤ count) :=
  Packet.Processor.Preserves.seq (allocate_preserves 5) (Packet.Processor.drop_preserves _)

example : ((Packet.Processor.liftLeft allocate).seq (Packet.Processor.liftRight countedFilter)).Preserves
    (fun state : Nat × Nat => 5 ≤ state.1 ∧ 7 ≤ state.2) :=
  Packet.Processor.Preserves.seq
    (Packet.Processor.Preserves.liftLeft (allocate_preserves 5) (fun count : Nat => 7 ≤ count))
    (Packet.Processor.Preserves.liftRight (filter_preserves 7) (fun count : Nat => 5 ≤ count))

example : (allocate.seq Packet.Processor.drop).run 0 input = (1, none) := rfl

example : (countedDrop.seq allocate).run 0 input = (7, none) := rfl

example : ((Packet.Processor.rewrite destinationRewrite).seq (Packet.Processor.acl policy) :
    Packet.Processor Unit).run () input = ((), some translated) := by decide

example : ((Packet.Processor.acl policy).seq (Packet.Processor.rewrite destinationRewrite) :
    Packet.Processor Unit).run () input = ((), none) := by decide

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

def run : IO Unit := do
  let rewriteThenFilter : Packet.Processor Nat :=
    (Packet.Processor.rewrite destinationRewrite).seq (Packet.Processor.acl policy)
  ensure (rewriteThenFilter.run 3 input == (3, some translated))
    "The postfilter did not see the rewritten header."
  let filterThenRewrite : Packet.Processor Nat :=
    (Packet.Processor.acl policy).seq (Packet.Processor.rewrite destinationRewrite)
  ensure (filterThenRewrite.run 3 input == (3, none)) "A denied input reached the later rewrite."
  let retained := (allocate.seq Packet.Processor.drop).run 3 input
  ensure (retained == (4, none)) "A postfilter drop rolled back an earlier state update."
  let shortCircuited := (countedDrop.seq allocate).run 3 input
  ensure (shortCircuited == (10, none)) "A first-stage drop executed the later allocator or lost its own state."
  let postfilterDrop := (allocate.seq countedDrop).run 3 input
  ensure (postfilterDrop == (11, none)) "A dropping second stage lost completed state updates."
  let left : Packet.Processor (Nat × Nat) := Packet.Processor.liftLeft allocate
  let right : Packet.Processor (Nat × Nat) := Packet.Processor.liftRight countedFilter
  ensure (left.run (3, 11) input == ((4, 11), some translated)) "The left stage changed the independent right store."
  ensure (right.run (3, 11) input == ((3, 12), none)) "The right drop changed the independent left store."
  ensure ((left.seq right).run (3, 11) input == ((4, 12), some translated))
    "Independent stores did not compose over the updated packet."
  ensure ((right.seq left).run (3, 11) input == ((3, 12), none))
    "Product lifting erased packet-order dependence."
  for count in [0, 3, 100] do
    for header in [input, translated, { translated with protocol := Protocol.udp }] do
      ensure (((allocate.seq countedFilter).seq countedDrop).run count header ==
        (allocate.seq (countedFilter.seq countedDrop)).run count header)
        "Stage grouping changed packet or store behavior."
      ensure ((Packet.Processor.identity.seq countedDrop).run count header == countedDrop.run count header)
        "Identity changed a dropping stage."
      ensure ((countedDrop.seq Packet.Processor.identity).run count header == countedDrop.run count header)
        "A final identity changed a drop or its state."
  IO.println "Packet processor tests passed."

end NetlibTest.Processor
