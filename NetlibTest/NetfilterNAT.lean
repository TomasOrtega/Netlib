import Netlib.Protocol.NetfilterNAT

namespace NetlibTest.NetfilterNAT

open Netlib.Packet
open Netlib.Protocol

private def original : Header := ⟨167772161, 3325256705, Protocol.tcp, 40000, 443⟩
private def aliasEndpoint : Endpoint := ⟨3405803777, 62000⟩
private def backend : Endpoint := ⟨167772162, 8443⟩

private def sourceFlow : FlowNAT.Entry :=
  ⟨original, ((Rewrite.sourceEndpoint aliasEndpoint).apply original).reverse, 0, 0, 0⟩

private def destinationFlow : FlowNAT.Entry :=
  ⟨original, ((Rewrite.destinationEndpoint backend).apply original).reverse, 0, 0, 0⟩

private def combinedFlow : FlowNAT.Entry :=
  ⟨original, ((Rewrite.destinationEndpoint backend).apply
    ((Rewrite.sourceEndpoint aliasEndpoint).apply original)).reverse, 0, 0, 0⟩

private def sourceEntry : NetfilterNAT.Entry := ⟨sourceFlow, true, false⟩
private def destinationEntry : NetfilterNAT.Entry := ⟨destinationFlow, false, true⟩
private def combinedEntry : NetfilterNAT.Entry := ⟨combinedFlow, true, true⟩
private def plainEntry : NetfilterNAT.Entry := ⟨⟨original, original.reverse, 0, 0, 0⟩, false, false⟩

example : sourceEntry.Compatible := (NetfilterNAT.Entry.check_correct _).mp (by decide)
example : destinationEntry.Compatible := (NetfilterNAT.Entry.check_correct _).mp (by decide)
example : combinedEntry.Compatible := (NetfilterNAT.Entry.check_correct _).mp (by decide)
example : plainEntry.Compatible := (NetfilterNAT.Entry.check_correct _).mp (by decide)

example : ¬({ sourceEntry with sourceNAT := false } : NetfilterNAT.Entry).Compatible := by decide
example : ¬({ destinationEntry with destinationNAT := false } : NetfilterNAT.Entry).Compatible := by decide

example : sourceEntry.changesSource .reply = false ∧ sourceEntry.changesDestination .reply = true := ⟨rfl, rfl⟩
example : destinationEntry.changesSource .reply = true ∧ destinationEntry.changesDestination .reply = false := ⟨rfl, rfl⟩

example (packet : Header) : (plainEntry.rewrite .original).apply packet = packet :=
  plainEntry.no_nat_identity rfl rfl _ _

private def ensure (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

def run : IO Unit := do
  for entry in [sourceEntry, destinationEntry, combinedEntry, plainEntry] do
    ensure entry.check "Known NAT flags must agree with the projected tuple endpoints."
    for direction in [FlowNAT.Direction.original, FlowNAT.Direction.reply] do
      let actual := (entry.rewrite direction).apply (entry.flow.input direction)
      ensure (actual == entry.flow.output direction) "Conditional endpoint manipulation must match tuple projection."
      ensure (actual.protocol == original.protocol) "NAT endpoint manipulation must preserve the transport protocol."
  ensure (!({ sourceEntry with sourceNAT := false } : NetfilterNAT.Entry).check)
    "A changed source endpoint requires source-NAT status evidence."
  ensure (!({ destinationEntry with destinationNAT := false } : NetfilterNAT.Entry).check)
    "A changed destination endpoint requires destination-NAT status evidence."
  ensure (!({ combinedEntry with sourceNAT := false } : NetfilterNAT.Entry).check &&
    !({ combinedEntry with destinationNAT := false } : NetfilterNAT.Entry).check)
    "Combined translation requires both endpoint status conditions."
  let sourceReply := (sourceEntry.rewrite .reply).apply sourceFlow.reply
  ensure (sourceReply.destinationEndpoint == original.sourceEndpoint &&
    sourceReply.sourceEndpoint == sourceFlow.reply.sourceEndpoint)
    "Reply processing must invert source NAT at the destination endpoint."
  let destinationReply := (destinationEntry.rewrite .reply).apply destinationFlow.reply
  ensure (destinationReply.sourceEndpoint == original.destinationEndpoint &&
    destinationReply.destinationEndpoint == destinationFlow.reply.destinationEndpoint)
    "Reply processing must invert destination NAT at the source endpoint."
  ensure (sourceFlow.check && !({ sourceEntry with sourceNAT := false } : NetfilterNAT.Entry).check)
    "A valid tuple pair alone must not establish conditional native rewriting."
  ensure (plainEntry.check && (plainEntry.rewrite .reply).apply original == original)
    "Absent NAT flags must retain every input field."
  IO.println "Status-aware NAT projection tests passed."

end NetlibTest.NetfilterNAT
