import Netlib.Protocol.NATPipeline

namespace NetlibTest.NATPipeline

open Netlib.Packet Netlib.Protocol

private def packet : Header := ⟨167772161, 3325256714, Protocol.tcp, 40000, 443⟩
private def firstAlias : Endpoint := ⟨3405803777, 62000⟩
private def secondAlias : Endpoint := ⟨3405803778, 63000⟩
private def firstWire : Header := (Rewrite.sourceEndpoint firstAlias).apply packet
private def secondWire : Header := (Rewrite.sourceEndpoint secondAlias).apply firstWire
private def allow : ACL := [⟨{}, .permit⟩]
private def opened : NAT.State :=
  (NAT.outboundProcessor firstAlias 10 allow).run NAT.State.initial packet |>.1

private def postdrop : NAT.Direction → Processor NAT.State := NAT.pipeline allow [] allow

private def inputs : List (NAT.Direction × Header) :=
  [(.outbound firstAlias 10, packet), (.inbound, firstWire.reverse)]

private def observed : List (Processor.Observation NAT.Direction) :=
  [⟨.outbound firstAlias 10, packet, none⟩, ⟨.inbound, firstWire.reverse, some packet.reverse⟩]

example : Processor.execute postdrop NAT.State.initial inputs = (opened, observed) := by decide

example (events : List (NAT.Direction × Header)) :
    (Processor.execute postdrop NAT.State.initial events).1.Safe :=
  (NAT.pipeline_safe allow [] allow).trace NAT.initial_safe
    (Processor.execute_trace postdrop NAT.State.initial events)

example :
    (NAT.inboundProcessor.liftRight.seq NAT.inboundProcessor.liftLeft).run
      (opened, (NAT.outboundProcessor secondAlias 20 allow).run NAT.State.initial firstWire |>.1)
      secondWire.reverse =
        ((opened, (NAT.outboundProcessor secondAlias 20 allow).run NAT.State.initial firstWire |>.1),
          some packet.reverse) := by decide

example : ¬(Processor.transition postdrop).Trace NAT.State.initial
    [⟨.outbound firstAlias 10, packet, some firstWire⟩] opened := by
  intro claimed
  have exactOutput := Processor.trace_eq_execute postdrop claimed
  have impossible : (none : Option Header) = some firstWire :=
    congrArg (fun result => (result.2.head?.bind (some ∘ Processor.Observation.output)).join) exactOutput
  cases impossible

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

def run : IO Unit := do
  let before := (Processor.acl ([] : ACL)).seq (NAT.outboundProcessor firstAlias 10 allow)
  let blocked := before.run NAT.State.initial packet
  ensure (decide (blocked = (NAT.State.initial, none)))
    "A prefilter denial installed NAT state."
  let after := (NAT.outboundProcessor firstAlias 10 allow).seq (Processor.acl [])
  let dropped := after.run NAT.State.initial packet
  ensure (dropped.2.isNone && dropped.1.bindings.length == 1)
    "A postfilter drop rolled back earlier NAT state."
  ensure (decide (NAT.inboundProcessor.run dropped.1 firstWire.reverse = (opened, some packet.reverse)))
    "The retained NAT state did not authorize the exact reply."
  let result := Processor.execute postdrop NAT.State.initial inputs
  ensure (decide (result = (opened, observed)))
    "Packet execution lost a drop or used an independent state for the reply."
  ensure (decide (result.2.map Processor.Observation.input = inputs))
    "The execution changed the input order."
  let forwarded := NAT.pipeline allow allow allow
  let admitted := Processor.execute forwarded NAT.State.initial inputs
  ensure (decide (admitted.2.map Processor.Observation.output = [some firstWire, some packet.reverse]))
    "A passing pipeline did not preserve both translations."
  let noInbound := Processor.execute (NAT.pipeline allow allow []) NAT.State.initial inputs
  ensure (decide (noInbound.1 = opened) &&
    decide ((noInbound.2[1]?).map Processor.Observation.output = some none))
    "An inbound postfilter changed NAT state or admitted a denied reply."
  let sourceFilter : ACL := [⟨{ source := some ⟨firstAlias.address, 32⟩ }, .permit⟩]
  let correctOrder := (NAT.outboundProcessor firstAlias 10 allow).seq (Processor.acl sourceFilter)
  let wrongOrder := (Processor.acl sourceFilter).seq (NAT.outboundProcessor firstAlias 10 allow)
  ensure ((correctOrder.run NAT.State.initial packet).2.isSome &&
    decide (wrongOrder.run NAT.State.initial packet = (NAT.State.initial, none)))
    "Filtering did not read the header at its declared stage."
  let tandem := (NAT.outboundProcessor firstAlias 10 allow).liftLeft.seq
    (NAT.outboundProcessor secondAlias 20 allow).liftRight
  let sent := tandem.run (NAT.State.initial, NAT.State.initial) packet
  ensure (decide (sent.2 = some secondWire) &&
    sent.1.1.bindings.length == 1 && sent.1.2.bindings.length == 1)
    "Tandem translation did not retain independent stores."
  let returned := (NAT.inboundProcessor.liftRight.seq NAT.inboundProcessor.liftLeft).run sent.1 secondWire.reverse
  ensure (decide (returned = (sent.1, some packet.reverse)))
    "Tandem replies did not invert the processing order."
  let reversed := (NAT.inboundProcessor.liftLeft.seq NAT.inboundProcessor.liftRight).run sent.1 secondWire.reverse
  ensure reversed.2.isNone "An incorrect tandem reply order unexpectedly succeeded."
  IO.println "NAT pipeline and ordered packet trace tests passed."

end NetlibTest.NATPipeline
