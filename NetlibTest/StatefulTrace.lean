import Netlib.Packet.StatefulTrace

namespace NetlibTest.StatefulTrace

open Netlib Netlib.Packet

private inductive Device where
  | client | gateway | server
  deriving Repr, BEq, DecidableEq

open Device

private def input : Header := ⟨167772161, 3405803786, Protocol.tcp, 50000, 80⟩

private def translated : Header := { input with destinationPort := 443 }

private def prepare : Processor Nat :=
  ⟨fun count packet => (count + 1, some { packet with destinationPort := 443 })⟩

private def dependent : Processor Nat :=
  ⟨fun count packet =>
    if count == 1 && packet.destinationPort == 443 then (count + 10, some packet) else (count, none)⟩

private def physical : Network Device :=
  ⟨fun source target => (source = client ∧ target = gateway) ∨ (source = gateway ∧ target = server)⟩

private def programs : Device → Device → Processor Nat
  | .client, .gateway => prepare
  | .gateway, .server => dependent
  | _, _ => Processor.identity

private def before : Stateful.Vertex Device Nat := ⟨client, input, 0⟩
private def middle : Stateful.Vertex Device Nat := ⟨gateway, translated, 1⟩
private def after : Stateful.Vertex Device Nat := ⟨server, translated, 11⟩

private def vertices := [before, middle, after]

private theorem witnessed : Network.Walk (Stateful.network physical programs) before after vertices :=
  .cons ⟨.inl ⟨rfl, rfl⟩, rfl⟩ (.cons ⟨.inr ⟨rfl, rfl⟩, rfl⟩ (.nil after))

private def observations : List (Processor.Observation (Device × Device)) :=
  [⟨(client, gateway), input, some translated⟩, ⟨(gateway, server), translated, some translated⟩]

example : Stateful.calls vertices = observations := rfl

example :
    (Processor.transition (fun edge : Device × Device => programs edge.1 edge.2)).Trace
      0 observations 11 :=
  Stateful.walk_processor_trace physical programs witnessed

example : Processor.execute (fun edge : Device × Device => programs edge.1 edge.2) 0
    (observations.map Processor.Observation.input) = (11, observations) :=
  Stateful.walk_execute physical programs witnessed

example : (Stateful.calls vertices).length = 2 := by decide

example : Stateful.calls ([] : List (Stateful.Vertex Device Nat)) = [] := rfl

example : Stateful.calls [before] = [] := rfl

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

def run : IO Unit := do
  let projected := Stateful.calls vertices
  ensure (decide (projected = observations)) "Hop projection changed packet order or output headers."
  ensure (projected.length == vertices.length - 1) "Hop projection lost an original edge."
  let replay := Processor.execute (fun edge : Device × Device => programs edge.1 edge.2) 0
    (projected.map Processor.Observation.input)
  ensure (decide (replay = (11, observations))) "Projected execution did not reproduce the exact walk."
  ensure (dependent.run 0 translated == (0, none)) "A fresh store unexpectedly passed the dependent hop."
  ensure (dependent.run 1 input == (1, none)) "The dependent hop ignored the rewritten header."
  ensure (dependent.run 1 translated == (11, some translated)) "The dependent hop did not consume shared state."
  let empty := Processor.execute (fun edge : Device × Device => programs edge.1 edge.2) 0 []
  ensure (decide (empty = (0, []))) "A zero-hop execution changed its store."
  IO.println "Stateful walk execution tests passed."

end NetlibTest.StatefulTrace
