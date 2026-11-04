import Netlib.Packet.Stateful

namespace NetlibTest.Stateful

open Netlib Packet Packet.Stateful

private inductive Node where
  | client | authorizer | service | isolated
  deriving Repr, DecidableEq

private def header : Header := ⟨167772161, 3325256705, Protocol.tcp, 40000, 443⟩

private def physical : Network Node where
  link source target := (source = .client ∧ target = .authorizer) ∨
    (source = .authorizer ∧ target = .service)

private def grant : Processor Bool := ⟨fun _ packet => (true, some packet)⟩
private def requireGrant : Processor Bool := ⟨fun allowed packet => (allowed, if allowed then some packet else none)⟩
private def grantThenDrop : Processor Bool := ⟨fun _ _ => (true, none)⟩

private def programs (source _target : Node) : Processor Bool :=
  if source = .client then grant else requireGrant

private def start : Vertex Node Bool := ⟨.client, header, false⟩
private def middle : Vertex Node Bool := ⟨.authorizer, header, true⟩
private def finish : Vertex Node Bool := ⟨.service, header, true⟩

/-- The first hop changes the store needed by the second hop. -/
private theorem reaches_with_grant : (network physical programs).Reachable start finish :=
  .step (next := middle) ⟨.inl ⟨rfl, rfl⟩, rfl⟩ (.single ⟨.inr ⟨rfl, rfl⟩, rfl⟩)

example : physical.Reachable .client .service := reachable_physical physical programs reaches_with_grant

example (packet output : Header) (after : Bool) :
    ¬(network physical programs).link ⟨.authorizer, packet, false⟩ ⟨.service, output, after⟩ := by
  rintro ⟨_, executed⟩
  have impossible := congrArg Prod.snd executed
  cases impossible

example : (network physical programs).Reachable start finish := reaches_with_grant

private def statelessPrograms : Node → Node → Header → Option Header := fun _ _ packet =>
  some ({ packet with destinationPort := 8443 })

/-- Choosing a different final store cannot create a stateless forwarding path. -/
example : ¬(network physical (stateless statelessPrograms)).Reachable
    start ⟨.service, { header with destinationPort := 8443 }, true⟩ := by
  intro path
  have unchanged := stateless_store physical statelessPrograms path
  cases unchanged

example (before after : Vertex Node Bool) :
    (network physical (stateless statelessPrograms)).Reachable before after ↔
      after.store = before.store ∧ (statelessTransfer physical statelessPrograms).network.Reachable
        (before.node, before.header) (after.node, after.header) := stateless_reachable_iff _ _ _ _

private theorem grant_preserved (source target : Node) :
    (programs source target).Preserves (· = true) := by
  intro allowed packet initial
  by_cases sourceIsClient : source = .client <;>
    simp [programs, sourceIsClient, grant, requireGrant, initial]

example {before after : Vertex Node Bool} (path : (network physical programs).Reachable before after)
    (initial : before.store = true) : after.store = true :=
  invariant physical programs (· = true) grant_preserved path initial

private theorem isolated_node : physical.Isolated (· = .client) (· = .isolated) := by
  apply Network.isolated_of_closed (fun node => node ≠ .isolated)
  · intro source target edge _ same
    subst target
    simp [physical] at edge
  · intro source same
    subst source
    decide
  · intro target same outside
    exact outside same

example : (network physical programs).Isolated (fun vertex => vertex.node = .client)
    (fun vertex => vertex.node = .isolated) := isolated_of_physical physical programs isolated_node

example : (grantThenDrop.seq requireGrant).run false header = (true, none) := rfl

example {before after : Vertex Node Bool} :
    ¬(network physical (fun _ _ => grantThenDrop)).link before after := by
  rintro ⟨_, executed⟩
  have impossible := congrArg Prod.snd executed
  cases impossible

example : ¬(network physical (fun _ _ => grantThenDrop)).Reachable start finish := by
  intro path
  cases path with
  | step edge _ =>
    have impossible := congrArg Prod.snd edge.2
    cases impossible

private def ensure (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

def run : IO Unit := do
  let first := (programs .client .authorizer).run false header
  let second := (programs .authorizer .service).run first.1 header
  ensure (first.1 && second.2.isSome) "The later hop must see the earlier grant."
  ensure ((requireGrant.run false header).2.isNone)
    "A hop must not choose an unrelated authorized store."
  let dropped := (grantThenDrop.seq requireGrant).run false header
  ensure (dropped.1 && dropped.2.isNone) "A drop must retain completed state updates without forwarding."
  let rewritten := (stateless statelessPrograms : Node → Node → Processor Bool) .client .authorizer
  ensure (!(rewritten.run false header).1 &&
    (rewritten.run false header).2 == some { header with destinationPort := 8443 })
    "A stateless header rewrite must retain its input store."
  IO.println "Stateful forwarding tests passed."

end NetlibTest.Stateful
