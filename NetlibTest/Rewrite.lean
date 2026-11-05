import Netlib.Packet.Transfer
import Netlib.Routing.Basic

namespace NetlibTest.Rewrite

open Netlib Netlib.Packet

private def original : Header := ⟨167772161, 3325256714, Protocol.tcp, 50000, 443⟩

private def externalEndpoint : Endpoint := ⟨3405803777, 40000⟩

private def serviceEndpoint : Endpoint := ⟨167772162, 8443⟩

private def snat : Packet.Rewrite := Packet.Rewrite.sourceEndpoint externalEndpoint

private def dnat : Packet.Rewrite := Packet.Rewrite.destinationEndpoint serviceEndpoint

private def translated : Header := dnat.apply original

private def changes : List Packet.Rewrite := [snat, dnat, { protocol := some Protocol.udp }]

example (header : Header) : header.reverse.reverse = header := Header.reverse_reverse header

example (first second : Packet.Rewrite) (header : Header) :
    (first.comp second).apply header = second.apply (first.apply header) :=
  Packet.Rewrite.comp_apply first second header

example : (Packet.Rewrite.destinationEndpoint original.sourceEndpoint).apply
    (snat.apply original).reverse = original.reverse :=
  Packet.Rewrite.source_reply_roundtrip original.sourceEndpoint externalEndpoint original rfl

example : (Packet.Rewrite.sourceEndpoint original.destinationEndpoint).apply
    (dnat.apply original).reverse = original.reverse :=
  Packet.Rewrite.destination_reply_roundtrip original.destinationEndpoint serviceEndpoint original rfl

example : snat.apply { original with source := 167772163, sourcePort := 50001 } = snat.apply original := rfl

example : (Packet.Rewrite.Universe.ofRewrites original changes).headerCount = 512 := by decide

example (header : Header) (member : header ∈ (Packet.Rewrite.Universe.ofRewrites original changes).headers) :
    dnat.apply header ∈ (Packet.Rewrite.Universe.ofRewrites original changes).headers :=
  Packet.Rewrite.Universe.rewrite_mem original changes dnat (by simp [changes]) header member

private inductive Device where
  | client
  | gateway
  | server
  deriving Repr, BEq, DecidableEq

open Device

private def physical : Network Device :=
  ⟨fun source target => (source = client ∧ target = gateway) ∨ (source = gateway ∧ target = server)⟩

private def routes (node : Device) : List (Routing.Entry Device) :=
  if node = gateway then [⟨⟨serviceEndpoint.address, 32⟩, some server⟩] else []

private def programs (source target : Device) : Program :=
  if source = client then Program.rewrite dnat
  else ⟨fun before after => Routing.nextHop (routes source) before.destination = some target ∧ after = before⟩

private def transfer : Transfer Device := Transfer.ofPrograms physical programs

private def stale (header : Header) : Network Device :=
  ⟨fun source target => physical.link source target ∧
    (source = client ∨ Routing.nextHop (routes source) header.destination = some target)⟩

private theorem actual_reaches :
    transfer.network.Reachable (client, original) (server, translated) := by
  apply Network.Reachable.step (next := (gateway, translated))
  · change physical.link client gateway ∧ (programs client gateway).run original translated
    constructor
    · exact .inl ⟨rfl, rfl⟩
    · rfl
  · apply Network.Reachable.single
    change physical.link gateway server ∧ (programs gateway server).run translated translated
    constructor
    · exact .inr ⟨rfl, rfl⟩
    · change Routing.nextHop (routes gateway) translated.destination = some server ∧ translated = translated
      exact ⟨by decide, rfl⟩

private theorem stale_misses : ¬(stale original).Reachable client server := by
  have closed : ∀ source target, (stale original).link source target → source ≠ server → target ≠ server := by
    intro source target
    cases source <;> cases target <;> simp only [stale, physical, routes] <;> decide
  have isolated := Network.isolated_of_closed (net := stale original)
    (sources := fun node => node = client) (targets := fun node => node = server)
    (fun node => node ≠ server) closed
    (fun node source => by subst node; decide)
    (fun node target => by subst node; exact fun outside => outside rfl)
  exact isolated client server rfl rfl

example : transfer.network.Reachable (client, original) (server, translated) := actual_reaches

example : ¬(stale original).Reachable client server := stale_misses

example (header : Header) (source target : Device) :
    (Transfer.fixed stale).network.Reachable (source, header) (target, header) ↔
      (stale header).Reachable source target := by
  rw [Transfer.fixed_reachable_iff]
  simp

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

def run : IO Unit := do
  ensure ((snat.apply original).sourceEndpoint == externalEndpoint) "Source translation lost its endpoint."
  ensure ((snat.apply original).destinationEndpoint == original.destinationEndpoint)
    "Source translation changed the destination endpoint."
  ensure (translated.destinationEndpoint == serviceEndpoint) "Destination translation lost its endpoint."
  ensure (translated.sourceEndpoint == original.sourceEndpoint) "Destination translation changed the source endpoint."
  let later : Packet.Rewrite := { destination := some 4294967295 }
  ensure ((dnat.comp later).apply original == later.apply translated) "Later overwrite precedence changed."
  ensure (((dnat.comp later).apply original).destinationPort == 8443)
    "An absent later field discarded an earlier overwrite."
  ensure (Routing.nextHop (routes gateway) original.destination == none) "The stale packet unexpectedly had a route."
  ensure (Routing.nextHop (routes gateway) translated.destination == some server)
    "Routing did not use the translated destination."
  let space := Packet.Rewrite.Universe.ofRewrites original changes
  ensure (space.headerCount == 512 && space.headers.length == space.headerCount)
    "The finite rewrite closure has the wrong size."
  ensure (space.headers.contains original) "The rewrite closure lost the initial header."
  for header in space.headers do
    ensure (space.headers.contains header.reverse) "The finite closure lost a reversed packet."
    for rewrite in changes do
      ensure (space.headers.contains (rewrite.apply header)) "The finite closure lost a rewrite output."
  IO.println "Packet rewrite tests passed."

end NetlibTest.Rewrite
