import Netlib.Protocol.FlowNAT

namespace NetlibTest.FlowNAT

open Netlib.Packet Netlib.Protocol.FlowNAT

private def original : Header := ⟨167772161, 3325256705, Protocol.tcp, 40000, 443⟩
private def publicEndpoint : Endpoint := ⟨3405803777, 62000⟩
private def backend : Endpoint := ⟨167772162, 8443⟩

private def snat : Entry :=
  ⟨original, ((Rewrite.sourceEndpoint publicEndpoint).apply original).reverse, 0, 0, 0⟩

private def dnat : Entry :=
  ⟨original, ((Rewrite.destinationEndpoint backend).apply original).reverse, 0, 0, 30⟩

private def combined : Entry :=
  ⟨original, ((Rewrite.destinationEndpoint backend).apply
    ((Rewrite.sourceEndpoint publicEndpoint).apply original)).reverse, 0, 0, 30⟩

private def peer : Entry :=
  let input := { original with source := 167772163, sourcePort := 40001, destination := 3325256706 }
  ⟨input, ((Rewrite.sourceEndpoint publicEndpoint).apply input).reverse, 0, 0, 20⟩

private def portPeer : Entry :=
  let input := { original with source := 167772164, sourcePort := 40002, destinationPort := 80 }
  ⟨input, ((Rewrite.sourceEndpoint publicEndpoint).apply input).reverse, 0, 0, 20⟩

example : (⟨[snat, peer, portPeer]⟩ : Snapshot).Valid :=
  (Snapshot.check_correct _).mp (by decide)

example : snat.remainingTTL = 0 ∧ snat.WellFormed := ⟨rfl, (Entry.check_correct _).mp (by decide)⟩

example : snat.sourceOnly := rfl
example : dnat.destinationOnly := rfl

example : (⟨[combined]⟩ : Snapshot).translate 0 combined.reply = some original.reverse := by decide

example : (Snapshot.translate ⟨[combined]⟩ 0 original).bind
    (fun wire => Snapshot.translate ⟨[combined]⟩ 0 wire.reverse) = some original.reverse :=
  Snapshot.roundtrip (⟨[combined]⟩ : Snapshot)
    ((Snapshot.check_correct (⟨[combined]⟩ : Snapshot)).mp (by decide)) combined (by simp)

private def ensure (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

def run : IO Unit := do
  for entry in [snat, dnat, combined] do
    let snapshot : Snapshot := ⟨[entry]⟩
    ensure snapshot.check "Each coherent tuple pair must validate."
    ensure (snapshot.translate entry.originalZone entry.original == some entry.reply.reverse)
      "Original-direction projection must use the reversed reply tuple."
    ensure (snapshot.translate entry.replyZone entry.reply == some entry.original.reverse)
      "Reply-direction projection must restore the reversed original tuple."
    for direction in [Direction.original, Direction.reply] do
      ensure ((entry.rewrite direction).apply (entry.input direction) == entry.output direction)
        "Endpoint rewrites must preserve the tuple-pair meaning."
  let peers : Snapshot := ⟨[snat, peer, portPeer]⟩
  ensure peers.check "Independent remote peers may share a public endpoint."
  for entry in peers.entries do
    ensure (peers.translate 0 entry.reply == some entry.original.reverse)
      "Full remote tuples must select the correct private flow."
  ensure ((peers.translate 1 original).isNone) "The lookup zone must participate in the key."
  ensure ((peers.translate 0 { original with sourcePort := 1 }).isNone)
    "An unknown five-tuple must remain untracked."
  let duplicate : Snapshot := ⟨[snat, snat]⟩
  ensure (!duplicate.check) "Duplicate flow keys must be rejected."
  let crossing : Entry := ⟨snat.reply, original, 0, 0, 20⟩
  ensure crossing.check "Each crossing entry is individually well formed."
  ensure (!(⟨[snat, crossing]⟩ : Snapshot).check)
    "An original key colliding with another reply key must be rejected."
  let symmetric : Entry := ⟨original, original, 0, 0, 10⟩
  ensure (!symmetric.check) "Identical direction keys must be rejected."
  let separated := { symmetric with replyZone := 1 }
  ensure (⟨[separated]⟩ : Snapshot).check "Distinct zones can distinguish identical tuple headers."
  let zones : Snapshot := ⟨[snat, { snat with originalZone := 1, replyZone := 1 }]⟩
  ensure zones.check "The same tuple pair may appear in distinct zones."
  ensure (!(⟨[{ snat with originalZone := 65536 }]⟩ : Snapshot).check)
    "Zones outside the native 16-bit range must be rejected."
  ensure (!(⟨[{ snat with remainingTTL := 4294967296 }]⟩ : Snapshot).check)
    "Timeout evidence outside the native 32-bit range must be rejected."
  ensure (!(⟨[{ snat with reply := { snat.reply with protocol := Protocol.udp } }]⟩ : Snapshot).check)
    "The tuple pair must preserve its transport protocol."
  let unsupported : Entry := { snat with
    original := { original with protocol := Protocol.icmp }
    reply := { snat.reply with protocol := Protocol.icmp } }
  ensure (!unsupported.check) "Unsupported transport tuples must be rejected."
  ensure (snat.remainingTTL == 0 && snat.check) "Zero remaining seconds must remain valid captured evidence."
  IO.println "Flow tuple projection tests passed."

end NetlibTest.FlowNAT
