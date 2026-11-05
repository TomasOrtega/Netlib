import Netlib.Import.NftablesIngress
import Netlib.Protocol.FragmentAdmission

/-!
# IPv4 admission before defragmentation

The source syntax excludes transport reads even when their ranges are tautological.
Source rules and their actual priority remain unchanged in the imported snapshot.
-/

namespace Netlib.Import.NftablesPredefrag

open Packet NftablesSyntax
open Protocol.IngressAttachment (NamespaceRef)
abbrev Binding := NftablesIngress.Binding
abbrev SourceRule := NftablesIngress.SourceRule

structure Snapshot where
  source : NftablesIngress.Snapshot
  noPorts : IngressPolicy.NoPorts source.compile

def Snapshot.guard (snapshot : Snapshot) : Protocol.FragmentAdmission.EarlyGuard :=
  ⟨snapshot.source.compile, snapshot.noPorts⟩

theorem Snapshot.guard_allows (snapshot : Snapshot) (index : Nat) (header : Header) :
    snapshot.guard.policy.allows index header = snapshot.source.permits index header :=
  snapshot.source.compile_allows index header

private def parseMatch (bindings : List Binding) (rule : SourceRule) (json : Lean.Json) (index : Nat) : Except String SourceRule := do
  fields json ["left", "right", "op"]
  require ((← str json "op") == "==") "Use equality in the selected early IPv4 guard."
  let (kind, left) ← singleton (← json.getObjVal? "left")
  if kind == "meta" then
    fields left ["key"]
    require ((← str left "key") == "iif" && rule.ingress.isNone) "Use one numeric input-interface equality per rule."
    let selected ← NftablesIngress.resolve bindings (← json.getObjVal? "right")
    return { rule with ingress := some selected, ingressExpressionIndex := some index }
  require (kind == "payload") "Only numeric ingress and IPv4 header predicates precede defragmentation."
  fields left ["protocol", "field"]
  require ((← str left "protocol") == "ip") "Transport selectors cannot be read before defragmentation."
  if (← str left "field") == "protocol" then
    require rule.protocol.isNone "Use one IPv4 protocol predicate per early rule."
  let test ← parseHeaderMatch rule.toSourceRule.compile.test json
  require (test.sourcePorts.isNone && test.destinationPorts.isNone) "Early IPv4 guard predicates must be independent of transport ports."
  return { rule with
    source := test.source
    destination := test.destination
    protocol := test.protocol
    sourcePorts := test.sourcePorts
    destinationPorts := test.destinationPorts }

private def parseLog (rule : SourceRule) (json : Lean.Json) (index : Nat) : Except String SourceRule := do
  fields json ["prefix", "group", "snaplen", "queue-threshold"]
  let label ← str json "prefix"
  require ((label == "FRAG_ALLOW" || label == "FRAG_DROP") && rule.logPrefix.isNone &&
    (← nat json "group") == 42 && (← nat json "snaplen") == 65531 && (← nat json "queue-threshold") == 1)
    "Require the selected early fragment NFLOG statement without extra flags."
  return { rule with logPrefix := some label, logExpressionIndex := some index }

private def parseRule (bindings : List Binding) (input : RuleInput) : Except String SourceRule := do
  let mut rule : SourceRule := {
    action := .deny, objectIndex := input.objectIndex, expressionIndices := input.expressionIndices,
    verdictIndex := 0, handle := input.handle, sourceID := input.sourceID, comment := input.comment }
  let mut finished := false
  for index in [:input.expressions.size] do
    require (!finished) "An early guard expression follows its terminal verdict."
    let (kind, value) ← singleton input.expressions[index]!
    match kind with
    | "match" =>
      require rule.logPrefix.isNone "Place every early predicate before its decision log."
      rule ← parseMatch bindings rule value index
    | "log" => rule ← parseLog rule value index
    | "accept" | "drop" =>
      require (value == .null) "An early verdict must have a null value."
      rule := { rule with action := ← action kind, verdictIndex := index }
      finished := true
    | _ => throw "The early guard supports IPv4/ingress predicates, selected NFLOG, and a terminal verdict."
  require finished "An early guard rule needs a terminal verdict."
  if let some label := rule.logPrefix then
    require ((label == "FRAG_ALLOW") == (rule.action == .permit)) "The early NFLOG label contradicts its verdict."
  return rule

def Snapshot.fromJson (ns : NamespaceRef) (bindings : List Binding) (json : Lean.Json) : Except String Snapshot := do
  require (0 < ns.id && bindings.all (fun binding => decide (binding.reference.ns = ns) &&
    !binding.name.isEmpty && binding.name.utf8ByteSize < 16)) "Resolve early ingress names within the declared namespace lifetime."
  require (decide (bindings.map (·.name)).Nodup && decide (bindings.map (·.reference.ifindex.val)).Nodup)
    "Early interface names and numeric indices must be unique."
  let envelope ← envelope json ["prerouting"]
  require (envelope.priority == -450) "The selected early guard must precede defragmentation at priority -450."
  let rules ← envelope.rules.mapM (parseRule bindings)
  let source : NftablesIngress.Snapshot := ⟨envelope, ns, bindings, rules, json⟩
  if checked : IngressPolicy.noPorts source.compile = true then
    return ⟨source, (IngressPolicy.noPorts_correct _).mp checked⟩
  else throw "The imported early guard contains an unavailable transport selector."

end Netlib.Import.NftablesPredefrag
