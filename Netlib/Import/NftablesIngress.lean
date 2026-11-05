import Netlib.Import.Nftables
import Netlib.Packet.IngressPolicy
import Netlib.Protocol.IngressAttachment

/-!
# Early IPv4 ingress filters

Numeric iif expressions can export a current device name as their JSON value.
Resolution uses the supplied contemporaneous namespace and interface bindings.
Names and controller births do not change the installed numeric rule's semantics.
-/

namespace Netlib.Import.NftablesIngress

open Packet NftablesSyntax
open Protocol.IngressAttachment (NamespaceRef InterfaceRef)

structure Binding where
  name : String
  reference : InterfaceRef
  deriving Repr, DecidableEq

structure SourceRule extends Nftables.SourceRule where
  ingress : Option Nat := none
  ingressExpressionIndex : Option Nat := none
  logPrefix : Option String := none
  logExpressionIndex : Option Nat := none
  deriving Repr

def SourceRule.accepts (rule : SourceRule) (index : Nat) (header : Header) : Bool :=
  (match rule.ingress with | none => true | some selected => decide (index = selected)) &&
    rule.toSourceRule.accepts header

def SourceRule.compile (rule : SourceRule) : IngressPolicy.Rule :=
  ⟨rule.ingress, rule.toSourceRule.compile.test, rule.action⟩

theorem SourceRule.compile_accepts (rule : SourceRule) (index : Nat) (header : Header) :
    rule.compile.accepts index header = rule.accepts index header := by
  change ((match rule.ingress with | none => true | some selected => decide (index = selected)) &&
      rule.toSourceRule.compile.test.accepts header) =
    ((match rule.ingress with | none => true | some selected => decide (index = selected)) &&
      rule.toSourceRule.accepts header)
  rw [Nftables.SourceRule.compile_accepts]

private def evaluateRules (fallback : Action) : List SourceRule → Nat → Header → Action
  | [], _, _ => fallback
  | rule :: rules, index, header =>
    if rule.accepts index header then rule.action else evaluateRules fallback rules index header

structure Snapshot where
  source : NftablesSyntax.Envelope
  ns : NamespaceRef
  bindings : List Binding
  rules : List SourceRule
  raw : Lean.Json

def Snapshot.compile (snapshot : Snapshot) : IngressPolicy.Policy :=
  ⟨snapshot.rules.map SourceRule.compile, snapshot.source.policy⟩

def Snapshot.evaluate (snapshot : Snapshot) (index : Nat) (header : Header) : Action :=
  evaluateRules snapshot.source.policy snapshot.rules index header

private theorem specialize_evaluate (rules : List SourceRule) (fallback : Action) (index : Nat) (header : Header) :
    (⟨rules.map SourceRule.compile, fallback⟩ : IngressPolicy.Policy).evaluate index header =
      evaluateRules fallback rules index header := by
  induction rules with
  | nil => exact IngressPolicy.Policy.evaluate_nil fallback index header
  | cons rule rules ih =>
    rw [List.map_cons, IngressPolicy.Policy.evaluate_cons, SourceRule.compile_accepts]
    simp only [evaluateRules, ih, SourceRule.compile]

theorem Snapshot.compile_evaluate (snapshot : Snapshot) (index : Nat) (header : Header) :
    snapshot.compile.evaluate index header = snapshot.evaluate index header := specialize_evaluate _ _ _ _

def Snapshot.permits (snapshot : Snapshot) (index : Nat) (header : Header) : Bool :=
  decide (snapshot.evaluate index header = .permit)

theorem Snapshot.compile_allows (snapshot : Snapshot) (index : Nat) (header : Header) :
    snapshot.compile.allows index header = snapshot.permits index header := by
  change decide (snapshot.compile.evaluate index header = .permit) = _
  rw [snapshot.compile_evaluate]
  rfl

private def ifindex (json : Lean.Json) : Except String Nat := do
  let value ← json.getNat?
  require (0 < value && value ≤ 2147483647) "An input interface index must be positive and fit a Linux signed index."
  return value

def namespaceFromJson (json : Lean.Json) : Except String NamespaceRef := do
  fields json ["id", "birth"]
  let id ← nat json "id"
  require (0 < id) "A namespace identity must be positive."
  return ⟨id, ← nat json "birth"⟩

def interfaceFromJson (json : Lean.Json) : Except String InterfaceRef := do
  fields json ["namespace", "ifindex", "birth"]
  let index ← ifindex (← json.getObjVal? "ifindex")
  if bounded : 0 < index ∧ index ≤ 2147483647 then
    return ⟨← namespaceFromJson (← json.getObjVal? "namespace"), ⟨index, bounded⟩, ← nat json "birth"⟩
  else throw "An input interface index exceeds the selected Linux domain."

def bindingsFromJson (ns : NamespaceRef) (json : Lean.Json) : Except String (List Binding) := do
  let values ← json.getArr?
  let mut bindings : List Binding := []
  for value in values do
    fields value ["name", "reference"]
    let name ← str value "name"
    require (!name.isEmpty && name.utf8ByteSize < 16) "Use a nonempty Linux interface name shorter than IFNAMSIZ."
    let reference ← interfaceFromJson (← value.getObjVal? "reference")
    require (decide (reference.ns = ns)) "An interface binding belongs to a different namespace lifetime."
    require (!(bindings.any (fun previous => previous.name == name ||
      decide (previous.reference.ifindex.val = reference.ifindex.val)))) "Interface names and numeric indices must be unique."
    bindings := bindings ++ [⟨name, reference⟩]
  return bindings

def resolve (bindings : List Binding) (json : Lean.Json) : Except String Nat := do
  match json with
  | .num _ => ifindex json
  | .str name =>
    let some binding := bindings.find? (·.name == name)
      | throw "A numeric iif export names no current interface in this namespace."
    return binding.reference.ifindex.val
  | _ => throw "Numeric iif requires an index or a current exported interface name."

private def parseMatch (bindings : List Binding) (rule : SourceRule) (json : Lean.Json) (index : Nat) : Except String SourceRule := do
  fields json ["left", "right", "op"]
  let (kind, value) ← singleton (← json.getObjVal? "left")
  if kind == "meta" then
    fields value ["key"]
    if (← str value "key") == "iif" then
      require ((← str json "op") == "==" && rule.ingress.isNone) "Use one numeric input-interface equality per rule."
      let selected ← resolve bindings (← json.getObjVal? "right")
      return { rule with ingress := some selected, ingressExpressionIndex := some index }
  let test ← parseHeaderMatch rule.toSourceRule.compile.test json
  return { rule with
    source := test.source, destination := test.destination, protocol := test.protocol,
    sourcePorts := test.sourcePorts, destinationPorts := test.destinationPorts }

private def parseLog (rule : SourceRule) (json : Lean.Json) (index : Nat) : Except String SourceRule := do
  fields json ["prefix", "group", "snaplen", "queue-threshold"]
  let label ← str json "prefix"
  require ((label == "ATTACH_ALLOW" || label == "ATTACH_DROP") && rule.logPrefix.isNone &&
    (← nat json "group") == 42 && (← nat json "snaplen") == 65531 && (← nat json "queue-threshold") == 1)
    "Require one selected attachment NFLOG observation without extra flags."
  return { rule with logPrefix := some label, logExpressionIndex := some index }

private def parseRule (bindings : List Binding) (input : RuleInput) : Except String SourceRule := do
  let mut rule : SourceRule := {
    action := .deny, objectIndex := input.objectIndex, expressionIndices := input.expressionIndices,
    verdictIndex := 0, handle := input.handle, sourceID := input.sourceID, comment := input.comment }
  let mut finished := false
  for index in [:input.expressions.size] do
    require (!finished) "An ingress expression follows its terminal verdict."
    let (kind, value) ← singleton input.expressions[index]!
    match kind with
    | "match" => rule ← parseMatch bindings rule value index
    | "log" => rule ← parseLog rule value index
    | "accept" | "drop" =>
      require (value == .null) "An ingress verdict must have a null value."
      rule := { rule with action := ← action kind, verdictIndex := index }
      finished := true
    | _ => throw "Only ingress/header matches, selected NFLOG, and terminal verdicts are supported."
  require finished "An ingress rule needs a terminal verdict."
  if let some label := rule.logPrefix then
    require ((label == "ATTACH_ALLOW") == (rule.action == .permit)) "The attachment NFLOG label contradicts its verdict."
  return rule

def Snapshot.fromJson (ns : NamespaceRef) (bindings : List Binding) (json : Lean.Json) : Except String Snapshot := do
  require (0 < ns.id && bindings.all (fun binding =>
    decide (binding.reference.ns = ns) && !binding.name.isEmpty && binding.name.utf8ByteSize < 16))
    "Resolve ingress names only within the declared current namespace and valid interface names."
  require (decide (bindings.map (·.name)).Nodup && decide (bindings.map (·.reference.ifindex.val)).Nodup)
    "Current interface names and numeric indices must be unique."
  let source ← envelope json ["prerouting"]
  require (source.priority == -300) "The selected ingress guard must precede ordinary conntrack at raw priority -300."
  let rules ← source.rules.mapM (parseRule bindings)
  return ⟨source, ns, bindings, rules, json⟩

end Netlib.Import.NftablesIngress
