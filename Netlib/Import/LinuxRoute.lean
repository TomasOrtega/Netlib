import Lean
import Netlib.Import.IPv4
import Netlib.Import.Json
import Netlib.Routing.Basic

/-!
# Linux main-table route snapshots

The input is the IPv4 JSON output of iproute2 6.19.0.
Bindings identify the modeled neighbor for each device and gateway pair.
This model covers transit forwarding after main-table selection.
It excludes the routing policy database, local delivery, and neighbor discovery.
-/

namespace Netlib.Import.LinuxRoute

open Packet

def sourceVersion : String := "iproute2-6.19.0"
def sourceURL : String := "https://raw.githubusercontent.com/iproute2/iproute2/v6.19.0/ip/iproute.c"

structure Binding where
  device : String
  nextNode : String
  gateway : Option Address := none
  deriving Repr, BEq, DecidableEq

inductive Kind where
  | unicast | blackhole | unreachable | prohibit
  deriving Repr, BEq, DecidableEq

structure Route where
  index : Nat
  original : Lean.Json
  destination : Prefix
  kind : Kind
  output : Option Binding
  metric : Option Nat
  protocol : Option String
  scope : Option String
  preferredSource : Option Address

namespace Route

def nextNode (route : Route) : Option String :=
  match route.kind with
  | .unicast => route.output.map Binding.nextNode
  | .blackhole | .unreachable | .prohibit => none

def compile (route : Route) : Routing.Entry String :=
  ⟨route.destination, route.nextNode⟩

def location (route : Route) : String := s!"/{route.index}"

end Route

structure Snapshot where
  routes : List Route
  bindings : List Binding

namespace Snapshot

def compile (snapshot : Snapshot) : List (Routing.Entry String) :=
  snapshot.routes.map Route.compile

private def select (selected : Option Route) (candidate : Route) (address : Address) : Option Route :=
  if candidate.destination.contains address then
    match selected with
    | none => some candidate
    | some previous =>
      if previous.destination.length.val < candidate.destination.length.val then some candidate
      else selected
  else selected

/-- Scan the structured records independently of the compiled route table. -/
def selected (snapshot : Snapshot) (address : Address) : Option Route :=
  snapshot.routes.foldl (fun previous candidate => select previous candidate address) none

def nextNode (snapshot : Snapshot) (address : Address) : Option String :=
  (snapshot.selected address).bind Route.nextNode

private theorem select_compile (previous : Option Route) (candidate : Route) (address : Address) :
    (select previous candidate address).map Route.compile =
      Routing.prefer (previous.map Route.compile)
        (if candidate.destination.contains address then some candidate.compile else none) := by
  cases previous with
  | none => cases matched : candidate.destination.contains address <;>
      simp [select, matched, Routing.prefer]
  | some previous =>
    cases matched : candidate.destination.contains address
    · simp [select, matched, Routing.prefer]
    · by_cases longer : previous.destination.length.val < candidate.destination.length.val <;>
        simp [select, matched, longer, Route.compile, Routing.prefer, Routing.Entry.rank]

private theorem scan_compile (routes : List Route) (previous : Option Route) (address : Address) :
    (routes.foldl (fun previous candidate => select previous candidate address) previous).map
        Route.compile =
      Routing.prefer (previous.map Route.compile) (Routing.lookup (routes.map Route.compile) address) := by
  induction routes generalizing previous with
  | nil => cases previous <;> rfl
  | cons route routes ih =>
    simp only [List.foldl_cons, List.map_cons, ih, select_compile, Routing.lookup,
      Routing.prefer_assoc]
    rfl

theorem selected_compile (snapshot : Snapshot) (address : Address) :
    (snapshot.selected address).map Route.compile = Routing.lookup snapshot.compile address := by
  simpa only [selected, compile, Option.map_none, Routing.prefer] using
    scan_compile snapshot.routes none address

theorem nextHop_correct (snapshot : Snapshot) (address : Address) :
    Routing.nextHop snapshot.compile address = snapshot.nextNode address := by
  rw [Routing.nextHop, ← selected_compile]
  unfold nextNode
  cases snapshot.selected address <;> rfl

end Snapshot

private def require (condition : Bool) (message : String) : Except String Unit :=
  if condition then .ok () else .error message

private def nameOK (name : String) : Bool :=
  !name.isEmpty && name.toList.all (fun c => c.isAlphanum || c == '_' || c == '-' || c == '.')

private def fields (json : Lean.Json) : Except String Unit := do
  let object ← json.getObj?
  let allowed := ["dst", "type", "dev", "gateway", "metric", "protocol", "scope", "prefsrc", "flags", "table"]
  for (key, _) in object.toList do
    require (allowed.contains key) s!"Unsupported route field: {key}."
  let _ ← json.getObjVal? "dst"

private def optional (json : Lean.Json) (name : String)
    (parse : Lean.Json → Except String α) : Except String (Option α) :=
  match (json.getObjVal? name).toOption with
  | none => .ok none
  | some value => some <$> parse value

private def string (json : Lean.Json) : Except String String := do
  let value ← json.getStr?
  require (!value.isEmpty) "Empty route metadata."
  return value

private def metric (json : Lean.Json) : Except String Nat := do
  let number ← json.getNat?
  require (number < 4294967296) "Route metric exceeds 32 bits."
  return number

private def destination (value : String) : Except String Prefix := do
  let block ← IPv4.parsePrefix (if value == "default" then "0.0.0.0/0" else value)
  let width := 2 ^ (32 - block.length.val)
  require (block.address.val % width == 0) "A route destination must be a canonical prefix."
  return block

private def parseKind (value : Option String) : Except String Kind :=
  match value with
  | none | some "unicast" => .ok .unicast
  | some "blackhole" => .ok .blackhole
  | some "unreachable" => .ok .unreachable
  | some "prohibit" => .ok .prohibit
  | some value => .error s!"Unsupported route type: {value}."

private def validateBindings (bindings : List Binding) : Except String Unit := do
  let mut seen : List (String × Option Address) := []
  for binding in bindings do
    require (nameOK binding.device && binding.device.toUTF8.size ≤ 15) "Invalid route device binding."
    require (nameOK binding.nextNode) "Invalid route next-node binding."
    let key := (binding.device, binding.gateway)
    require (!seen.contains key) "Duplicate route device and gateway binding."
    seen := key :: seen

private def bindingFor (bindings : List Binding) (device : String) (gateway : Option Address) :
    Except String Binding := do
  let matchingDevice := bindings.filter (·.device == device)
  require (!matchingDevice.isEmpty) s!"Unbound route output interface: {device}."
  match matchingDevice.find? (·.gateway == gateway) with
  | some binding => return binding
  | none => throw s!"The gateway does not match the binding for {device}."

private def validateTable (json : Lean.Json) : Except String Unit := do
  match (json.getObjVal? "table").toOption with
  | none => pure ()
  | some (.str "main") | some (.str "254") => pure ()
  | some value => require (value.getNat?.toOption == some 254) "Only the main route table is supported."

private def parseRoute (bindings : List Binding) (index : Nat) (json : Lean.Json) :
    Except String Route := do
  fields json
  validateTable json
  match (json.getObjVal? "flags").toOption with
  | none => pure ()
  | some flags =>
    require (← flags.getArr?).isEmpty "Route flags are unsupported."
  let block ← destination (← (← json.getObjVal? "dst").getStr?)
  let kind ← parseKind (← optional json "type" string)
  let device ← optional json "dev" string
  let gateway ← optional json "gateway" (fun value => do IPv4.parseAddress (← value.getStr?))
  let scope ← optional json "scope" string
  match scope with
  | none => pure ()
  | some value =>
    require (["global", "link", "0", "253"].contains value) "Unsupported route scope."
  let preferredSource ← optional json "prefsrc" (fun value => do IPv4.parseAddress (← value.getStr?))
  let output ← match kind with
    | .unicast => do
      let some device := device | throw "A unicast route needs an output device."
      some <$> bindingFor bindings device gateway
    | .blackhole | .unreachable | .prohibit => do
      require (device.isNone && gateway.isNone && preferredSource.isNone)
        "A drop route cannot supply a device, gateway, or preferred source."
      pure none
  return ⟨index, json, block, kind, output, ← optional json "metric" metric,
    ← optional json "protocol" string, scope, preferredSource⟩

/-- Reject equal canonical prefixes instead of guessing metric or multipath selection. -/
def Snapshot.fromJson (json : Lean.Json) (bindings : List Binding) : Except String Snapshot := do
  validateBindings bindings
  let values ← json.getArr?
  let mut routes : List Route := []
  for index in [:values.size] do
    let route ← (parseRoute bindings index values[index]!).mapError (s!"route /{index}: " ++ ·)
    require (!(routes.any (fun previous => previous.destination == route.destination)))
      s!"route /{index}: duplicate destination prefix; metric and multipath choices are unsupported."
    routes := routes ++ [route]
  return ⟨routes, bindings⟩

def Snapshot.parse (text : String) (bindings : List Binding) : Except String Snapshot := do
  Snapshot.fromJson (← Netlib.Import.Json.parse text) bindings

end Netlib.Import.LinuxRoute
