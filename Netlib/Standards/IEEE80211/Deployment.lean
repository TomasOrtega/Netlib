import Netlib.Standards.IEEE80211.Enterprise
import Netlib.Check.DataPlane

namespace Netlib.Wifi

open Standards

structure Binding where
  interface : String
  node : String
  bridge : Option String
  deriving Repr

private def fields (json : Lean.Json) (names : List String) : Except String Unit := do
  let object ← json.getObj?
  for (name, _) in object.toList do
    if !names.contains name then throw s!"Unknown Wi-Fi deployment field: {name}."
  for name in names do
    let _ ← json.getObjVal? name

private def string (json : Lean.Json) (name : String) : Except String String := do
  (← json.getObjVal? name).getStr?

/-- The profile fixes its queries so that an input cannot remove an obligation. -/
def deploymentQueries (ap : String) : List DataPlane.Query := [
  ⟨"WIFI-SERVICE", .reach, .zone "guest", .zone "services", "https", "guest-traffic", none⟩,
  ⟨"WIFI-MANAGEMENT", .isolate, .zone "guest", .zone "management", "management", "guest-traffic", none⟩,
  ⟨"WIFI-GATEWAY", .mediated, .zone "guest", .zone "services", "https", "guest-traffic", some (.group "boundary")⟩,
  ⟨"WIFI-AP", .mediated, .zone "guest", .zone "services", "https", "guest-traffic", some (.node ap)⟩,
  ⟨"WIFI-IDENTITY", .isolate, .zone "guest", .zone "services", "https", "unknown-traffic", none⟩]

private def parseDeployment (ap : Hostapd.Config) (text : String) :
    Except String (Binding × DataPlane.Config) := do
  let json ← Lean.Json.parse text
  fields json ["schema", "binding", "model"]
  if (← (← json.getObjVal? "schema").getNat?) != 1 then throw "Use Wi-Fi deployment schema 1."
  let bindingJson ← json.getObjVal? "binding"
  fields bindingJson ["interface", "node", "bridge"]
  let bridge ← match ← bindingJson.getObjVal? "bridge" with
    | .null => pure none
    | value => some <$> value.getStr?
  let binding : Binding := ⟨← string bindingJson "interface", ← string bindingJson "node", bridge⟩
  let config ← DataPlane.Config.fromJson (← json.getObjVal? "model")
  if ap.get? "interface" != some binding.interface then
    throw "The modeled AP interface does not match hostapd."
  if ap.get? "bridge" != binding.bridge then
    throw "The modeled AP bridge does not match hostapd."
  let accessPoints := config.devices.filter (·.role == "access-point")
  if accessPoints.map (·.id) != [binding.node] then
    throw "Bind exactly one modeled access point to the hostapd file."
  if !(config.select config.enforcement).contains binding.node then
    throw "The imported AP must belong to the enforcement group."
  if config.requirements != deploymentQueries binding.node then
    throw "The deployment must contain every fixed Wi-Fi query in order."
  return (binding, config)

private def localRequirement (query : DataPlane.Query) : Standards.Requirement :=
  ⟨query.id,
   ⟨"Netlib Wi-Fi deployment policy", "1", query.id,
    "https://github.com/TomasOrtega/Netlib/blob/main/docs/WIFI.md#deployment-policy"⟩,
   match query.id with
    | "WIFI-SERVICE" => "Permit the selected guest HTTPS traffic to the service."
    | "WIFI-MANAGEMENT" => "Block the selected guest traffic to the management network."
    | "WIFI-GATEWAY" => "Route each selected service path through the boundary gateway."
    | "WIFI-AP" => "Route each selected service path through the imported AP."
    | "WIFI-IDENTITY" => "Block service traffic for the unauthenticated request."
    | _ => "Check the named deployment query.",
   "Every selected endpoint pair for the named packet header and request",
   ["The reviewer maps the hostapd interface and bridge to the modeled AP.",
    "The supplied identity facts describe the AP's authenticated stations.",
    "Routes, packet rules, and physical links describe the reviewed deployment."]⟩

private def networkFinding (result : (query : DataPlane.Query) ×
    DataPlane.Check.Checked (query.Meaning config)) : Finding :=
  ⟨localRequirement result.1, if result.2.value then .satisfied else .violated, result.2.evidence⟩

/-- Each network status carries the exact data-plane query meaning. -/
theorem network_finding_correct (result : (query : DataPlane.Query) ×
    DataPlane.Check.Checked (query.Meaning config)) :
    (networkFinding result).status = .satisfied ↔ result.1.Meaning config := by
  have correct := result.2.correct
  cases value : result.2.value <;> simp [networkFinding, value] at correct ⊢ <;> exact correct

/-- The combined report keeps every AP check and every fixed network query. -/
def deploymentReport (ap : Hostapd.Config) (network : DataPlane.Check.Report config) : Report :=
  ⟨"Netlib enterprise Wi-Fi deployment subset 1",
    (check ap).findings ++ network.results.map networkFinding⟩

/-- Passing both reports is equivalent to passing their combined report. -/
theorem deployment_report_iff (ap : Hostapd.Config) (network : DataPlane.Check.Report config) :
    (deploymentReport ap network).compliant = true ↔
      (check ap).compliant = true ∧ network.compliant = true := by
  have nonempty : (check ap).findings.isEmpty = false := rfl
  have combinedNonempty :
      ((check ap).findings ++ network.results.map networkFinding).isEmpty = false := by
    rfl
  have sameCheck : (fun a : (query : DataPlane.Query) ×
      DataPlane.Check.Checked (query.Meaning config) => (networkFinding a).status.passes) =
      (fun a => a.2.value) := by
    funext result
    cases value : result.2.value <;> simp [networkFinding, value, Status.passes]
  simp only [Report.compliant, deploymentReport, combinedNonempty, nonempty,
    Bool.not_false, Bool.true_and, List.all_append, List.all_map,
    Function.comp_def, DataPlane.Check.Report.compliant]
  rw [sameCheck]
  simp only [Bool.and_eq_true]

/-- This check binds the AP input to the model before it checks network paths. -/
def checkDeployment (hostapdText modelText : String) : Except String Report := do
  let ap ← Hostapd.parse hostapdText
  let (_, model) ← parseDeployment ap modelText
  let network ← DataPlane.Check.check model
  return deploymentReport ap network

end Netlib.Wifi
