import Netlib.Standards.Basic
import Netlib.Import.Hostapd

namespace Netlib.Wifi

open Standards

/-- Each condition states one exact configuration obligation. -/
inductive Condition where
  | equals (field expected : String)
  | naturalRange (field : String) (lower upper : Nat)
  | present (field : String)
  deriving Repr, BEq

namespace Condition

def field : Condition → String
  | .equals f _ | .naturalRange f _ _ | .present f => f

def evaluate (config : Hostapd.Config) : Condition → Option Bool
  | .equals field expected => (config.get? field).map (fun value => decide (value = expected))
  | .naturalRange field lower upper => (config.natural? field).map (fun n => decide (lower ≤ n ∧ n ≤ upper))
  | .present field => (config.get? field).map (fun value => !value.isEmpty)

/-- This meaning does not assign a value to a missing field. -/
def Holds (config : Hostapd.Config) : Condition → Prop
  | .equals field expected => config.get? field = some expected
  | .naturalRange field lower upper =>
    ∃ n, config.natural? field = some n ∧ lower ≤ n ∧ n ≤ upper
  | .present field => ∃ value, config.get? field = some value ∧ value.isEmpty = false

theorem evaluate_true_iff (config : Hostapd.Config) (condition : Condition) :
    condition.evaluate config = some true ↔ condition.Holds config := by
  cases condition with
  | equals field expected =>
    cases value : config.get? field <;> simp [evaluate, Holds, value]
  | naturalRange field lower upper =>
    cases value : config.natural? field <;> simp [evaluate, Holds, value]
  | present field =>
    cases value : config.get? field <;> simp [evaluate, Holds, value]

def evidence (config : Hostapd.Config) (condition : Condition) : String :=
  match config.setting? condition.field with
  | none => s!"{condition.field}: no explicit setting"
  | some setting =>
    if setting.name == "auth_server_shared_secret" then
      s!"line {setting.line}: {setting.name} is present; its value is hidden"
    else s!"line {setting.line}: {setting.name}={setting.value}"

end Condition

structure Check where
  requirement : Requirement
  conditions : List Condition
  deriving Repr

private def cpUrl : String :=
  "https://www.nsa.gov/Portals/75/(U)%20Campus%20WLAN%20CP%20v3.2.0.pdf"

private def cp (clause : String) : Source :=
  ⟨"NSA Campus WLAN Capability Package", "3.2.0 (27 March 2026)", clause, cpUrl⟩

private def hostapd (field : String) : Source :=
  ⟨"hostapd.conf", "hostapd 2.12", field, "https://w1.fi/releases/hostapd-2.12.tar.gz"⟩

private def assumptions : List String :=
  ["This file describes one AP and one BSS.",
   "hostapd 2.12 applies these settings without external overrides.",
   "The driver supports the selected settings.",
   "The result covers explicit AP settings, not client or server behavior."]

private def obligation (id : String) (source : Source) (statement : String)
    (conditions : List Condition) : Check :=
  ⟨⟨id, source, statement, "Selected AP configuration sub-obligation only", assumptions⟩, conditions⟩

/-- Internal IDs identify model checks. Source clauses identify external requirements. -/
def catalogue : List Check := [
  obligation "AP-RSN" (hostapd "wpa") "Enable RSN without legacy WPA."
    [.naturalRange "wpa" 2 2],
  obligation "AP-192" (cp "WLAN-WL-2") "Select only the 192-bit enterprise key management mode."
    [.equals "wpa_key_mgmt" "WPA-EAP-SUITE-B-192"],
  obligation "AP-PMF" (cp "WLAN-WL-5") "Require protected management frames at the AP."
    [.naturalRange "ieee80211w" 2 2],
  obligation "AP-NO-TRANSITION" (cp "WLAN-WL-6") "Exclude other key management modes from this AP."
    [.equals "wpa_key_mgmt" "WPA-EAP-SUITE-B-192"],
  obligation "AP-PAIRWISE" (hostapd "rsn_pairwise") "Select only the GCMP-256 pairwise cipher."
    [.equals "rsn_pairwise" "GCMP-256"],
  obligation "AP-MANAGEMENT-CIPHER" (hostapd "group_mgmt_cipher") "Select the BIP-GMAC-256 management cipher."
    [.equals "group_mgmt_cipher" "BIP-GMAC-256"],
  obligation "AP-REKEY" (cp "WLAN-WS-2") "Set the pairwise key renewal interval from 1 to 3600 seconds."
    [.naturalRange "wpa_ptk_rekey" 1 3600],
  obligation "AP-8021X" (cp "WLAN-WS-1") "Enable IEEE 802.1X at the AP."
    [.naturalRange "ieee8021x" 1 1],
  obligation "AP-EAP-RELAY" (cp "WLAN-WS-1") "Disable the internal EAP server for this pass-through profile."
    [.naturalRange "eap_server" 0 0],
  obligation "AP-RADIUS" (cp "WLAN-WS-1") "Configure the external RADIUS server and its shared secret."
    [.present "auth_server_addr", .naturalRange "auth_server_port" 1 65535,
     .present "auth_server_shared_secret"],
  obligation "AP-AUTH-ALGORITHM" (hostapd "auth_algs") "Select Open System authentication for IEEE 802.1X."
    [.naturalRange "auth_algs" 1 1],
  obligation "AP-CLIENT-ISOLATION" (hostapd "ap_isolate") "Disable direct station bridging within this BSS."
    [.naturalRange "ap_isolate" 1 1]]

/-- A missing field cannot satisfy its condition. -/
def status (config : Hostapd.Config) (conditions : List Condition) : Status :=
  if conditions.all (fun c => decide (c.evaluate config = some true)) then .satisfied
  else if conditions.any (fun c => decide (c.evaluate config = some false)) then .violated
  else .missingEvidence

theorem status_satisfied_iff (config : Hostapd.Config) (conditions : List Condition) :
    status config conditions = .satisfied ↔ ∀ condition ∈ conditions, condition.Holds config := by
  have exactMeaning : conditions.all (fun c => decide (c.evaluate config = some true)) = true ↔
      ∀ c ∈ conditions, c.Holds config := by
    simp only [List.all_eq_true, decide_eq_true_eq, Condition.evaluate_true_iff]
  cases all : conditions.all (fun c => decide (c.evaluate config = some true)) with
  | true =>
    have holds := exactMeaning.mp all
    exact ⟨fun _ => holds, fun _ => by simp [status, all]⟩
  | false =>
    have notHolds : ¬(∀ condition ∈ conditions, condition.Holds config) := by
      intro holds
      have := exactMeaning.mpr holds
      simp_all
    cases any : conditions.any (fun c => decide (c.evaluate config = some false)) <;>
      simp [status, all, any, notHolds]

private def finding (config : Hostapd.Config) (check : Check) : Finding :=
  ⟨check.requirement, status config check.conditions, check.conditions.map (·.evidence config)⟩

/-- The profile reports only the selected configuration obligations. -/
def check (config : Hostapd.Config) : Report :=
  ⟨"Netlib enterprise AP configuration subset 1", catalogue.map (finding config)⟩

def checkText (text : String) : Except String Report := do
  return check (← Hostapd.parse text)

theorem satisfied_check_sound (config : Hostapd.Config) (entry : Check)
    (passed : (finding config entry).status = .satisfied) :
    ∀ condition ∈ entry.conditions, condition.Holds config :=
  (status_satisfied_iff _ _).mp passed

private theorem status_not_inapplicable (config : Hostapd.Config) (conditions : List Condition) :
    status config conditions ≠ .notApplicable := by
  unfold status
  split
  · simp
  · split <;> simp

/-- A passing profile establishes every selected configuration predicate. -/
theorem check_sound (config : Hostapd.Config) (passed : (check config).compliant = true) :
    ∀ entry ∈ catalogue, ∀ condition ∈ entry.conditions, condition.Holds config := by
  intro entry member
  have included : finding config entry ∈ (check config).findings :=
    List.mem_map.mpr ⟨entry, member, rfl⟩
  rcases Report.compliant_status (check config) passed (finding config entry) included with good | absent
  · exact satisfied_check_sound config entry good
  · exact False.elim (status_not_inapplicable config entry.conditions absent)

/-- The report covers all selected configuration predicates. -/
theorem check_complete (config : Hostapd.Config)
    (holds : ∀ entry ∈ catalogue, ∀ condition ∈ entry.conditions, condition.Holds config) :
    (check config).compliant = true := by
  simp only [Report.compliant, Bool.and_eq_true]
  constructor
  · rfl
  · apply List.all_eq_true.mpr
    intro result member
    obtain ⟨entry, entryMember, rfl⟩ := List.mem_map.mp member
    have good : status config entry.conditions = .satisfied :=
      (status_satisfied_iff _ _).mpr (holds entry entryMember)
    simp [finding, good, Status.passes]

/-- These source clauses need evidence outside the AP configuration model. -/
def coverage : Report := ⟨"Campus WLAN 3.2.0 evidence outside the AP subset", [
  ⟨⟨"COVERAGE-EAP-TLS", cp "WLAN-AA-1", "Verify mutual EAP-TLS authentication with device certificates.",
    "WLAN client and authentication server", []⟩, .missingEvidence,
    ["Supply client and server certificate policies and protocol evidence."]⟩,
  ⟨⟨"COVERAGE-CIPHER-SUITE", cp "WLAN-AA-2 and Table 17", "Verify all selected CNSA 1.0 algorithms.",
    "Client, server, and negotiated wireless link", []⟩, .unsupported,
    ["The AP cipher setting does not establish this algorithm-suite requirement."]⟩,
  ⟨⟨"COVERAGE-CONTROLLER", cp "WLAN-WL-4", "Protect the AP-to-controller connection when WPA3 terminates at the AP.",
    "Architectures with an external WLAN controller", []⟩, .missingEvidence,
    ["Supply the controller architecture and encrypted-channel evidence."]⟩,
  ⟨⟨"COVERAGE-ENCLAVES", cp "WLAN-WS-5 through WLAN-WS-7", "Verify enclave policy and interface separation.",
    "Architectures with multiple enclaves", []⟩, .missingEvidence,
    ["No enclave applicability or physical-interface evidence was supplied."]⟩]⟩

end Netlib.Wifi
