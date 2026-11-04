import Lean

namespace Netlib.Hostapd

/-- A setting keeps its source line. -/
structure Setting where
  name : String
  value : String
  line : Nat
  deriving Repr, BEq

/-- This model covers one access point and one BSS. -/
structure Config where
  settings : List Setting
  deriving Repr

namespace Config

def setting? (config : Config) (name : String) : Option Setting :=
  config.settings.find? (·.name == name)

def get? (config : Config) (name : String) : Option String :=
  (config.setting? name).map (·.value)

def natural? (config : Config) (name : String) : Option Nat :=
  (config.get? name).bind String.toNat?

end Config

private def numericFields : List (String × Nat × Nat) :=
  [("wpa", 0, 3), ("ieee8021x", 0, 1), ("ieee80211w", 0, 2),
   ("eap_server", 0, 1), ("ap_isolate", 0, 1), ("auth_algs", 0, 3),
   ("wpa_ptk_rekey", 0, 2147483647), ("auth_server_port", 1, 65535),
   ("channel", 0, 233), ("logger_stdout", 0, 2147483647),
   ("logger_stdout_level", 0, 4)]

private def stringFields : List String :=
  ["interface", "ssid", "driver", "hw_mode", "country_code", "bridge", "ctrl_interface",
   "wpa_key_mgmt", "rsn_pairwise", "group_mgmt_cipher", "auth_server_addr",
   "auth_server_shared_secret"]

/-- The importer rejects syntax outside the supported single-BSS fragment. -/
def supportedFields : List String := stringFields ++ numericFields.map (·.1)

private def ipv4 (value : String) : Bool :=
  let parts := value.splitOn "."
  parts.length == 4 && parts.all (fun part =>
    !part.isEmpty && part.toList.all Char.isDigit &&
      match part.toNat? with | some n => n ≤ 255 | none => false)

private def validate (name value : String) : Except String Unit := do
  if value.isEmpty then throw s!"empty hostapd field: {name}"
  if name == "logger_stdout" && value == "-1" then return
  match numericFields.find? (·.1 == name) with
  | some (_, lower, upper) =>
    let some n := value.toNat? | throw s!"expected a decimal number for {name}"
    if !(value.toList.all Char.isDigit) || n < lower || upper < n then
      throw s!"number outside the supported range for {name}"
  | none => pure ()
  if name == "auth_server_addr" && !ipv4 value then
    throw "use an IPv4 RADIUS server address in this profile"
  if name == "ssid" && value.toUTF8.size > 32 then throw "SSID exceeds 32 bytes"
  if name == "interface" && value.toList.any Char.isWhitespace then
    throw "interface name contains whitespace"
  if name == "wpa_key_mgmt" then
    let modes := value.splitOn " " |>.filter (!·.isEmpty)
    let supported := ["WPA-EAP", "WPA-EAP-SHA256", "WPA-EAP-SUITE-B", "WPA-EAP-SUITE-B-192",
      "WPA-PSK", "WPA-PSK-SHA256", "SAE", "OWE"]
    if !modes.all supported.contains then throw "unsupported hostapd key management mode"
  if name == "rsn_pairwise" then
    let modes := value.splitOn " " |>.filter (!·.isEmpty)
    if !modes.all (["TKIP", "CCMP", "CCMP-256", "GCMP", "GCMP-256"].contains) then
      throw "unsupported hostapd pairwise cipher"
  if name == "group_mgmt_cipher" &&
      !(["AES-128-CMAC", "BIP-GMAC-128", "BIP-GMAC-256", "BIP-CMAC-256"].contains value) then
    throw "unsupported hostapd management cipher"

/-- Secret values remain in memory and never enter a profile report. -/
def parse (text : String) : Except String Config := do
  let mut settings := []
  let mut number := 0
  for raw in text.splitOn "\n" do
    number := number + 1
    let line := if raw.endsWith "\r" then (raw.dropEnd 1).toString else raw
    if line.trimAscii.toString.isEmpty || line.startsWith "#" then continue
    if line.startsWith " " || line.startsWith "\t" then
      throw s!"line {number}: indented hostapd directives are unsupported"
    let parts := line.splitOn "="
    let name := parts.head!
    if parts.length < 2 then throw s!"line {number}: expected name=value"
    if !supportedFields.contains name then
      throw s!"line {number}: unsupported hostapd field: {name}"
    if settings.any (fun setting : Setting => setting.name == name) then
      throw s!"line {number}: duplicate hostapd field: {name}"
    let value := String.intercalate "=" parts.tail!
    (validate name value).mapError (s!"line {number}: " ++ ·)
    settings := settings ++ [⟨name, value, number⟩]
  let config := Config.mk settings
  if (config.get? "interface").isNone then throw "hostapd input needs interface"
  if (config.get? "ssid").isNone then throw "hostapd input needs ssid"
  return config

end Netlib.Hostapd
