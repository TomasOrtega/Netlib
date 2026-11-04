import Netlib.Standards.IEEE80211.Deployment

namespace NetlibTest.Wifi

open Netlib Standards

private def expect (value : Bool) (label : String) : IO Unit :=
  unless value do throw (IO.userError label)

private def unwrap (value : Except String α) : IO α :=
  match value with
  | .ok result => pure result
  | .error message => throw (IO.userError message)

private def rejects (text : String) (label : String) : IO Unit :=
  match Hostapd.parse text with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError s!"expected rejection: {label}")

private def hasStatus (report : Report) (id : String) (status : Status) : Bool :=
  report.findings.any (fun result => result.requirement.id == id && result.status == status)

example : Status.missingEvidence.passes = false := by decide
example : Status.unsupported.passes = false := by decide
example : Status.violated.passes = false := by decide
example : Status.notApplicable.passes = true := by decide
example : (Report.mk "empty" []).compliant = false := by decide

example (config : Hostapd.Config) (reportPasses : (Netlib.Wifi.check config).compliant = true)
    (check : Netlib.Wifi.Check) (member : check ∈ Netlib.Wifi.catalogue) :
    ∀ condition ∈ check.conditions, condition.Holds config :=
  Netlib.Wifi.check_sound config reportPasses check member

def run : IO Unit := do
  let secure ← IO.FS.readFile "examples/wifi/secure.conf"
  let parsed ← unwrap (Hostapd.parse secure)
  let good := Netlib.Wifi.check parsed
  expect good.compliant "secure AP subset did not pass"
  expect good.complete "secure AP subset lacks a result"
  expect (good.findings.length == Netlib.Wifi.catalogue.length) "profile lost a selected requirement"
  expect (good.findings.all (fun finding => !finding.requirement.source.version.isEmpty &&
    !finding.requirement.source.clause.isEmpty && !finding.requirement.source.url.isEmpty))
    "profile lost source provenance"
  expect ((parsed.setting? "ieee80211w").map (·.line) == some 10) "source line was lost"
  expect ((good.render.splitOn "example-only-secret").length == 1) "text report leaks a shared secret"
  expect (((good.renderJson.pretty).splitOn "example-only-secret").length == 1) "JSON report leaks a shared secret"
  for (file, id, status) in [
      ("legacy-wpa", "AP-RSN", Status.violated),
      ("non-192", "AP-192", .violated),
      ("pmf-optional", "AP-PMF", .violated),
      ("transition", "AP-NO-TRANSITION", .violated),
      ("pairwise-128", "AP-PAIRWISE", .violated),
      ("management-128", "AP-MANAGEMENT-CIPHER", .violated),
      ("rekey-too-long", "AP-REKEY", .violated),
      ("no-8021x", "AP-8021X", .violated),
      ("internal-eap", "AP-EAP-RELAY", .violated),
      ("missing-radius", "AP-RADIUS", .missingEvidence),
      ("shared-key-auth", "AP-AUTH-ALGORITHM", .violated),
      ("client-bridging", "AP-CLIENT-ISOLATION", .violated)] do
    let report ← unwrap (Netlib.Wifi.checkText (← IO.FS.readFile s!"examples/wifi/{file}.conf"))
    expect (!report.compliant) s!"broken AP fixture passed: {file}"
    expect (hasStatus report id status) s!"wrong source-linked result: {file}"
  rejects (secure.replace "\nwpa=2" "\n wpa=2") "indented hostapd directive"
  let exactSecret ← unwrap (Hostapd.parse (secure.replace "example-only-secret" "secret with trailing spaces  "))
  expect (exactSecret.get? "auth_server_shared_secret" == some "secret with trailing spaces  ")
    "hostapd parser changed secret bytes"
  rejects (secure ++ "bss=wlan1\n") "multiple BSS configuration"
  rejects (secure ++ "ieee80211w=0\n") "duplicate security field"
  rejects (secure ++ "include=extra.conf\n") "configuration include"
  rejects (secure.replace "ieee80211w=2" "ieee80211w=3") "invalid PMF value"
  rejects (secure.replace "auth_server_port=1812" "auth_server_port=65536") "invalid RADIUS port"
  rejects (secure.replace "auth_server_addr=192.0.2.10" "auth_server_addr=999.0.2.10") "invalid RADIUS address"
  rejects (secure.replace "wpa_ptk_rekey=3600" "wpa_ptk_rekey=-1") "negative rekey interval"
  rejects (secure.replace "wpa_ptk_rekey=3600" "wpa_ptk_rekey=4294967296") "overflowed host integer"
  rejects (secure.replace "wpa_key_mgmt=WPA-EAP-SUITE-B-192" "wpa_key_mgmt=UNKNOWN") "unknown key management mode"
  rejects (secure.replace "interface=wlan0\n" "") "missing AP identity"
  rejects "interface=wlan0\nssid=\n" "empty SSID"
  let leadingZeros ← unwrap (Netlib.Wifi.checkText (secure.replace "wpa=2" "wpa=02"))
  expect leadingZeros.compliant "decimal field normalization changed its meaning"
  let logger ← unwrap (Hostapd.parse (secure ++ "logger_stdout=-1\n"))
  expect ((logger.get? "logger_stdout") == some "-1") "all-module logger flag was rejected"
  let secretSymbols ← unwrap (Netlib.Wifi.checkText (secure.replace "example-only-secret" "secret=with#symbols"))
  expect secretSymbols.compliant "secret syntax changed the parsed configuration"
  expect ((secretSymbols.render.splitOn "secret=with#symbols").length == 1) "symbol secret leaks"
  expect (!Netlib.Wifi.coverage.compliant && !Netlib.Wifi.coverage.complete)
    "AP configuration was treated as full Campus WLAN evidence"
  expect (hasStatus Netlib.Wifi.coverage "COVERAGE-CIPHER-SUITE" .unsupported)
    "unsupported cipher proof was hidden"
  expect (hasStatus Netlib.Wifi.coverage "COVERAGE-EAP-TLS" .missingEvidence)
    "missing mutual-authentication evidence was hidden"
  let deployment ← IO.FS.readFile "examples/wifi/deployment.json"
  let joint ← unwrap (Netlib.Wifi.checkDeployment secure deployment)
  expect joint.compliant "secure Wi-Fi deployment did not pass"
  expect (joint.findings.length == Netlib.Wifi.catalogue.length + 5)
    "deployment report omitted a fixed query"
  for (file, id) in [
      ("management-leak", "WIFI-MANAGEMENT"),
      ("service-drop", "WIFI-SERVICE"),
      ("network-bypass", "WIFI-GATEWAY"),
      ("identity-admitted", "WIFI-IDENTITY")] do
    let broken ← unwrap (Netlib.Wifi.checkDeployment secure
      (← IO.FS.readFile s!"examples/wifi/{file}.json"))
    expect (!broken.compliant && hasStatus broken id .violated)
      s!"deployment violation lost its evidence: {file}"
  let bypass ← unwrap (Netlib.Wifi.checkDeployment secure
    (← IO.FS.readFile "examples/wifi/network-bypass.json"))
  expect (hasStatus bypass "WIFI-AP" .violated && hasStatus bypass "WIFI-IDENTITY" .violated)
    "direct service path did not bypass AP enforcement"
  for file in ["binding-mismatch", "missing-obligation"] do
    match Netlib.Wifi.checkDeployment secure (← IO.FS.readFile s!"examples/wifi/{file}.json") with
    | .error _ => pure ()
    | .ok _ => throw (IO.userError s!"invalid deployment was accepted: {file}")
  let brokenAp ← unwrap (Netlib.Wifi.checkDeployment
    (secure.replace "ieee80211w=2" "ieee80211w=1") deployment)
  expect (hasStatus brokenAp "AP-PMF" .violated && !brokenAp.compliant)
    "joint report hid an AP configuration violation"
  IO.println "Wi-Fi profile tests passed."

end NetlibTest.Wifi
