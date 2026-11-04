# Enterprise Wi-Fi pilot

This pilot connects a hostapd file to explicit configuration obligations.
An optional deployment file adds packet, route, identity, and gateway checks.
Each finding keeps its source clause, version, assumptions, and evidence.

The passing result concerns the selected model obligations.
It does not establish product approval or complete Campus WLAN compliance.

## Sources

The configuration adapter follows the official
[hostapd 2.12 release](https://w1.fi/releases/hostapd-2.12.tar.gz).
Its reference file is `hostapd-2.12/hostapd/hostapd.conf`.
The release archive has this SHA-256 hash:

```text
f43502561c28ba47ab77e18e1a973d07361c68cc8b14178e619bd5796b70eabd
```

The reference configuration has this SHA-256 hash:

```text
3f756fec0b3622f2c43c90b3eca8371b9d54698ba9894098c359109ee657c352
```

The standards source is the
[NSA Campus WLAN Capability Package 3.2.0](https://www.nsa.gov/Portals/75/(U)%20Campus%20WLAN%20CP%20v3.2.0.pdf).
Its issue date is 27 March 2026.
The [NSA publication page](https://www.nsa.gov/Resources/Commercial-Solutions-for-Classified-Program/Capability-Packages/)
identifies that version.

A model check ID identifies a Netlib obligation.
A source clause ID identifies an external requirement.
An AP setting can establish only a declared part of a larger source requirement.
Client behavior, server behavior, negotiated algorithms, and operational evidence remain separate.

## Configuration obligations

| Model check | Source | Explicit setting |
| --- | --- | --- |
| `AP-RSN` | hostapd `wpa` | `wpa=2`. |
| `AP-192` | `WLAN-WL-2` | Only `WPA-EAP-SUITE-B-192` key management. |
| `AP-PMF` | `WLAN-WL-5` | `ieee80211w=2`. |
| `AP-NO-TRANSITION` | `WLAN-WL-6` | No additional key management mode. |
| `AP-PAIRWISE` | hostapd `rsn_pairwise` | Only `GCMP-256`. |
| `AP-MANAGEMENT-CIPHER` | hostapd `group_mgmt_cipher` | `BIP-GMAC-256`. |
| `AP-REKEY` | `WLAN-WS-2` | Pairwise key renewal from 1 through 3600 seconds. |
| `AP-8021X` | `WLAN-WS-1` | `ieee8021x=1`. |
| `AP-EAP-RELAY` | `WLAN-WS-1` | `eap_server=0`. |
| `AP-RADIUS` | `WLAN-WS-1` | Server address, port, and shared secret. |
| `AP-AUTH-ALGORITHM` | hostapd `auth_algs` | `auth_algs=1`. |
| `AP-CLIENT-ISOLATION` | hostapd `ap_isolate` | `ap_isolate=1`. |

The cipher checks use hostapd configuration semantics.
They do not claim equivalence to the complete CNSA algorithm tables.
The rekey check establishes the configured interval.
It does not prove a successful runtime key exchange.

## Import rules

The adapter accepts one AP and one BSS.
Supply explicit `interface` and `ssid` fields.
The adapter preserves source line numbers.
It rejects unknown fields, repeated fields, includes, and multiple BSS declarations.
It also rejects invalid numbers, indented directives, and unsupported security values.
The parser preserves SSID and shared-secret bytes, including trailing spaces.

Numeric flags use decimal values.
The parser accepts leading zeroes without changing the numeric meaning.
RADIUS server addresses use IPv4.
The supported subset does not import IPv6 RADIUS endpoints.
Missing security settings produce missing-evidence findings.
The checker does not infer a passing setting from a default.

The input secret stays in memory.
Reports show its presence without its value.
The fixture secret is an example string.
It supplies no evidence about secret entropy or production credentials.

## Deployment policy

Run the complete example:

```sh
lake exe netlib wifi examples/wifi/secure.conf examples/wifi/deployment.json --json
```

The deployment JSON contains `schema`, `binding`, and `model` fields.
Schema 1 binds the hostapd interface to one modeled AP node.
The optional bridge value must also match the file.
Exactly one model device must have the `access-point` role.
The AP must belong to the model's enforcement group.

The model uses the data-plane input schema.
It supplies directed physical links, longest-prefix routes, ordered packet rules, and request policies.
The reviewer supplies the device mapping and identity facts.
The importer does not discover a live topology or prove EAP authentication.
The separate [EAP session layer](EAP.md) connects raw message framing and trusted method results to guarded session admission.
Its wired native experiment leaves the Wi-Fi profile's original coverage gaps unchanged.

The profile requires these fixed queries in their specified order:

| Query | Local policy |
| --- | --- |
| `WIFI-SERVICE` | Permit the selected guest HTTPS flow to the service. |
| `WIFI-MANAGEMENT` | Block the selected guest flow to the management network. |
| `WIFI-GATEWAY` | Require the boundary gateway on each selected service path. |
| `WIFI-AP` | Require the imported AP on each selected service path. |
| `WIFI-IDENTITY` | Block the selected unauthenticated request. |

These local policies have their own source IDs.
They are not replacements for complete NSA requirements.
Each query covers all selected endpoint pairs for one named header and request.
It does not quantify over unspecified packet headers or session events.
The checker rejects a deployment that omits or changes a fixed query.

A direct service link can bypass the AP and the boundary gateway.
The bypass fixture demonstrates that failure with a path witness.
The management leak fixture changes a packet rule.
The service drop fixture changes a route.
The identity fixture changes the supplied principal policy.

## Proof connection

`Condition.evaluate_true_iff` connects an accepted field check to its proposition.
`status_satisfied_iff` covers every condition in a configuration obligation.
`check_sound` and `check_complete` connect the AP report to the complete selected catalogue.

`DataPlane.Check.Report.compliant_iff` covers every data-plane query.
`network_finding_correct` preserves that meaning in the standards report.
`deployment_report_iff` proves that the combined report passes exactly when both reports pass.
Parsing and the physical-device mapping remain reviewed inputs.

## Evidence outside the subset

`Wifi.coverage` is a separate report that cannot pass from an AP file.
It preserves these gaps:

- `WLAN-AA-1` needs client and server mutual-authentication evidence.
- `WLAN-AA-2` and Table 17 need complete algorithm-suite evidence.
- `WLAN-WL-4` needs controller-channel and architecture evidence.
- `WLAN-WS-5` through `WLAN-WS-7` need enclave applicability and interface evidence.

The report marks missing evidence or unsupported checks explicitly.
It does not convert an unchecked clause to a satisfied clause.

## Fixtures

`examples/wifi/secure.conf` passes every selected AP configuration obligation.
Each other AP fixture changes one setting or removes necessary evidence.
The `deployment.json` companion passes all five network queries.
Its negative companions demonstrate management leaks, service loss, bypasses, and an admitted identity.
Binding mismatches and missing obligations produce input errors.

Run the Lean Wi-Fi tests with the project test command.
The tests check every selected AP obligation and each deployment failure.
They also check source provenance, secret redaction, and unsupported input.
