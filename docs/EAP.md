# EAP-derived session admission

This layer connects raw EAPOL frames, guarded authentication results, session credentials, and campus application paths.
It separates packet correlation from cryptographic method evidence.
An EAP Success packet alone cannot authenticate the modeled session.
The [session firewall guide](SESSION_FIREWALL.md) connects current scope guards to generated native policies and measured gateway packets.

## Run the native examples

```sh
lake exe netlib eap examples/eap/success.json --json
lake exe netlib eap examples/eap/bad-server.json --json
```

Both traces are compliant.
The first records logical authorization after a successful EAP-TLS exchange, then its removal after Logoff.
Its final `authorized` value is false.
The second records rejection of a server-name mismatch and remains unauthorized.
Compliance means agreement with supplied observations; correct rejection can satisfy that condition.

The [capture guide](../examples/eap/README.md) retains the reproduction recipe and exact producer versions.
The experiment uses hostapd 2.12 and wpa_supplicant 2.12 over private wired Ethernet interfaces.
It retains 32 raw frames across two producer windows, public certificate material, configurations, status snapshots, and sanitized logs.
The original Ethernet frames remain unchanged.
Private keys and ephemeral key material are excluded from the retained artifacts.

The peer's outer Identity is `anonymous@campus.example.test`.
The configured certificate principal is `alice@campus.example.test`.
The model binds method evidence to the expected principal and never promotes the outer Identity into that role.

The native exchange exercises TLS 1.3 and fragmentation in both directions.
The independent verifier checks frame bytes against producer hexdumps, fragment acknowledgments, record framing, producer outcomes, and configured identity policy.
It does not independently verify TLS cryptography.
The [source note](research/EAP_AUTHENTICATION.md) records the primary-source interpretation.

## Framing and correlation

The EAP byte codec implements the RFC 3748 base packet header.
Request and Response packets contain a Type byte and opaque method data.
Success and Failure have a declared length of four bytes.
Bytes beyond the declared EAP length remain preserved padding.

The EAPOL codec supports versions 1 through 3 and EAP, Start, and Logoff bodies.
It accepts untagged Ethernet EAPOL with EtherType `0x888e`.
Inner EAP padding and padding outside the EAPOL body remain separate.
Key, MKA, VLAN, and other encapsulations are outside this selected codec profile.
The session checker also excludes reserved and expanded method types.

The binary codecs have round-trip proofs in both directions.
Encoding a supported value then decoding preserves that value and its padding.
Decoding accepted bytes then encoding reconstructs the exact received bytes.
Hex and MAC text parsing have runtime tests; those text parsers have no general correctness theorem.

The checker binds one peer MAC and one authenticator MAC.
Requests and terminal packets must have the authenticator role.
Responses, Start, and Logoff must have the peer role.
Those checks establish consistency with the declared link binding.
MAC fields alone supply no cryptographic origin guarantee.

## Guarded authentication

The selected session profile uses EAP-TLS Type 13.
Authorization needs all of these conditions:

1. The latest Request and Response have matching identifiers and the selected method type.
2. The terminal Success matches that Response identifier.
3. Separate method evidence accepts the expected principal and method in the current local round.

Method data remains opaque to the Lean state machine.
The method result must faithfully represent the configured cryptographic and certificate policies.
It can be observed before or after terminal Success.
Authorization becomes true only when both pieces are present and correlated.

Wrong identifiers or method types cannot complete the selected transaction.
Exact retransmissions preserve the current state.
Fragmented method exchanges can use several Request/Response pairs before the terminal packet.
The native verifier separately checks TLS fragment acknowledgment structure.
The Lean authentication guard relies on the trusted method result for method correctness.

The local failclosed policy resets authorization and method evidence on Start, Logoff, disconnect, and declared restart.
Matching Failure and current negative method evidence also reset it.
Changing an established method or starting a new Request after terminal completion starts a new local round.
These reset rules define this Netlib profile; they do not model every IEEE 802.1X reauthentication option.
Old method evidence retains its old round tag and cannot authorize the reset state.

Local rounds are not EAP wire nonces.
Identifiers have only eight bits.
The native builder declares one begin event and counts the single captured Start to assign method round 2.
Producer windows, log references, and configured certificate policy supply the separate attribution assumption.
This does not establish general wire replay protection or cryptographic freshness.

## Session and campus connection

Only the guarded EAP authorization state sets session authentication in the bridge.
Application events cannot inject an `authenticate` Boolean.
A changed local round or authorization result clears the previous credential and admission.
Harmless protocol duplicates preserve them.

An authenticated session still needs a current credential for an application request.
The credential must match the issuer, subject, audience, requested scope, integrity result, and clock.
At the native success checkpoint, the campus guard still isolates application access because no application credential is installed.
Local credential revocation remains separate from EAP Logoff.

The bridge proves a corresponding session trace for each protocol/application execution.
Every modeled or correctly observed application admission has both the full credential guard and current accepted method evidence.
The campus examples connect that result to management isolation, gateway traversal, and availability under each admitted single internal-node fault.
Both modeled gateways use the same current session state.
The campus path theorem uses a state snapshot.
Earlier admitted traffic needs the separate [buffered cutover model](BUFFERING.md).
The configured-principal deployment theorem uses the report's actual consumer value, including the native certificate principal.
It does not substitute the outer Identity or a fixed campus subject.

Native files contain authentication observations only.
Application token/request events in tests are explicitly synthetic model scenarios.
Physical AP enforcement, native campus topology, RADIUS transport, wireless key installation, queue behavior, and complete cryptographic refinement remain separate work.
The [existing Wi-Fi profile](WIFI.md) retains its original selected configuration obligations and coverage gaps.

## Schema 1

The root fields are `schema`, `context`, `link`, and `events`.
Context contains `consumer`, `producer`, and `issuer` names.
The expected EAP method principal is the consumer.
Link contains distinct unicast `peer` and `authenticator` MAC addresses.

Every event contains `type` and `authorized`.
The latter is an observed logical authorization Boolean, or null when unobserved.
It never sets the model state.

| Event type | Other fields |
| --- | --- |
| `frame` | `raw`, a strict hex string containing the complete Ethernet frame. |
| `method` | `round`, `subject`, `method`, `accepted`, and optional-valued `source`. |
| `install` | `credential`, with the shared session credential fields. |
| `advance` | `now`, a nondecreasing natural-number clock value. |
| `request` | `scope` and the observed Boolean `accepted`. |
| `begin`, `restart`, `disconnect`, `close`, `revoke` | No additional fields. |

The method event's `accepted` value is supplied verification evidence.
The request event's `accepted` value observes an application outcome.
The event type distinguishes those roles.
A credential has `issuer`, `subject`, `audience`, `scopes`, `expiresAt`, and `integrity` fields.
Each scope contains nonempty `resource` and `operation` names.

The input requires at least one raw frame and one authorization or admission observation.
Unknown fields, malformed framing, role mismatches, unsupported encapsulations, and backward clocks cause input errors.
Exit code 0 means observation agreement, 1 means a mismatch, and 2 means an input or processing error.
Observed mismatches never replace the modeled state.

## Sources and proof scope

Reports link the selected RFC 3748 and RFC 9190 clauses.
They also link the pinned hostapd EAPOL definitions.
The framing, correlation, current-evidence, session, and campus theorems concern their stated Lean models.
Certificate validation, TLS signatures, key derivation, method freshness, and faithful producer observations remain explicit assumptions.
The wired experiment supplies no general physical controlled-port or application enforcement proof.
It does not certify complete EAP-TLS, IEEE 802.1X, WLAN, or CNSA compliance.
