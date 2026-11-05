# CLI and input guide

Run commands from the repository root after the [local setup](TOOLING.md#local-build-and-ci).
The [README](../README.md) gives the first demo command.
The [stateful failover guide](STATEFUL_FAILOVER.md) connects native replication, commitment, route handoff, and current packet policy.

## TCP framing and sequence arithmetic

```sh
lake exe netlib tcp-segment examples/tcp/segment.json --json
lake exe netlib tcp-wire examples/tcp/frame.json --json
lake exe netlib tcp-sequence examples/tcp/sequence.json --json
lake exe netlib tcp-receive examples/tcp-receive/trace.json --json
```

The [TCP guide](TCP.md) describes input fields, mandatory checksum validation, preserved options, and bounded serial-order laws.
Byte validity does not establish a connection or acceptable acknowledgment.
The report gives the MSS placement result separately from structural acceptance.
The [receive-state guide](TCP_RECEIVE.md) describes seeded replay, bounded ACK processing, and the stop at unsupported continuations.

## Interface-bound campus admission

```sh
lake exe netlib attachment-campus examples/attachments/bundle.json --json
```

The [ingress attachment guide](INGRESS_ATTACHMENTS.md) describes current EAP-to-interface bindings and the raw prerouting guard.
The checker evaluates installed numeric rules before ordinary conntrack and NAT.
Its guarded suffix follows an explicit empty-table reset after the unsafe impersonation example.
The default equivalence budget is one million cells.
Use `--budget N` to change that limit.
Wrong-port rejection, historical flow ownership, and current session permission have separate checks.

## Joint campus deployment

```sh
lake exe netlib campus-deployment examples/campus/bundle.json --json
lake exe netlib campus-deployment examples/campus/bundle.json --budget 100000 --json
```

Use `campus-deployment BUNDLE [--budget N] [--json]` with the combined input in the [campus deployment guide](CAMPUS_DEPLOYMENT.md).
The timeline interleaves indexed authentication and network observations with planned primary withdrawal.
Current installation certificates compare actual configured policy with the consumed authentication prefix.
A declared application class must cover every processed packet, including denied packets.
Selected next-hop labels must match the request or reply endpoint role.

The primary's retained state becomes an archive after withdrawal; later live primary operations are rejected.
The wired interpretation connects request and reply continuity without inferring native access points or Wi-Fi.
Matched ticket outputs retain exact NAT headers, payload, and TTL effects from their actual earlier assignments.
The current prefix supplies the session and method-readiness conclusions.
Cryptography, principal ownership, lifetime stability, physical correspondence, and automatic failure recovery remain explicit limits.

## Safe gateway handoff

```sh
lake exe netlib wire-safe-handoff examples/safe-handoff/replay.json --json
```

The [safe handoff guide](SAFE_HANDOFF.md) separates route assignment from later processing at the assigned gateway.
Lean calls these operations `assign` and `serve`; JSON retains the event type `admit` for assignment.
Every served ticket retains its actual earlier admission bytes and route assignment.
Processing evaluates the assigned gateway's current installed configuration.

The proofs cover arbitrary admissible interleavings and construct successful next steps from conditions on the preceding state.
A finite drain uses exactly the initial outstanding count of selected processing operations.
It establishes no time bound, fair scheduling, or physical queue correspondence.
The native example records 20 operations, seven datagrams, and six protected tickets without a native EAP claim.
Current-session enforcement separately requires installation of the matching certified policy at processing.

## Named-service commands

```sh
lake exe netlib check examples/secure.json examples/requirements.netlib
lake exe netlib check examples/failover.json examples/requirements.netlib
lake exe netlib check examples/bypass.json examples/requirements.netlib --json
lake exe netlib formalize examples/requirements.netlib
lake exe netlib analyze examples/requirements.netlib examples/goals.netlib
lake exe netlib analyze examples/incomplete.netlib examples/goals.netlib
lake exe netlib analyze examples/contradictory.netlib
lake exe netlib analyze examples/redundant.netlib
```

The secure and failover configurations pass. The bypass configuration fails both
gateway requirements. Its report shows the direct path. Offline analysis finds a
missing gateway requirement, a contradiction, and a duplicate requirement.

| Exit code | Meaning |
| --- | --- |
| `0` | Success. |
| `1` | A requirement fails, requirements contradict, or a goal does not follow. |
| `2` | An input, resource, or internal error prevents a result. |

The `demo` command succeeds when all three scenarios give their expected results.

## Write requirements

Each input line contains one requirement in a controlled language. Give each
requirement a unique ID and a final period. Blank lines and full-line `#` comments
are permitted. The parser rejects other sentence forms.

```text
AVAILABLE: node:red must reach node:black for https.
ISOLATED: zone:untrusted must be isolated from zone:management for ssh.
GATEWAY: node:red must traverse group:inner before node:black for https.
CONDITIONAL: if node:red must reach node:black for https then node:red must traverse group:inner before node:black for https.
```

A selector has one of these forms: `node:NAME`, `zone:NAME`, `role:NAME`, or
`group:NAME`. A requirement applies to every ordered pair of selected source and
target devices. Every selector must select at least one device. This rule also
applies to a conditional requirement when its premise is false.

A gateway group can contain several devices. A path satisfies the gateway
requirement when it visits at least one group member.

The `formalize` command prints each formula, its source text, and its line number.
The Lean language also supports all Boolean combinations:

```lean
import Netlib
open Netlib

example (a b : Formula String) :
    Reasoning.entails [a, .impl a b] b = true := by
  apply (Reasoning.entails_iff _ _).mpr
  intro valuation satisfied
  have ha := satisfied a (by simp)
  have hab := satisfied (.impl a b) (by simp)
  exact hab ha
```

## Describe a configuration

A configuration is a JSON object with `devices`, `links`, and `groups` arrays.
All fields in this example are necessary:

```json
{
  "devices": [
    {"id": "client", "zone": "red", "role": "endpoint"},
    {"id": "gateway", "zone": "gray", "role": "enforcer"},
    {"id": "server", "zone": "black", "role": "endpoint"}
  ],
  "links": [
    {"from": "client", "to": "gateway", "service": "https", "enabled": true},
    {"from": "gateway", "to": "server", "service": "https", "enabled": true}
  ],
  "groups": [{"name": "boundary", "members": ["gateway"]}]
}
```

The importer rejects unknown fields, duplicate IDs, invalid links, and invalid
group members. A link permits a directed step for its named traffic class.
The link service `*` permits every named traffic class. A requirement must name
one class and cannot use `*`. A disabled link permits no step.

Names can contain letters, digits, `_`, `-`, and `.`. This rule applies to device
IDs, zones, roles, groups, and traffic classes. Reviewers supply all labels and
group members. The importer does not infer roles from vendor configurations.

Reachability includes a path with zero steps from a device to itself. Isolation
means that no path exists. Mediation means that every path visits a gateway.
A gateway at either endpoint counts as a visit. Mediation can hold when no path
exists. Add a reachability requirement when availability is necessary.

The checker searches the complete finite graph, including cycles. It validates
each search result with a path or a cut certificate. An invalid certificate
causes an error.

The CLI uses `VerifiedCompliance.check` to verify observation values and original
requirement formulas. Its `check_compliant_iff` theorem connects the final status
to every original requirement. A successful report passes exactly when all those
requirements hold in the supplied model.

## Packet and standards commands

Use the dedicated guides for their input formats and model assumptions:

- [Wi-Fi deployment checks](WIFI.md).
- [EAP frames, guarded authentication, and session admission](EAP.md).
- [Session-derived firewall compilation and native snapshot checks](SESSION_FIREWALL.md).
- [Packet, route, and request checks](DATAPLANE.md).
- [IPv4 and UDP wire bytes and checksums](WIRE.md).
- [Payload, TTL, and NAT wire forwarding](WIRE_FORWARDING.md).
- [MTU decisions, fragmentation, and strict reassembly](MTU.md).
- [Generated ICMP errors and related quotation NAT](ICMP.md).
- [Received ICMP, NAT association, and host PMTU feedback](RECEIVED_ICMP.md).
- [Ingress IPv4 reassembly and policy at completion](REASSEMBLY.md).
- [Whole traffic classes](TRAFFIC.md).
- [Linux forwarding snapshots](LINUX.md).
- [Native conntrack records](CONNTRACK.md).
- [Safe gateway handoff with outstanding assignments](SAFE_HANDOFF.md).
- [Joint campus authentication, installation, and withdrawal](CAMPUS_DEPLOYMENT.md).
- [Tracked forwarding and stateful filter refinement](LIFECYCLE.md).
- [Output exclusion after a policy cutover](REVOCATION.md).
- [Buffered cutovers and delivery after draining](BUFFERING.md).
- [Packet requirement compilation](COMPILER.md).
- [Packet rewrites and timed flow authorization](STATEFUL.md).
- [5G admission traces](FIVEG.md).
- [Policy analysis and search budgets](SOLVER.md).

Run the coverage reports for requirements outside the selected profiles:

```sh
lake exe netlib wifi-coverage --json
lake exe netlib fiveg-coverage --json
```

Unsupported checks and missing evidence cannot count as satisfied.
A selected profile does not establish complete CSfC or 5G compliance.
Read the [model scope](SPECIFICATION.md#scope-limits) and [glossary](../GLOSSARY.md).
