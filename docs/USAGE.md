# CLI and input guide

Run commands from the repository root after the [local setup](TOOLING.md#local-build-and-ci).
The [README](../README.md) gives the first demo command.

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
- [Whole traffic classes](TRAFFIC.md).
- [Linux forwarding snapshots](LINUX.md).
- [Native conntrack records](CONNTRACK.md).
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
