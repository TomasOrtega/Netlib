# Netlib

Netlib is a Lean 4 library for network requirements, architecture proofs, and
finite network models. It connects reviewed requirements to formal propositions.
The library also provides packet policies, routing models, request enforcement,
and network change proofs. Its CLI analyzes requirements and evaluates
named-service configurations.

The standards catalogue records document versions, clauses, applicability, and assumptions.
The Wi-Fi profile imports real hostapd settings and checks a complete network model.
The 5G profile checks selected service admission rules over session traces.
Read the [Wi-Fi guide](docs/WIFI.md), [data-plane guide](docs/DATAPLANE.md),
and [5G guide](docs/FIVEG.md).

DARPA-SN-27-13 (FastVacc) provides the research direction for this library.
The [specification](docs/SPECIFICATION.md) maps that notice to the implementation.
The examples show architecture patterns. They do not certify an external standard.

## Run locally

Install [elan](https://github.com/leanprover/elan) and
[uv](https://docs.astral.sh/uv/getting-started/installation/).
Then run these commands from the repository directory:

```sh
uv sync --locked
uv run prek -a --quiet
uv run prek -a --quiet --stage manual
lake build
lake test
uv run python scripts/check_cli.py
lake exe netlib demo
```

The project uses Lean **4.35.0** and the Lean/Std libraries in that toolchain.
It needs no Mathlib download or external solver. `lake build` verifies library
proofs and theorem tests. `lake test` runs tests of input and compliance results.
The Python tests compare 1,800 CLI results with an independent graph algorithm.
They also run the documented scenarios.

All Lean compilation runs locally. CI validates saved HTML.
A manual Pages workflow deploys it.
See [the documentation process](#publish-documentation) and
[tooling](docs/TOOLING.md) for the complete process.

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
| `2` | The input is invalid. |

The `demo` command succeeds when all three scenarios give their expected results.

## Publish documentation

Commit the reviewed Lean source before the documentation build.
The builder requires that commit for stable source links.
Include manual, tooling, and prose changes in the source commit.
Then generate and validate the saved site locally:

```sh
uv run python scripts/check_text.py
uv run python scripts/build_docs.py
uv run python scripts/check_site.py --extract build/site
uv run python -m http.server --directory build/site 8000
```

Use an empty `build/site` directory for extraction.
Open `http://localhost:8000/` to review the landing page, manual, and API.
The builder saves `docs/site.tar.gz` and `docs/site-manifest.json`.
Commit those generated files in a separate documentation commit.
Push both commits.

Open the Pages workflow in GitHub Actions.
Select `Run workflow` for the branch with both commits.
The workflow validates and deploys the saved files without Lean compilation.
After an input change, repeat the local build and documentation commit.

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

## Analyze requirements

Offline analysis needs no configuration. It uses propositional logic and three
network laws:

- Universal reachability implies some reachability when both selections contain
  devices.
- Universal and existential reachability agree for a pair of node selectors.
- Isolation implies mediation by any gateway set.

The [observation proofs](Netlib/Policy/Observation.lean) connect these laws to
network semantics.

Analysis reports consistency, redundant requirements, missing goals, and abstract
countermodels. It also reports an inconsistent core when requirements contradict.
A proposed completion contains only supplied goals that remain consistent with
the requirements. Reports keep source IDs and text.

A propositional model can describe a combination that no network can realize.
Analysis uses a proved branch solver with a work budget.
It has no fixed atom-count limit.
The default budget permits 100,000 search nodes per solver query.
A budget error produces no consistency or entailment result.
Read the [solver guide](docs/SOLVER.md).

## Check standards and packet models

Run the complete Wi-Fi deployment example:

    lake exe netlib wifi examples/wifi/secure.conf examples/wifi/deployment.json --json

The report checks 12 AP obligations and five fixed network requirements.
Each result identifies its source and assumptions.
The companion model connects physical links, longest-prefix routes, ordered ACLs,
identity policies, and gateway enforcement.
Its AP binding must match the imported interface and bridge.

Run a packet model or a 5G session trace:

    lake exe netlib dataplane examples/dataplane/secure.json --json
    lake exe netlib fiveg examples/5g/secure.json --json
    uv run python scripts/check_profiles.py

The 5G trace records both accepted and denied requests.
A correct denial satisfies admission safety.
An unauthorized observed admission violates the selected profile.
Valid token reuse remains permitted.

Use the coverage reports for assurance outside these selected checks:

    lake exe netlib wifi-coverage --json
    lake exe netlib fiveg-coverage --json

Unsupported requirements and missing evidence cannot count as satisfied.
A passing selected profile does not establish complete CSfC or 5G compliance.
Identity and cryptographic observations remain explicit assumptions.

## Read the proofs

The library proves results about paths, cuts, segmentation, link removal, and
architecture refinement. Examples cover gateway clusters, failover, and two
mandatory gateway layers. A bypass example shows why ordinary reachability
refinement cannot prove mediation.

See the [proof inventory](docs/PROOFS.md) and [glossary](GLOSSARY.md). The library
contains no unfinished proofs, project-added network axioms, or `native_decide`
proofs. Lean verifies the formal claims and the successful checker's final status.
Tests and review address parser behavior, source interpretation, configuration
accuracy, and reports.

## Packet policies and network changes

The Lean library represents IPv4 addresses, protocol numbers, and port numbers.
Packet matches use address prefixes, protocols, and port ranges. Ordered access
control lists use the first matching rule and an explicit default action.
The library proves results about rule order, shadowed rules, and policy refinement.

Routing uses the longest matching destination prefix. The first matching route
wins when prefix lengths are equal. Routing and access control lists define
packet-specific forwarding networks. These library models are stateless.
They do not rewrite packet headers. The original check command still uses named services.
The dataplane command imports packet headers and request policies.

Network change theorems preserve results when two networks agree throughout a
closed region that contains the queried sources. These theorems cover
reachability, isolation, and mediation. They state conditions for reuse of query
results. The CLI does not maintain an incremental query cache.

## Request enforcement

A request names a principal, a resource, and an operation.
A request policy supplies authentication and authorization results.
Both results must pass for admission. An admitted request keeps the base
network's paths.

Denial removes links that touch the enforcement gateway set.
For outside endpoints, `denied_isolated_iff_mediated` proves that denial gives
isolation exactly when those gateways mediate every base path.
A bypass can preserve access for an unauthorized request.
The identity and permission results are supplied assumptions.
These proofs do not verify cryptography or live device behavior.

The packet, routing, and request suites contain 94 theorem examples.
See the [proof inventory](docs/PROOFS.md) for their scope and counts.

## Library layout

| Directory | Content |
| --- | --- |
| `Netlib/Core/` | Formula semantics and finite propositional reasoning. |
| `Netlib/Network/` | Paths, cuts, architecture refinement, and change proofs. |
| `Netlib/Packet/` | Header fields and access control lists. |
| `Netlib/Routing/` | Destination routes and forwarding models. |
| `Netlib/Security/` | Request identity, permission, and gateway enforcement. |
| `Netlib/Policy/` | Requirement input, observations, and offline analysis. |
| `Netlib/Model/` | Named-service configuration input. |
| `Netlib/Check/` | Compliance search, proofs, and reports. |
| `Netlib/Examples/` | Reference architecture proofs. |
| `Netlib/Standards/` | Sourced requirements and Wi-Fi and 5G profiles. |
| `Netlib/Import/` | Strict import of hostapd settings. |
| `Netlib/Protocol/` | Session states and admission invariants. |

The models exclude stateful firewalls, cryptographic correctness, dynamic routing
protocols, and live device configuration. The importer supports a strict hostapd 2.12 subset.
It does not import general vendor configurations. Netlib does not translate arbitrary prose or PDFs.
The repository does not claim the speedup target in the DARPA notice.
New models, adapters, proofs, and benchmarks can extend the library.
