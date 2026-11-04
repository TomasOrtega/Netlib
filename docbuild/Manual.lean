import VersoManual
import Netlib

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Netlib Manual" =>

%%%
shortTitle := "Netlib"
%%%

Netlib is a Lean library for network requirements and proofs.
It also checks finite network configurations.
This manual explains the model, the proof methods, and the check process.
The [API pages](../api/) show the declarations and their source files.

# Library model
%%%
tag := "model"
file := "model"
%%%

A network contains nodes and directed links.
A link represents one permitted step for one traffic class.
A path contains zero or more permitted steps.
Thus, each node has a path to itself.
The model does not predict packet delivery time.

Reachability means that a permitted path exists.
Isolation means that no permitted path connects the selected sources and targets.
Gateway mediation means that every such path visits the selected gateway set.
A gateway at either endpoint counts as a visit.
Mediation can hold when no path exists.

Keep availability and gateway requirements separate.
An isolated destination does not prove useful service.
A gateway group can contain several devices.
A path needs to visit only one group member.
Separate gateway groups can state separate layer requirements.

The configuration assigns node identities, zones, roles, and group members.
The importer does not infer these labels from vendor files.
The reviewer must check that the labels match the intended network.
The result concerns the supplied model and requirements.

The core logic supports atoms, negation, conjunction, disjunction, and implication.
Each atom has an explicit meaning.
Offline analysis checks assignments without a concrete configuration.
Some assignments can describe combinations that no concrete network can realize.
A logical countermodel is not a proposed network deployment.

The source tree separates the library into these parts:

 * `Netlib.Core` defines formulas and finite logical analysis.
 * `Netlib.Theory` proves queue laws and limits of header-only NAT decisions.
 * `Netlib.Network` defines paths, cuts, gateways, and refinements.
 * `Netlib.Packet` defines packet fields, policies, transformations, and transfer relations.
 * `Netlib.Routing` selects destination routes.
 * `Netlib.Security` defines request policy and gateway enforcement.
 * `Netlib.Protocol` defines sessions, timed flow grants, and NAT state.
 * `Netlib.Standards` records sources and selected standards profiles.
 * `Netlib.Import` reads strict hostapd, Linux route, and nftables inputs.
 * `Netlib.Compile` translates packet intent to certified firewall policies.
 * `Netlib.Model` defines configuration data.
 * `Netlib.Policy` connects requirement text and network observations.
 * `Netlib.Check` checks configurations and constructs certified results.
 * `Netlib.Examples` gives proved architecture examples.

The packet library adds 32-bit addresses, protocol numbers, and port ranges.
An address prefix selects addresses with the same first bits.
A match can restrict any supported header field.
An absent field accepts every value for that field.
The original `check` command uses named traffic classes.
The `dataplane` command uses fixed packet headers and named requests.
The `transfer` command tracks a changing header through each forwarding step.
The `nat-trace` command checks observed translations and timed return-flow authorization.

# Proof patterns
%%%
tag := "proof-patterns"
file := "proof-patterns"
%%%

State each assumption in the theorem type.
Use generic node types when a proof does not need a finite configuration.
Keep the graph relation separate from the parser and report code.
This lets one theorem apply to several import formats.

## Paths

The empty path proves reachability from a node to itself.
Verso checks this example with the library:

```lean
example {Node : Type} (net : Netlib.Network Node)
    (node : Node) :
    Netlib.Network.Reachable net node node := .refl node
```

Combine two paths with the transitivity theorem.
The shared node must match.

```lean
example {Node : Type} (net : Netlib.Network Node)
    (a b c : Node)
    (left : Netlib.Network.Reachable net a b)
    (right : Netlib.Network.Reachable net b c) :
    Netlib.Network.Reachable net a c := left.trans right
```

## Cuts and gateways

A cut is a set of nodes closed under the relevant permitted steps.
For isolation, the cut must contain the source and exclude the destination.
The certificate validator checks these conditions.
It then connects the accepted cut to the isolation proposition.

For gateway mediation, remove all links incident to the gateway set.
Check that no bypass path remains.
Handle gateway endpoints before this graph check.
This method treats a whole cluster as one gateway set.

## Network changes

Link removal preserves isolation and gateway mediation.
It can remove the last available path.
Prove availability from a retained subnetwork after a failure.
Check added links again because they can create a bypass.

A refinement maps physical paths to abstract paths.
Ordinary refinement transfers isolation.
Gateway transfer needs the stronger stuttering refinement contract.
Its assumptions prevent an abstract path from hiding a physical bypass.

A saved result can survive a change outside a closed source region.
Prove that the old region is closed.
Prove that both networks have the same links from each region member.
The change theorems then transfer path, isolation, and gateway results for sources inside the region.

## Packet controls

An access control list checks rules in order.
The first matching rule supplies the action.
The standard policy denies a packet when no rule matches.
A later rule has no effect when an earlier match always covers it.

Each directed link can have its own access control list.
The filtered graph retains a link only when its policy permits the header.
Filtering can remove paths and preserves existing isolation and mediation.
A stronger policy permits no extra headers.
It therefore cannot introduce a new packet path.

## Logical checks

The Boolean formula evaluator has a separate proposition semantics.
The library proves that these meanings agree.
The exact reference solver enumerates finite assignments.
The executable solver branches on atoms and simplifies constants.
Every completed answer carries a model proof or an impossibility proof.
It has no fixed atom limit.

Each solver query has a default budget of 100,000 search nodes.
Both branches share the remaining nodes for that query.
An exhausted query returns an error.
It does not establish consistency, inconsistency, or entailment.
The analysis can make several queries.
This budget does not limit total analysis time or memory.

Check consistency before goal coverage.
An inconsistent policy entails every goal in classical logic.
Reduce requirements in sequence so that two duplicate requirements cannot both disappear.
Keep the background laws fixed during every removal.
The fast reduction carries a proof of equivalence for every valuation.
Use supplied goals for completion.
Do not infer an unstated mission goal.

## Routes and request controls

A route matches the destination address prefix.
The route lookup selects the longest matching prefix.
The first table entry wins when prefix lengths are equal.
A drop route supplies no next hop.
An access control list can further restrict the selected forwarding step.

A Zero Trust request names a principal, resource, and action.
The supplied policy checks identity and permission.
An admitted request retains the base network paths.
A denied request cannot cross a policy gateway.

For denied-request isolation, prove gateway mediation first.
Keep the source and target sets outside the gateway set.
Under these conditions, mediation is both necessary and sufficient for isolation.
A bypass path remains usable when the gateway rejects the request.
These theorems assume the identity checks.
They do not prove an identity protocol or cryptography.

# Input and check process
%%%
tag := "check-process"
file := "check-process"
%%%

## Requirement text

Write one identified requirement per line.
End each requirement with a period.
Use a unique identifier.
Use a named service instead of the wildcard `*`.

```
AVAILABLE: node:client must reach node:server for https.
GATEWAY: node:client must traverse group:boundary before node:server for https.
ISOLATED: zone:untrusted must be isolated from zone:management for ssh.
```

Selectors name a node, zone, role, or group.
Each selected source and target pair must satisfy the requirement.
Each referenced selection must contain a device.
This rule also applies inside an inactive implication branch.
The parser rejects unsupported sentences.

## Configuration data

Supply a JSON object with `devices`, `links`, and `groups` arrays.
Each device has an `id`, `zone`, and `role`.
Each link has `from`, `to`, `service`, and `enabled` fields.
Each group has a `name` and `members` list.
Unknown fields and missing fields are errors.

Device and group identities must be unique.
Each link endpoint and group member must name a declared device.
Disabled links do not permit a step.
A link service of `*` permits every named traffic class.
The checker does not truncate cycles to a fixed path length.

## Run a check

Run these commands from the repository root:

```
lake build
lake test
uv run --locked python scripts/check_cli.py
lake exe netlib check examples/secure.json examples/requirements.netlib
```

Use `--json` when another program needs the report.
Use `formalize` to review the normalized formulas.
Use `analyze` to check consistency and explicit goals without a configuration.

```
lake exe netlib check examples/bypass.json examples/requirements.netlib --json
lake exe netlib formalize examples/requirements.netlib
lake exe netlib analyze examples/requirements.netlib examples/goals.netlib
```

The CLI returns `0` for success.
It returns `1` for a failed requirement, inconsistency, or missing goal.
It returns `2` for invalid input.
Read the finding details before a configuration change.

## Result guarantees

The checker validates each accepted path or cut.
The certified wrapper evaluates the original formulas.
Its theorems connect each status to the requirement's formal meaning.
The result list covers the original requirements in their original order.
An internal certificate error is not a compliance result.

These proofs do not establish parser correctness or configuration fidelity.
They do not certify live devices, cryptography, or an external security standard.
Review the source text, formulas, labels, and imported links together.

# Standards and composed models
%%%
tag := "standards"
file := "standards"
%%%

## Sources and evidence

Each source record names a document, version, clause, and URL.
Each requirement records its applicability and assumptions.
Each finding keeps the requirement and its evidence.
Model check IDs and external clause IDs remain separate.

Only satisfied and not-applicable findings can pass.
Unsupported requirements and missing evidence remain visible.
An empty report cannot pass.
These checked examples establish two rules:

```lean
example :
    Netlib.Standards.Status.passes .unsupported =
      false := by
  decide

example :
    (Netlib.Standards.Report.mk "Example" []).compliant =
      false := by
  decide
```

The source mapping still needs review against the intended clause.
A formal predicate proves only its stated part of a source requirement.

## Wi-Fi deployment

The Wi-Fi adapter reads one AP and one BSS from hostapd 2.12.
It rejects unsupported directives, duplicate fields, and invalid values.
Reports preserve source lines and hide the RADIUS shared-secret value.
Missing security settings produce missing-evidence findings.

The AP subset checks 12 explicit configuration obligations.
These include selected Campus WLAN 3.2.0 sub-obligations.
A setting does not establish the full client, server, or negotiated algorithm behavior.

The deployment companion binds the AP interface and bridge to one modeled access point.
It adds five fixed network requirements.
The input cannot delete or reorder those requirements.
The requirements cover service availability, management isolation, gateway mediation, AP mediation, and an unauthenticated request.

Run the complete example:

```
lake exe netlib wifi examples/wifi/secure.conf examples/wifi/deployment.json --json
lake exe netlib wifi-coverage --json
```

The coverage report identifies obligations outside the AP subset.
It does not convert missing operational evidence into a passing result.

## Composed forwarding

The data-plane model uses fixed IPv4 packet headers and named requests.
Each step must follow an enabled physical link.
The longest matching route must select its target.
The link's ordered ACL must permit the packet.
Any incident enforcement gateway must admit the request.

The route lookup cannot create physical adjacency.
An empty ACL denies traffic.
The identity and permission facts remain supplied inputs.
Every selected endpoint pair has a checked path or cut.

Run the passing model and a gateway bypass:

```
lake exe netlib dataplane examples/dataplane/secure.json --json
lake exe netlib dataplane examples/dataplane/bypass.json --json
```

The final-status theorem covers every original query in its original order.
The bypass fixture shows why a failed identity check alone does not establish isolation.

## 5G service traces

The selected profile uses TS 33.501 version 19.5.0, clause 13.4.1.1.2.
It checks admitted requests in a direct NF-instance trace.
The session records identity results, a credential, a clock, and guarded admission.
Its transition proofs preserve the admission invariant.

The trace supplies identity and integrity observations.
The guards check token presence, issuer, subject, audience, scope, and expiration.
An unsafe observed admission violates the profile.
A correct denied request satisfies admission safety.
Valid token reuse remains permitted.

The selected service-request procedure has no token-revocation step.
Generic local revocation clears the current credential.
It does not maintain a persistent token blacklist.
The 5G profile rejects that event.

Run the trace and its separate evidence report:

```
lake exe netlib fiveg examples/5g/secure.json --json
lake exe netlib fiveg-coverage --json
uv run --locked python scripts/check_profiles.py
```

The report assumes that the trace records every actual admission.
It does not prove TLS authentication or token cryptography.
Optional claim forms and indirect communication remain outside the selected profile.

## Review the complete chain

1. Select a versioned source clause.
2. Review its formal predicate and assumptions.
3. Import the supported configuration or trace.
4. Bind the input to the declared model.
5. Check the model property.
6. Inspect source-linked evidence and any violating path or event.

A passing selected profile does not establish complete standards compliance.

# Composition foundations
%%%
tag := "composition"
file := "composition"
%%%

The library connects packet classes, protocol traces, domains, faults, and operational updates.
Each connection has explicit assumptions and a proof.

## Queue conservation and service

The discrete FIFO model appends arrivals before each service step.
The service capacity limits the number of packets served in that step.
Sequence conservation connects the delivered and pending packets to every supplied arrival.
The theorem preserves packet order without loss or duplication in the model.
Backlog bounds require explicit arrival and service assumptions.
A finite queue drains after enough service steps when no new packets arrive.
The current queue model has no storage limit or physical clock.

## Whole traffic classes

The `traffic` command checks every header selected by a packet match.
The partition collects ACL, route, and selection boundaries.
Every header has a represented cell.
ACL and routing decisions remain equal within that cell.
The data-plane checker transfers this equality through physical links and request enforcement.
An exhausted cell budget returns an error without a compliance result.

Universal ACL refinement has an executable decision and a semantic theorem:

```lean
open Netlib.Packet in
example (stronger weaker : ACL) :
    Partition.checkACLRefines stronger weaker = true ↔
      stronger.Refines weaker :=
  Partition.checkACLRefines_iff stronger weaker
```

## Traces and update plans

A labeled transition relation defines permitted state changes.
Independent events interleave.
Synchronized events change both modeled states.
Trace refinement maps a concrete event to a finite abstract trace.
Invariants transfer through these refinements and their composition.

An update plan includes the initial state, final state, and every intermediate snapshot.
An accepted check carries a proof that each snapshot satisfies the contract.
The migration tests distinguish safe gateway replacement from an outage or a temporary bypass.
Both unsafe examples have passing endpoints.

## Domains, failures, and the campus example

Domains expose abstract forwarding contracts and keep their node identities separate.
Local refinement proofs compose when border transitions satisfy the same contract.
A common closed region also supports isolation proofs across a graph union.
Isolation of each graph separately does not establish isolation of their union.

The fault model states which nodes and links can fail.
Two internally disjoint paths preserve service under one internal-node failure.
That theorem excludes client and server failures and independent link faults.

The campus example connects these results to session-controlled application access.
It proves management isolation, gateway mediation, and the declared fault availability.
Session traces connect recorded admission to the credential conditions and an available application path.
This example still assumes observed identity and integrity results.
Real device configuration and authentication protocol refinement remain open work.

## Formal standards composition

Formal clauses separate applicability, optional feature selection, and the obligation.
Profiles compose by conjunction and retain each original source record.
Compatibility checks return a model or a proof of contradiction under supplied facts.
Version refinement checks implication and returns a countermodel when implication fails.
Unsupported clauses and exhausted budgets return errors.
Compatibility and refinement reject unsupported clauses even when a guard could make them inactive.
An implication proof does not establish that the stronger profile is satisfiable.

## Native input and configuration compilation

The Linux adapter binds iproute2 route exports and nftables forward-chain exports to declared device identities.
It generates the physical links, packet rules, and route tables.
Unknown syntax and unsupported native behavior cause input errors.
Reports preserve source locations, original route records, and firewall rule provenance.
Every JSON text input rejects duplicate decoded object keys.

The route translation has an all-address theorem:

```lean
open Netlib.Import.LinuxRoute in
example (snapshot : Snapshot)
    (address : Netlib.Packet.Address) :
    Netlib.Routing.nextHop snapshot.compile address =
      snapshot.nextNode address :=
  snapshot.nextHop_correct address
```

The composed graph also preserves the source-chain decisions and declared request enforcement.
The scope assumes valid unfragmented IPv4 transit after main-table selection.
Interface bindings and external identity controls need separate review.
Other hooks and packet transformations must preserve the modeled decisions.

Packet intent supplies unordered permit and hard-deny requirements.
The exact partition checks every overlap.
A conflict returns original requirement IDs and a concrete packet.
Successful compilation carries a proof for every modeled header.
Native-format emission preserves that certificate in a structured nftables snapshot.

The serializer has roundtrip tests over exact packet partitions.
Native nftables 1.1.3 accepted and loaded generated JSON in an isolated Linux container.
The imported re-export preserves the generated policy under all-header equivalence checks.
These tests establish interoperability evidence, separate from the structured translation theorems.
The generated additions require a fresh table and exclusive modeled forwarding behavior.
The compiler does not apply a deployment operation.

# Packet transformations and flow state
%%%
tag := "stateful"
file := "stateful"
%%%

## Header-changing paths

A transfer state contains both a node and the current packet header.
Each link first checks its guard and then applies its rewrite.
A later firewall stage therefore reads the changed header.
Matching links represent alternatives.
Separate stage nodes represent ordered processing.

Rewrites can overwrite any of the five supported fields.
An absent replacement preserves the field.
Composition applies the first rewrite and then the second:

```lean
open Netlib.Packet in
example (first second : Rewrite) (header : Header) :
    (first.comp second).apply header =
      second.apply (first.apply header) :=
  Rewrite.comp_apply first second header
```

The checker builds a finite universe from the initial header and overwrite constants.
The universe is closed under all declared rewrites and header reversal.
Each returned path or cut has a checked certificate.
Reachability permits any resulting header at the target.
Isolation and mediation cover every resulting header and modeled path for the supplied initial header.

Run a translation and a firewall bypass:

```
lake exe netlib transfer examples/transfer/dnat.json --json
lake exe netlib transfer examples/transfer/gateway-bypass.json --json
```

The default budget is 4,096 node/header states.
The checker computes the exact state-list size before constructing it.
Budget exhaustion or certificate failure returns an error without a query result.
Every returned answer agrees with the full semantic query.
The library has no separate theorem that guarantees successful search completion for every valid input.

## Timed translation traces

The local source-NAPT model separates public endpoint mappings from return-flow grants.
Mapping selection depends on the inside endpoint and protocol.
Several remote peers can share that mapping.
Each reply still needs a live grant for its exact reversed five-tuple.
The current clock must precede the grant deadline.

The trace auditor derives outbound permission from a certified packet-intent policy.
The input cannot supply its own authorization result.
The auditor compares each recorded output or drop with the model output.
A passing report covers every supplied packet event.
Each restored reply has an earlier outbound event permitted by the declared intent.

```
lake exe netlib nat-trace examples/nat/secure.json --json
lake exe netlib nat-trace examples/nat/expired-admitted.json --json
```

The trace starts with empty mappings and grants.
It can advance the clock, close a flow, or flush the tables.
The input supplies public allocations and deadlines in one abstract time unit.
The default budget limits policy compilation to 100,000 partition cells.
It does not bound trace length or table size.
Accurate observations and a complete trace remain assumptions.

## Alias reuse and packet freshness

Source translation removes the inside endpoint from the external header.
An old flow can expire before a new flow reuses the same public alias.
When the remote endpoint and protocol match, their external reply headers are equal.
Any decision function given the same state and header must treat those replies alike.
The library proves that this holds for arbitrary decision functions over the header abstraction.

```
lake exe netlib nat-trace examples/nat/alias-reuse.json --json
```

This passing trace restores a delayed old reply to the new inside endpoint.
The current NAT safety invariant still holds.
Policy provenance and mapping consistency cannot establish packet freshness.
Stronger claims need additional observations or lifecycle assumptions.

These models exclude TCP flags, sequence windows, handshake state, checksums, and fragmentation.
They do not establish full NAT standards conformance or native Linux conntrack correspondence.
The Linux snapshot importer retains its documented stateless scope.
The packet-transformation and stateful models need separate native bindings.

# Documentation process
%%%
tag := "documentation"
file := "documentation"
%%%

Lean, doc-gen4, and Verso use matching Lean 4.35.0 versions.
The docbuild manifest records exact dependency commits.
Doc-gen4 produces the API pages from the library declarations.
Verso produces this manual and checks its Lean examples.
Both builders run on the local computer.

Use the locked Python tools:

```
uv sync --locked --group dev
uv run --locked prek -a --quiet
```

The default hooks check Python lint, format, source policy, prose, and tool tests.
They do not compile Lean.
Run local compiler and compiled CLI checks through the manual stage:

```
uv run --locked prek -a --quiet --stage manual
```

Commit the reviewed source before the website build.
Run the website command from the repository root:

```
uv run --locked python scripts/build_docs.py
```

The script saves the site in `docs/site.tar.gz`.
It records input hashes in `docs/site-manifest.json`.
The inputs include source modules, documentation, examples, and the Python dependency lock.
The combined site contains a manual and an API directory.
Each API source link uses the committed source version.
Commit the generated archive and manifest in a separate documentation commit.

Extract a checked copy into an empty folder:

```
uv run --locked python scripts/check_site.py --extract build/site
uv run --locked python -m http.server --directory build/site 8000
```

Review the pages at `http://localhost:8000/`.
Run the saved-site hook before a push:

```
uv run --locked prek -a --quiet --stage pre-push
```

CI installs the locked Python environment and runs the default hooks.
It also checks the saved site explicitly.
The manual Pages workflow validates and deploys those static files.
CI must not run the manual hook stage, install Lean, or invoke a documentation builder.
CI must never compile Lean code.

After a source change, generate the site again locally.
A stale archive must fail the CI freshness check.
After a Lean upgrade, select matching documentation tools and update the manifest.
Build and check the full library locally before the next site export.

# Technical glossary
%%%
tag := "glossary"
file := "glossary"
%%%

: Atom

  One observation in a logical formula.

: Access control list

  An ordered rule list whose first matching rule supplies the action.

: Availability

  A permitted path exists for each required source and target pair.

: Certificate

  A path or cut that the validator checks against the graph.

: Configuration

  The supplied devices, links, labels, and groups.

: Countermodel

  An assignment that satisfies the policy and makes a goal false.

: Cut

  A node set closed under the relevant permitted steps.

: Gateway mediation

  Every permitted path visits the selected gateway set.

: Isolation

  No permitted path connects any selected source and target pair.

: Flow grant

  A timed permission for a reply with the exact reversed five-tuple.

: NAPT

  Translation of a network address and transport port.

: Packet header

  The addresses, protocol number, and port numbers that a packet match reads.

: Refinement

  A mapping that connects physical steps to abstract paths under explicit assumptions.

: Selector

  A name that selects devices by node identity, zone, role, or group.

: Traffic class

  A named service for which the checker selects permitted links.

: Trust boundary

  The line between the formal guarantees and the inputs or assumptions that need separate review.
