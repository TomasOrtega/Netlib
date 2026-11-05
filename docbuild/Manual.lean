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
 * `Netlib.Import` reads strict hostapd, route, firewall, and conntrack inputs.
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

## Composable processors and ordered executions

A packet processor returns an updated store and an optional output header.
A drop skips the remaining stages while retaining every update from completed stages.
A prefilter can prevent a NAT grant from being installed.
A postfilter can drop the packet while leaving its grant in place.
The library proves both order effects.
It also proves a reply roundtrip through two NAT stages with independent stores.

Sequential processor composition is associative:

```lean
open Netlib.Packet in
example {Store : Type}
    (first second third : Processor Store) :
    (first.seq second).seq third =
      first.seq (second.seq third) :=
  Processor.seq_assoc first second third
```

Ordered execution records one output or drop for each supplied packet input.
It passes the complete resulting store to the next call.
The trace theorem includes dropped packets that changed state.
Determinism connects each valid observed trace to the computed execution.
State invariants transfer through every call.

NAT pipeline traces refine the state changes of the existing NAT event model.
The refinement preserves stores rather than unfiltered outputs.
An earlier policy-permitted outbound input can authorize a reply even if a postfilter dropped that input.
This does not establish that the server received it.

The stateful forwarding graph retains a node, header, and store at every vertex.
Each successful edge threads its computed store to the next vertex.
Physical isolation and gateway mediation transfer to this graph.
Stateless processors recover the previous transfer semantics and preserve the store.
Every successful forwarding walk also projects to an ordered processor execution.
The projection retains every hop, physical adjacency, observed packet, and shared store result.

Dropped calls have no forwarding edge.
Their retained state changes belong to the ordered execution model.
These models do not provide concurrent packet scheduling or prove delivery under arbitrary interleaving.

## Campus reply failover

The stateful campus example adds reverse links to the earlier topology.
Each gateway has a separate NAT store.
Session permission guards outbound and return processing.
An application ACL restricts new grants.
The forwarding proofs retain management isolation, mandatory gateways, and store invariants.

The primary roundtrip uses the actual store left by the outbound path.
When that gateway fails, a physical path still exists through the standby.
Without standby flow grants, every client output header and store remains unreachable from the reply vertex.
Topology redundancy therefore does not establish reply availability.

With an exact pre-fault replica, a return path survives every admitted single internal-node fault.
Client and server failure and independent link failures fall outside that fault model.
The result assumes a fixed fault snapshot, current session permission, and no clock advance during the path.
Both gateways must be able to use the same public alias.

The ideal copy preserves the model invariant when the primary store is safe:

```lean
open Netlib.Examples.CampusNAT in
example (store : Store) (safe : store.1.Safe) :
    StoreSafe (replicatePrimary store) :=
  replication_safe store safe
```

Preserving both clocks also requires equal logical clocks.
The example does not prove a replication protocol, routing convergence, or live delivery.
Stale copies, replication delay, revocation propagation, and packet freshness require additional models.

# Conntrack snapshots and native evidence
%%%
tag := "conntrack"
file := "conntrack"
%%%

The native flow model uses original and reply tuples with effective direction zones.
Its lookup keys include the complete five-tuple.
Different remote peers can therefore share a public address and port.
This differs from the stronger endpoint-independent mapping invariant in the local timed NAPT model.

The XML importer reads the conntrack-tools 1.4.9 snapshot format with `libnetfilter_conntrack` 1.1.1.
It preserves fields, visible markers, source lines, and exact XML spans.
It rejects unsupported syntax and ambiguous keys.
XML does not expose the complete native status mask.
Its tuple pairs alone do not establish active NAT or policy authority.

The separate collector reads raw Netlink messages and retains full reported status.
It checks framing, sender, sequence, errors, loss signals, and successful dump completion.
The Lean importer validates the structured fields and the supported status conditions.
It retains raw bytes without proving that they decode to the supplied structured fields.
Collector behavior and capture authenticity remain evidence assumptions.

NAT selections determine which endpoints change.
Reply processing reverses those selections.
The status-compatible rewrite agrees with the tuple projection:

```lean
open Netlib.Protocol in
example (entry : NetfilterNAT.Entry)
    (valid : entry.Compatible)
    (direction : FlowNAT.Direction) :
    (entry.rewrite direction).apply
      (entry.flow.input direction) =
        entry.flow.output direction :=
  entry.rewrite_correct valid direction
```

The policy auditor checks every reported original tuple against certified packet intent.
Its result covers the supplied records in their original order.
This establishes permission under that intent, not how a native flow was created.

```
lake exe netlib conntrack examples/conntrack/native/conntrack.xml examples/conntrack/intent.json --json
lake exe netlib conntrack-map examples/conntrack/native/netlink.json 0 examples/conntrack/original.json --json
```

The second command requires full-status capture JSON.
A lookup miss means unassociated.
It does not mean that Linux denied a packet.
The commands do not extend the stateless Linux deployment adapter into a complete hook execution model.

The repository retains a real isolated capture from kernel 6.8.0-117-generic.
Pinned conntrack, formatter, and nftables sources produced its configuration and table evidence.
Two TCP and two UDP records share one public endpoint across two remote peers.
Six socket roundtrips agree with the tuple projection.
The joined reply tuples reverse server-observed wire tuples; they are not independent pre-NAT reply captures.
Original bytes, observations, versions, and source hashes remain available for review.

Normal dumps can omit tentative or hidden NAT-clash objects.
Timeout zero can represent a remaining fraction of a second.
The frozen model does not evolve a clock or establish state completeness.
Status checks reject the explicit-helper bit but do not identify every automatic helper attachment.
Transport acceptance, hook ordering, checksums, payload effects, kernel refinement, and live delivery need further arguments.

# Tracked forwarding and policy changes
%%%
tag := "lifecycle"
file := "lifecycle"
%%%

The ordinary forwarding lifecycle attaches a tuple before the modeled hooks.
It applies destination translation, destination routing, and the forward filter in that order.
Source translation and a late postrouting filter follow.
Only then can a fresh candidate become a confirmed record.
Fresh route, forward, and late drops leave the ordinary confirmed table unchanged.

Packet classification and attachment freshness are separate.
An original packet remains new until the record has seen a reply.
It can therefore be classified new while reusing a confirmed binding.
Such a packet does not reread new NAT rules.
A valid reply is classified established and sets seen-reply before later filters.
That state update survives a later filter drop.
It does not prove that the client received the reply.

The source adapters preserve ordered stateful filter decisions for all supplied state labels and headers.
The fixed NAT adapter preserves first-match endpoint rewrites at the two supported stages.
The replay derives a fresh candidate from those imported NAT rules only on a lookup miss.
It uses the stored binding for an existing attachment.
Native allocation, transport validation, and the correctness of the parser remain separate obligations.

Explicit deletion removes both direction keys of a record.
It preserves ordinary-table validity:

```lean
open Netlib.Protocol.ConntrackLifecycle in
example (state : State) (zone : Nat)
    (packet : Netlib.Packet.Header) (valid : state.Valid) :
    (state.erase zone packet).Valid :=
  state.erase_valid zone packet valid
```

The operation trace binds each result to its exact step and incoming state.
The audit report preserves every supplied event in order.
A passing report means agreement with all packet observations and every supplied stable-state observation.
Missing state observations remain distinct from declared empty states.
Observed values do not replace the state computed by the model.

```
lake exe netlib lifecycle examples/lifecycle/replay.json --json
lake exe netlib stateful-refines examples/lifecycle/native/forward-established-only.json examples/lifecycle/native/forward-initial.json --json
```

The native experiment records nine UDP packets, 30 chain visits, and eight table snapshots.
It shows a dropped first reply setting seen-reply without application delivery.
It also shows cached NAT bindings surviving rule changes, including packets still classified new.
After deletion, the old original becomes fresh and is denied under the changed rules.

The static filter comparison checks every modeled state label and packet header:

```lean
open Netlib.Check.StatefulRefinement Netlib.Import in
example (stronger : NftablesStateful.Snapshot)
    (weaker : NftablesStateful.Snapshot) :
    check stronger weaker = true ↔
      Meaning stronger weaker :=
  check_correct stronger weaker
```

Native comparisons also require the same hook and priority.
A failed comparison has a concrete state and header counterexample.
The default budget covers 100,000 cells across all five state labels.
Static inclusion does not prove a safe cutover, revoke an existing flow, or compare changing NAT and route contexts.

The lifecycle assumes valid unfragmented packets whose tracker accepts the modeled attachment.
TCP reopening, tracker replacement, expiry, concurrent changes, helper expectations, related traffic, and allocation races are outside the model.
The native experiment supplies no TCP transport-state evidence.
The proofs establish the modeled lifecycle and structural invariants, without kernel C refinement or a complete upgrade contract.

# Output exclusion after a cutover
%%%
tag := "revocation"
file := "revocation"
%%%

A late-filter barrier denies a selected output-header class for every modeled state label.
Its exact certificate checks policy and selection boundaries, including rule order and the explicit chain default.

```lean
open Netlib.Check.StatefulExclusion in
example (snapshot : Netlib.Import.NftablesStateful.Snapshot)
    (forbidden : Netlib.Packet.Match) :
    check snapshot forbidden = true ↔
      Blocks snapshot forbidden :=
  check_correct snapshot forbidden
```

Every forwarded lifecycle output passed that late filter after both NAT stages.
A valid barrier therefore excludes its forbidden class even for cached established bindings.
Deleting the stored binding is not necessary for this exclusion argument.
An established-only forward filter can still permit that cached traffic.

The ordered proof covers packets and explicit record deletion.
It also connects to certified upgrade snapshots when every selected packet pipeline comes from a safe snapshot.
The replay suffix retains the state produced by its full prefix.
A compliant report transfers model exclusion to every supplied suffix output observation.

```
lake exe netlib lifecycle-blocks TRACE.json MATCH.json --from N --json
```

The cutover is a zero-based event position, including deletion events.
The CLI requires a nonempty suffix containing a packet.
It certifies each selected late filter across all five labels and every selected header.
The total budget charges partition cells for every suffix packet event, including repeated configurations.
A failed barrier has a concrete permitted state/header counterexample, even if that context was never observed.
Success also requires agreement with all supplied observations in the complete replay.

The class describes headers after NAT.
A destination-only class can exclude requests while allowing replies in the opposite direction.
Users must connect translated endpoints to their intended restriction.
Native installation, barrier retention, hook traversal, and packets already beyond the hook need separate evidence.
The declared event position does not prove a physical drain or credential revocation.
All ordinary lifecycle transport and native correspondence assumptions still apply.

# Buffered cutovers and queue service
%%%
tag := "buffering"
file := "buffering"
%%%

A late barrier controls new admissions to a queue.
Earlier admitted packets can remain queued and arrive after installation.
The buffered lifecycle therefore separates the admission boundary from the delivery boundary.
Computed operation outputs join the FIFO tail.
Drops and explicit deletions enqueue nothing.
Service events remove exactly the smaller of their capacity and the pending length.

The old-prefix proof requires every later arrival to have the desired property.
Service capacity covering the initial backlog then establishes a clean pending queue:

```lean
open Netlib.Theory in
example (property : Nat → Prop) (initial : Queue.State Nat)
    (ticks : List (Queue.Tick Nat))
    (arrivals : QueueDrain.CleanArrivals property ticks)
    (enough : initial.pending.length ≤
      QueueDrain.totalCapacity ticks) :
    QueueDrain.CleanPending property
      (Queue.run initial ticks) :=
  QueueDrain.run_pending_clean property initial ticks
    arrivals enough
```

The total backlog can keep growing under overload while the older prefix clears.
The last draining batch can still contain older forbidden packets.
The exclusion guarantee starts after that batch and preserves earlier delivered history.
The buffered report computes both boundary states from the complete execution prefix.
A ready certificate establishes a clean pending queue, including at the end of the schedule.
Any later modeled continuation that retains the barrier has clean service outputs.
Observation agreement also transfers the result to the supplied service batches.

```
lake exe netlib buffered-lifecycle examples/drain/replay.json examples/drain/forbidden.json --from 1 --drained-at 3 --json
```

The native example records a queued old UDP packet arriving after barrier installation.
A later same-tuple packet hits the barrier and drops.
The model correctly retains the old forbidden delivery before the drain boundary.
Queue counters alone do not identify packets; the isolated recipe and socket payloads supply that association.
The proofs use declared FIFO service and make no wall-clock drain claim.
Physical service bounds, complete queue correspondence, and native installation still need separate evidence.

# Authentication messages and campus sessions
%%%
tag := "eap"
file := "eap"
%%%

The EAP layer separates packet framing, message correlation, method evidence, and application admission.
Raw Success packets and untrusted outer Identity bytes cannot set session authentication alone.
Accepted method evidence must match the expected principal, selected method, and current local round.

The binary codecs preserve supported messages and their padding.
They also reconstruct arbitrary accepted bytes:

```lean
open Netlib.Protocol.EAP in
example (bytes : List UInt8) (value : Decoded)
    (accepted : decode bytes = .ok value) :
    encodeDecoded value = .ok bytes :=
  encode_decode bytes value accepted
```

EAPOL and untagged Ethernet have the corresponding two-way byte proofs.
The text hex and MAC parsers have runtime tests.
Method bytes remain opaque and supply no cryptographic proof.

Current method evidence is a separate premise of authorization:

```lean
open Netlib.Protocol.EAPAuth in
example (context : Context) (state : State)
    (safe : state.Safe context)
    (authorized : state.authorized = true) :
    ∃ evidence, state.evidence = some evidence ∧
      evidence.ValidFor context state.round :=
  authorized_evidence context state safe authorized
```

The session bridge clears old credentials when authorization or the local round changes.
Application events cannot inject authentication.
Every application admission still needs the complete current credential guard.
The configured-principal campus theorem combines the checked report, that guard, and availability under each admitted internal-node fault.
Authenticated native checkpoints without application credentials remain isolated.

```
lake exe netlib eap examples/eap/success.json --json
lake exe netlib eap examples/eap/bad-server.json --json
```

Both commands pass by agreeing with their observations.
The first authorizes after the EAP-TLS exchange and later clears authorization after Logoff.
The second correctly denies a server-name mismatch.
The native principal differs from its anonymous outer Identity.
The wired capture retains raw frames, sanitized producer logs, public certificates, and exact configurations.

Trusted cryptographic results and method-to-round attribution remain explicit assumptions.
Local rounds are not wire nonces or native producer-window identifiers.
Physical controlled-port enforcement, wireless keys, RADIUS paths, and complete campus deployment bindings need further evidence.

# Session firewall enforcement
%%%
tag := "session-firewall"
file := "session-firewall"
%%%

The session compiler binds application scopes to packet classes.
A class is permitted exactly when its current scope guard permits access.
Overlapping permit and deny requirements cause a compilation error with a packet witness.
Unspecified traffic is denied.

The generated policy has the same meaning for every conntrack state:

```lean
open Netlib Netlib.Protocol Netlib.Packet in
open Netlib.Compile.SessionFirewall in
example {context : Context} {state : EAPSession.State}
    {requirements : List Intent}
    (compiled : Certified context state requirements)
    (ct : StatefulACL.CTState) (header : Header) :
    compiled.statefulSnapshot.permits ct header =
      compiled.snapshot.permits header :=
  compiled.statefulSnapshot_permits ct header
```

The native snapshot checker recomputes the session from each selected event prefix.
It checks both permission directions for all five states and all modeled headers.
An extra established-flow exception and a missing required permit each produce a counterexample.
Its budget covers compilation and all comparisons across the supplied snapshots.

```
lake exe netlib session-firewall examples/admission/bundle.json --json
```

Lifecycle output theorems connect the active forward filter to current EAP readiness and valid credentials.
Updated Logoff, close, and revocation policies block arbitrary cached flows.
The theorem requires the current filter to be installed and the reviewed principal-to-packet binding to hold.
It does not bound update latency or remove packets admitted to queues earlier.

The native capture measures a private routed UDP service before and after wired EAP-TLS authorization.
A declared local demonstration credential enables the selected request and reply.
Actual EAPOL Logoff and replacement policy stop the same flow while its conntrack row remains present.
Raw packet observations and socket results supply finite deployment evidence.
Cryptographic refinement, spoof resistance, distributed propagation, and physical wireless enforcement remain open.

# IPv4 and UDP wire bytes
%%%
tag := "wire"
file := "wire"
%%%

The wire layer derives packet-policy fields from captured bytes.
Its selected profile covers untagged Ethernet, IPv4 IHL five without fragmentation, and UDP with an exact payload length.
It preserves outer padding and validates the IPv4 header checksum and each present UDP pseudoheader checksum.
Zero UDP checksum means omission and remains distinct from verification.

Checksum synthesis works for arbitrary aligned fields and payloads:

```lean
open Netlib.Protocol.InternetChecksum in
example (first rest : List UInt8)
    (aligned : first.length % 2 = 0) :
    valid (first ++ wordBytes
      (checksum (first ++ [0, 0] ++ rest)) ++ rest) =
        true :=
  synthesize_valid first rest aligned
```

The codecs also reconstruct every accepted byte sequence:

```lean
open Netlib.Protocol.IPv4 in
example (bytes : List UInt8) (value : Decoded)
    (accepted : decode bytes = .ok value) :
    encodeDecoded value = .ok bytes :=
  encode_decode bytes value accepted
```

UDP reconstruction uses the actual IPv4 addresses in its pseudoheader.
The checked Ethernet value carries decode equations for the original input bytes.
Its exact reconstruction proof preserves MAC fields, checksums, payload, and outer padding.
The deployment theorem connects the decoded forward-stage header to current session credentials and EAP method readiness.
Stage attribution, installed policy, and principal-to-header binding remain assumptions.

```
lake exe netlib wire examples/wire/frame.json --json
lake exe netlib session-firewall examples/wire/bundle.json --json
```

The native capture disables checksum offload on its private veth interfaces and retains complete UDP checksums.
Separate raw probes show that gateway forwarding and destination UDP reception are different observations.
Invalid UDP checksums and lengths can pass the forward filter before the destination drops them.
An omitted checksum can reach the socket while supplying no UDP checksum verification.
The earlier admission capture retains offload intermediates and makes its original tuple-level claims.
The new wire checker rejects those partial checksums as completed wire bytes.

Options, fragments, IPv6, full TCP, and native implementation refinement remain open.

# Wire forwarding and NAT
%%%
tag := "wire-forwarding"
file := "wire-forwarding"
%%%

The forwarding wrapper derives its tuple from the checked IPv4/UDP input.
It attaches conntrack once, applies destination NAT, and selects the route before testing TTL.
A routed packet with TTL zero or one produces no selected UDP transit output.
It retains prepared reply observations and never confirms a fresh record.

Other packets use the existing forward filter, source NAT, late filter, and confirmation sequence.
Permitted output has decremented TTL and updated checksums.
The payload remains exact:

```lean
open Netlib.Protocol in
example {packet : UDP.DecodedIPv4}
    {target : Netlib.Packet.Header} {ttl : UInt8}
    (result : UDPRewrite.Certified packet target ttl) :
    result.packet.datagram.payload =
      packet.datagram.payload := result.payload
```

The transformation also preserves TOS, identification, DF, and packet length.
An omitted UDP checksum remains omitted.
A present checksum is recomputed using the translated tuple.
The inherited payload bound prevents an encoding failure after confirmation.

The replay checker validates actual ingress and egress bytes.
Its compliant-report theorem establishes agreement for every supplied event and table observation in order.
Matched observed outputs preserve payload and decrement TTL exactly once.
Intermediate null fields remain unobserved; null output means no selected UDP egress.

```
lake exe netlib wire-forward examples/wire-nat/replay.json --json
lake exe netlib session-firewall examples/wire-nat/session.json --json
```

The native capture uses two-sided NAT with complete checksums.
A TTL-one reply marks the cached record seen-reply despite having no UDP egress.
A later normal reply reaches the client.
Logoff and the current deny policy stop the same cached flow.
Separate probes cover erasure, TTL zero, TTL two, and UDP checksum omission.

The deployment theorem combines exact emitted packet facts with current scope credentials and EAP readiness.
MTU, fragmentation, ICMP generation, concurrency, and kernel C refinement remain outside this model.
Identity bindings, capture location, current installation, and cryptographic method fidelity remain assumptions.

# MTU and IPv4 fragment families
%%%
tag := "mtu"
file := "mtu"
%%%

The MTU extension accepts whole IPv4 UDP inputs and returns complete output fragment families.
Each route next hop has an explicit effective MTU between 68 and 65,535 bytes.
Route and path constraints can lower this value below the device MTU.

Routing precedes TTL expiry, which precedes oversized-DF rejection.
Early rejection retains prepared tracking state and never confirms a fresh candidate.
Other packets execute the existing filters, NAT, and confirmation exactly once.
Fragmentation follows successful translated output.

Every nonfinal payload has an eight-byte-aligned length.
The offsets cover the complete IP payload without gaps or overlap.
Every output header has a valid checksum and fits the selected effective MTU.
The UDP header and application payload are recovered together:

```lean
open Netlib.Protocol in
example {packet : IPv4.Packet}
    {mtu : IPv4Fragmentation.MTU}
    (result : IPv4Fragmentation.Certified packet mtu) :
    IPv4Fragmentation.reassemble result.fragments =
      .ok packet := result.reassembled
```

The recovery theorem also holds for every permutation of the generated family.
Strict reassembly rejects gaps, overlaps, duplicates, inconsistent metadata, and incomplete families.
UDP validation follows complete recovery.

```
lake exe netlib wire-mtu examples/mtu/replay.json --json
lake exe netlib session-firewall examples/mtu/session.json --json
```

The checker compares normalized fragment fields and the complete recovered datagram.
An empty output array asserts no selected UDP egress.
Null intermediate metadata remains unobserved.
Matched observed families preserve the exact input payload, decrement TTL, and fit their actual emission MTU.
Both forwarding checkers reuse the shared observed-execution certificate.
Observed disagreement cannot replace computed state.

The native capture forwards a 1,200-byte socket payload through NAT as three fragments on an MTU-600 path.
The server's UDP socket receives the exact original payload.
Additional cases cover DF rejection, TTL priority, exact-MTU DF forwarding, and checksum omission.
Those packet-mechanics probes use a separate fixed permit suffix.
Current EAP permission authorizes modeled families, while Logoff denies cached traffic.

ICMP generation, input reassembly, options, resource failures, concurrency, and native implementation refinement remain open.
Capture attribution, effective MTU, principal binding, and current installation retain explicit assumptions.

# ICMP errors and quoted NAT
%%%
tag := "icmp"
file := "icmp"
%%%

The ICMP extension generates Time Exceeded and Fragmentation Needed from the computed transit rejection.
It quotes the packet after destination NAT, then restores the embedded tuple through related NAT.
The restored quote equals the original input prefix, including its UDP checksum.
Only equivalent IPv4 checksum zero representations can differ.

Incremental checksum updates require the changed tuple words, without requiring missing application bytes.
The operation preserves checksum omission and has a general inverse:

```lean
open Netlib.Protocol in
example (checksum : InternetChecksum.Word)
    (removed added : Nat) :
    ChecksumRewrite.update
      (ChecksumRewrite.update checksum removed added)
      added removed = checksum :=
  ChecksumRewrite.update_inverse checksum removed added
```

The quote retains its original IPv4 and UDP declared lengths even when truncated.
The return MTU bounds generated output independently of the forward MTU reported by Fragmentation Needed.
For IHL five, the quote budget is `min(returnMTU, 576) - 28` bytes.
Only complete UDP quotations establish transport checksum validity.

The error reuses the opposite connection direction as related traffic.
Separate output and late policies govern control emission.
Fresh rejected candidates remain unconfirmed, and earlier reply observations survive.
Current-session guards still authorize UDP transit.
A control error does not imply application permission because TTL and DF rejection precede forward filtering.

```
lake exe netlib wire-icmp examples/icmp/replay.json --json
lake exe netlib session-firewall examples/icmp/session.json --json
```

The checker validates both the UDP transit family and the generated ICMP error.
Compliant observed quotations inherit the source-prefix and generation proofs.
Observed identification supplies an explicit allocator choice; the remaining semantic fields are computed.

A fresh capture retains twelve errors across full and truncated quotations, odd lengths, TOS changes, and checksum omission.
Native `LOCAL_OUT` and postrouting traces expose related filtering and NAT correction.
The selected profile disables rate limiting and assumes successful allocation and transmission.
This generation layer excludes received ICMP and host PMTU feedback; the next chapter connects both.
Input fragments, concurrency, and kernel refinement remain open.

# Received errors and host PMTU
%%%
tag := "received-icmp"
file := "received-icmp"
%%%

The received-error layer associates a reversed quoted UDP tuple and zone with confirmed connection state.
The outer destination must agree with the found tuple.
The quoted fields remain untrusted data, including incorrect checksums, declarations, and raw flag bits.

Related NAT restores the sender-boundary tuple and updates checksums incrementally.
Invalid checksum residue remains invalid.
The quoted TTL retains the earlier forwarding hop's decrement.
Forwarded errors lose one outer TTL, retain frozen conntrack state, and pass related forward and late policy.
Small egress MTUs produce certified fragment families.

The host matches the restored socket tuple and Fragmentation Needed kind.
PMTU updates model floor locking, refresh, and expiry.
Expired exceptions can restore the physical route MTU.
A drained-error DF send has the following capacity condition:

```lean
open Netlib.Protocol in
example (route : PMTU.Route) (state : PMTU.State)
    (now payload : Nat) :
    PMTU.send route state now true payload = .accepted ↔
      payload + 28 ≤ 65535 ∧
      payload + 28 ≤ (state.current route now).val := by
  simpa using PMTU.send_accepted_iff
    route state now true payload
```

The reporter address does not authenticate feedback.
A matching forged quote can lower an unlocked cached PMTU.
The composition theorem connects actual gateway output and restored quote bytes to the host update while conntrack remains frozen.

```
lake exe netlib wire-related examples/received-icmp/replay.json --json
lake exe netlib host-pmtu examples/received-icmp/host.json --json
```

The gateway replay checks sixteen events and the host replay checks nineteen observations.
Post-episode snapshots attach only to their final observed event; earlier prefixes can remain unobserved.
The native experiment uses an EAP/NAT edge, downstream router, client, and server.
It demonstrates PMTU 600, local oversized-send rejection, smaller UDP delivery, and a matching forgery lowering PMTU to 576.
Runtime tests also cover 68-byte output fragmentation and abstract exception expiry.

Received-error input reassembly, clock correspondence, broader host behavior, source identity, and implementation refinement remain open.

# Ingress queues and current policy
%%%
tag := "reassembly"
file := "reassembly"
%%%

Ingress reassembly buffers fragments before ordinary UDP attachment and NAT.
Queue keys retain effective defragmentation user, L3 master identity, addresses, protocol, and identification.
The selected namespace uses a fixed timeout and zero source-disorder distance control.

The model preserves Linux run grouping, including order-dependent duplicate classification.
It trims unaligned MF data and destroys queues on genuine overlaps or inconsistent final lengths.
Accepted first-header, ECN, DF, and size metadata determine the completed packet.
Proofs preserve byte provenance, key isolation, layout, and bounds through every computed arrival.

Incomplete fragments leave conntrack unchanged.
Completion evaluates the current installed session policy.
A fragment buffered before Logoff does not retain the earlier permission.
The deployment proof connects actual completion to a valid current scope and ready EAP method.

Output can require fragmentation again even when the whole datagram fits its route.
The retained maximum fragment size supplies another cap.
The shared output contract supports small legal budgets and different kernel layout paths.

```lean
open Netlib.Protocol in
open Netlib.Protocol.IPv4Refragmentation in
example (packet : IPv4.Packet)
    (cap : Budget) (df : Bool)
    (bounded : packet.Encodable) :
    reassemble (generate packet cap df bounded).fragments =
      .ok (outputPacket packet df) :=
  (generate packet cap df bounded).reassembled
```

Timeout errors use the expired queue's actual first-fragment header and accepted normalized payload prefix.
The codec includes reassembly time exceeded, type 11/code 1.
A VIP that is local before destination NAT can trigger this error.
The selected unassociated local-output path checks invalid-state permission and preserves conntrack.

```
lake exe netlib wire-reassembly examples/reassembly/replay.json --json
lake exe netlib wire-reassembly-timeouts examples/reassembly/timeout.json --json
```

Replay observations do not replace computed queue or ordinary-table state.
Native early-hook logging separates reassembly bytes from later mutable packet buffers.
Timeouts and event clocks share one unit; the native projection uses nanoseconds.
Allocation, capture authenticity, synchronous policy installation, and kernel correspondence remain explicit assumptions.
A complete arbitrary-arrival permutation theorem, broader transport behavior, and concurrency remain open.

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
