# Netlib specification

## Source and purpose

The source is DARPA-SN-27-13, *Verification and Compliance Checking for
Natural-Language Network Requirements (FastVacc)*. The notice date is
October 29, 2026. The supplied file is `DARPA-SN-27-13-2.pdf`.
Page references below include the cover of this six-page PDF.

The notice requests research into requirements, abstract reasoning, concrete
networks, and compliance reports. This repository implements that direction as a
Lean library and a finite network checker. The [scope limits](#scope-limits)
identify research problems that this implementation does not resolve.

## Requirements traceability

| RFI concern | Netlib contract | Evidence |
| --- | --- | --- |
| Formal intermediate system (pp. 3–4, question 1) | Give requirements explicit syntax and semantics. Connect evaluation to those semantics. | Definitions and theorems in `Netlib/Core/Logic.lean`. |
| Abstract reasoning before configuration (p. 3) | Analyze consistency and implication without a concrete network. | `Netlib/Core/Reasoning.lean`, `Netlib/Policy/Analysis.lean`, and `Netlib/Policy/Observation.lean`. |
| Redundancy (pp. 2–3) | Preserve every policy model after removal of a redundant requirement. | Preservation theorems and examples with duplicate or equivalent requirements. |
| Incompleteness (p. 3) | Find supplied security goals that the requirements do not imply. | Countermodels for missing goals. |
| Architecture proofs (p. 4, question 3) | Prove reusable results for isolation, mediation, refinement, and network changes. | `Netlib/Network/Basic.lean` and `Netlib/Network/Architecture.lean`. |
| Clusters and extensions (pp. 2–3) | Represent several physical nodes by one abstraction. State the refinement assumptions for each security result. | Cluster examples and explicit theorem hypotheses. |
| Exhaustive evaluation (p. 3) | Evaluate the complete declared network and every relevant endpoint pair. | `Netlib/Model/Config.lean`, `Netlib/Check/Compliance.lean`, and boundary tests. |
| Verifiable evaluation (pp. 2–3) | Validate path and cut certificates against a graph with only declared nodes. | `validPath_sound`, `validCut_sound`, and `check_compliant_iff`. |
| Understandable output (p. 2) | Keep source IDs. Report the proposition, status, and useful evidence. | `Main.lean`, `Netlib/Check/Render.lean`, and passing and failing examples. |
| Translation fidelity (p. 4, question 4) | Accept a specified controlled language. Reject unsupported input. | `Netlib/Policy/Language.lean`, parser rejection tests, and formalized examples. |
| Evaluation quality and scale (p. 4, question 4) | State the scope and resource limits. Supply reproducible examples. | Local builds, tests, and documented algorithm costs. |

## Network model

The original `check` command uses a finite set of nodes and directed links. Each node has
an ID, a zone, and a role. A named group can contain several nodes. Each link
permits steps for a service.

A matching enabled link permits a step for the selected service. An absent,
disabled, or nonmatching link permits no step. Reachability includes a path with
zero steps from a node to itself.

Reachability describes permitted paths in the model. It does not guarantee
physical packet delivery. The model excludes congestion, timing, device faults,
routing convergence, and omitted protocol state.

The JSON input must contain these arrays and fields:

| Array | Fields for each entry |
| --- | --- |
| `devices` | `id`, `zone`, `role` |
| `links` | `from`, `to`, `service`, `enabled` |
| `groups` | `name`, `members` |

The importer rejects unknown fields, missing fields, duplicate IDs, invalid links,
and empty groups. A link service of `*` permits every named service.
JSON input also rejects duplicate decoded object keys at every nesting level.
A requirement must name one service and cannot use `*`.

## Packet models

The Lean library also provides packet models. A header contains source and
destination IPv4 addresses, a protocol number, and source and destination ports.
Addresses use 32 bits. Protocol numbers use 8 bits. Ports use 16 bits.

A packet match can select source and destination prefixes, a protocol, and port
ranges. An absent match field accepts every value for that field.
Address prefixes include `/0` and `/32`. Reversed port bounds accept no port.

An access control list evaluates rules in order. The first matching rule supplies
the permit or deny action. An explicit default applies when no rule matches.
The standard `allows` function uses a deny default.

Routing selects the longest matching destination prefix. Equal prefix lengths
preserve the first route. A route supplies a next hop or a drop action.
Routing and access control lists define packet-specific forwarding networks.

The `dataplane` and `traffic` forwarding models are stateless.
They keep the same header throughout a path.
They exclude dynamic routing protocols.
The `dataplane` command imports these models through JSON schema 1.
The `traffic` command checks every header selected by a packet match.
It partitions headers at every ACL, route, and selection boundary.
Proved decision equality lifts the finite representative checks to the complete selected class.
The [traffic guide](TRAFFIC.md) defines its interface and cell budget.

Each forwarding step needs four controls:

1. An enabled physical link joins declared nodes.
2. The longest matching route selects that link's target.
3. The link's first matching ACL rule permits the packet.
4. The request policy permits any step through an enforcement gateway.

An empty ACL denies the packet.
A missing route or a selected drop route permits no next hop.
A route cannot create physical adjacency.
Each query fixes one header and one named request throughout its path.
Every selected endpoint pair must satisfy the query.

The importer rejects invalid references, duplicate identities, unsupported fields, and invalid numeric values.
An empty selection cannot satisfy a query.
`Config.finiteNetwork_eq_model` connects executable edges to the composed library graph.
`DataPlane.Check.Report.compliant_iff` connects the final status to every original query.
The [data-plane guide](DATAPLANE.md) defines the complete schema.

## Header-changing forwarding

`Netlib/Packet/Rewrite.lean` provides constant overwrites of address, protocol, and port fields.
An absent overwrite preserves its incoming value.
Sequential rewrites compose, and flow reversal exchanges the two endpoints.
Reply inversion requires the original endpoint as explicit information.

`Netlib/Packet/Transfer.lean` defines guards, rewrites, and their ordered composition.
Its forwarding graph retains both the current node and current header.
Physical links still constrain each modeled program step.
Header-preserving programs embed the existing forwarding graph semantics.

The `transfer` command checks one initial packet.
`Netlib/Import/TransferConfig.lean` imports declared nodes, guarded links, constant rewrites, and one query.
Each link tests the incoming header, applies its rewrite, and arrives at its fixed target.
Matching links remain permitted alternatives.
Separate stage nodes express processing order.
Routing lookup and Linux hook order are not implicit.

Reachability permits any resulting header at the target node.
Isolation excludes every resulting header.
Mediation requires a gateway on every path, including rewritten paths.
Gateway endpoints and zero-step reachability retain their existing meanings.
`Netlib/Check/Transfer.lean` checks packet-state path and cut certificates.
Its returned status agrees exactly with the stated query.

Initial values and overwrite constants generate a finite header universe.
Closure proofs cover every modeled path from the initial packet.
The default budget is 4,096 device/header states.
The checker counts that product before constructing the states.
Budget exhaustion or certificate rejection returns an error without an answer.
There is no theorem guaranteeing successful search completion for every valid input.
All-header class verification across rewrites remains future work.

## Timed flow state and source NAPT

`Netlib/Protocol/Conntrack.lean` grants one TCP or UDP flow and its exact reverse reply until its deadline.
Time is monotone.
Closing a flow removes its grant.
`Netlib/Protocol/NAT.lean` maps an inside endpoint and protocol to a supplied public endpoint.
The mapping can serve several remote peers.
Each peer still needs a separate live reverse-flow grant.

Accepted transitions preserve live entries and unique mapping keys.
An accepted outbound packet has a source-endpoint rewrite.
Its exact reverse reply restores the inside endpoint while the grant remains live.
Public-endpoint collisions and changes to an existing live mapping cause denial.
Expiration removes old entries.
Closing a flow can leave its mapping in place.
Flush clears grants and mappings while preserving the clock.

The `nat-trace` command audits every supplied packet observation from an empty initial state.
`Netlib/Check/NATTrace.lean` obtains outbound permission from the declared packet-intent policy.
The input cannot supply an authorization result.
Each finding compares observed output with independently computed model output.
Correct denials can pass.
Every matched restored reply has an earlier outbound source permitted by that policy.
Accurate observations, complete traces, and clock interpretation remain assumptions.

Allocations and expiration deadlines remain supplied inputs.
The default budget covers 100,000 policy partition cells, not trace processing.
`Netlib/Import/PacketFields.lean` reads bounded packet fields and dotted IPv4 addresses.
Its codec and the trace parser have runtime tests rather than parser-correctness proofs.

`Netlib/Theory/NATReuse.lean` proves a freshness limit after public-alias reuse.
Different inside endpoints can produce identical external reply headers for the same remote endpoint and protocol.
No deterministic decision using only that header and the same current state can distinguish them.
A proved trace expires the old flow, reuses its alias, and delivers the delayed reply to the new inside endpoint.
The current mapping and grant safety invariant still holds.
That invariant therefore cannot establish rejection of retired replies.

These models exclude checksums, fragmentation, TCP flags, sequence windows, and transport handshakes.
They do not establish allocator correctness, public-address ownership, Linux conntrack correspondence, or complete RFC conformance.
The Linux deployment adapter retains its stateless subset.
The [stateful guide](STATEFUL.md) defines the input formats and evidence limits.

## Native conntrack snapshots

The separate `Protocol.FlowNAT` model represents reported original and reply TCP/UDP tuples in one implicit capture namespace.
Each direction has its effective zone and complete header as a lookup key.
Validation rejects duplicate combined keys, including original/reply collisions across entries.
Different remote peers may share the same public endpoint.
This differs from the local NAPT model's globally unique public-endpoint/protocol mapping.

A matching original tuple projects to the reversed reply tuple.
A matching reply tuple projects to the reversed original tuple.
Validated lookup and round-trip theorems establish those operations over the supplied table.
A miss means the table contains no association; it does not establish packet denial.
Remaining timeout is evidence in whole seconds.
Zero remains valid evidence because the native export truncates fractional seconds.
The model does not evolve time, allocate new flows, refresh timeouts, or validate transport packets.

`Protocol.NetfilterNAT` adds source/destination NAT flags to each tuple pair.
The flags select which endpoint fields change and reverse their roles for reply processing.
Compatibility requires unchanged endpoints wherever a NAT flag is absent.
The status-selected rewrite is proved equal to the tuple projection under those conditions.
This contract covers the complete modeled connection boundary, without an implicit per-hook execution order.

The `conntrack` command checks every supplied original tuple against a declared packet-intent policy.
It accepts the supported conntrack-tools XML slice or full-status collector JSON.
Its passing status means that all reported original tuples satisfy the certified intent.
The report preserves row order, source locations or indices, and available native IDs.
It does not establish the policy that admitted a flow or the provenance of a restored reply.
An empty raw snapshot has no rows to violate this condition; the XML slice requires a nonempty snapshot.

XML preserves original/reply tuples and selected metadata from conntrack-tools 1.4.9 with libnetfilter_conntrack 1.1.1.
Its status markers do not provide the full native status mask or establish NAT activation.
The `conntrack-map` command therefore requires full-status collector JSON.
It reports a frozen association and projected header, rather than a firewall-admission result.

The full-status profile requires confirmation and checks NAT initialization and tuple compatibility.
It rejects expected, sequence-adjustment, dying, template, NAT-clash, explicit-helper, offload, and unknown status bits.
Rejecting the explicit-helper bit does not establish absence of automatically assigned helper extensions.
Additional native attributes remain in raw evidence without modeled payload semantics.
Missing timeout metadata is unsupported in this profile; optional ID, mark, and use fields can remain unknown.

`scripts/capture_conntrack.py` sends a fixed IPv4 Netlink dump request inside the isolated native environment.
It retains the request and complete messages while rejecting malformed, interrupted, truncated, or lost dumps.
The requested IPv4 family filter is supported.
Capture budgets and transport errors produce no successful partial output.
The Lean JSON importer retains these bytes as hexadecimal evidence without independently decoding them.
The collector's decoding and the agreement between raw and structured fields remain reviewed implementation boundaries.

The retained native example has four flows and six successful socket round trips on Ubuntu kernel `6.8.0-117-generic`.
Both TCP and UDP reuse public `203.0.113.1:40000` across two remote peers.
Structured records agree with the retained Netlink bytes and XML tuples and IDs.
Socket metadata records server wire headers and client restored headers.
The joined reply tuples are derived from reversed server wire tuples, without independent pre-NAT reply IP captures.
The collision and late-drop examples record no replies and no additional visible confirmed records.
These observations support the demonstrated cases, without proving kernel C refinement, complete table coverage, or general packet delivery.
Upstream Linux v6.8 supplies the source reference; distribution patches remain outside that correspondence.
The [conntrack guide](CONNTRACK.md) defines the commands, supported records, and capture procedure.

## Stateful filters and fixed NAT snapshots

`Packet.StatefulACL` combines the existing header match with an optional connection-state selection.
The first matching rule supplies the action, followed by the explicit fallback.
The five labels are `new`, `established`, `related`, `invalid`, and `untracked`.
The matcher has independent propositional semantics.
Specialization at one fixed label gives an equivalent ordinary ACL for every header.
Unguarded rules recover the original stateless behavior.
The label is an input to this filter model; it does not establish transport state or authorization.

The shared nftables syntax decoder preserves the original stateless adapter's forward-only subset.
That adapter still rejects state predicates and NAT statements.
`Import.NftablesStateful` separately accepts one IPv4 filter chain at forward or postrouting.
It preserves ordered header/state matches, the chain policy, handles, and source expression indices.
Its compiler agrees with structured source evaluation for every supplied label and header.

`Import.NftablesNAT` accepts one IPv4 table with destination NAT at prerouting priority -100 and source NAT at postrouting priority 100.
Both chains have NAT type and accept policy.
Each rule has supported header matches and one fixed address target with an optional port.
The first matching target stops its chain, including an identity target.
A miss preserves the header, and an omitted target port preserves its incoming value in this model.
Ranges, maps, dynamic targets, masquerade, extra chains, and side effects are unsupported.

The structured NAT compiler preserves source-rule matching and endpoint translation.
Its candidate records the original tuple and reversed translated tuple, with NAT flags derived from endpoint changes.
Compatibility follows under explicit protocol, zone, and distinct-key conditions.
This candidate is a proposal, not proof of native allocation or port preservation.
The replay assumes that a confirmed fixed proposal is the applicable native allocation.
It rejects confirmation collisions instead of simulating native remapping or race recovery.

## Ordinary forwarded-packet lifecycle

`Protocol.ConntrackLifecycle` gives ordinary forwarded packets an explicit hook sequence.
A confirmed record contains a compatible tuple pair and a seen-reply flag.
Lookup uses the complete input header and zone once, before the stages below.
A miss requires a separate unconfirmed candidate whose original tuple and zone match the input.
Intermediate packet rewrites retain that attachment.

Processing follows this order:

1. Classify the attached original or reply and mark seen-reply for an existing valid reply.
2. Apply destination NAT, including inverse source NAT for replies.
3. Select the longest matching destination route using that translated destination.
4. Evaluate the stateful forward filter on the packet after destination NAT.
5. Apply source NAT, including inverse destination NAT for replies.
6. Evaluate the late filter on the packet after source NAT.
7. Confirm a fresh candidate only if all prior stages permit it and its combined keys remain unique.

A missing next hop, a forward denial, or a late denial produces no output.
A fresh drop leaves the confirmed table unchanged.
An existing reply can mark seen-reply even when one of those later stages drops it.
The next original can therefore be established without an application receiving that first reply.
These transitions do not infer a completed transport handshake.

An existing original is `new` before seen-reply and `established` afterward.
Both cases reuse the stored binding with `fresh = false`.
Changing NAT rules does not recreate that binding merely because the current original is `new`.
A leading established permit can also preserve old traffic after the filter starts denying new traffic.
Structural validity proves compatible records and unique lookup keys, without establishing the current policy's authorization of every stored flow.

`Protocol.ConntrackOperations` adds an explicit erase operation by either directional key.
It removes both directions of the associated record and preserves structural validity.
Its execution trace binds every returned result to the exact operation and preceding table.
Packet calls can select different policy snapshots within that ordered trace.
The model does not infer an erase from a later table observation.

The `lifecycle` checker accepts schema 1 with routing, named configurations, an initial table, and ordered events.
Routing imports the pinned iproute2 6.19.0 main-table slice and trusted device bindings.
Each configuration contains separate forward, late, and fixed NAT snapshots.
The forward chain must use the forward hook.
The late chain must use postrouting with priority greater than 100 and less than 2147483647.
This places it after source NAT and before modeled confirmation.

The checker derives a candidate from the selected NAT table only on a lookup miss.
The input cannot supply a candidate or an authorization Boolean.
Observations do not update the modeled table.
Every packet observation compares classification, freshness, both stage headers, next hop, disposition, and final output.
Every supplied state observation compares both tuples, zones, NAT flags, and seen-reply after the operation.
Timeout seconds, IDs, marks, use counts, other supported status metadata, and record order do not affect that comparison.
Native records and metadata remain retained evidence.

Root `initial: null` declares an empty initial table.
Event `state: null` records no table observation; it does not assert an empty table.
An initial native table normalizes timeout evidence to zero for replay without asserting expiration.
`Report.covered` preserves all events in order.
`Report.compliant_iff` states exact agreement with the complete supplied observation list.
`Report.prefixes_valid` proves structural validity of every modeled prefix and the final table.
Observation mismatch gives a noncompliant report.
Malformed input, unsupported execution, or confirmation collision gives an error without a compliance answer.

The native lifecycle evidence records nine UDP packets, 30 traced chain visits, and eight table observations.
All ten replay operations, including one erase, match the model.
The capture shows combined DNAT/SNAT stages, fresh drops before confirmation, cached unreplied bindings after a NAT change, and seen-reply after a dropped reply.
The independent evidence verifier checks retained trace, socket, and raw snapshot records.
These cases do not validate the complete TCP lifecycle or formally refine kernel C.

The domain requires valid unfragmented IPv4 TCP/UDP packets whose transport tracker accepts the modeled attachment.
The protocol-number check does not establish transport validity.
TCP reopen, replacement, and `NF_REPEAT` are unsupported.
Expiry, concurrent changes, helpers, related traffic, offload, hidden clashes, and allocator or race recovery are also excluded.
The main-table route context and exclusive captured NAT/filter hook sequence must apply to the selected traffic.
Faithful observations and complete selected-traffic coverage remain assumptions.
The [lifecycle guide](LIFECYCLE.md) defines the schema, producer versions, and native evidence boundary.

## Static stateful filter refinement

The `stateful-refines` command checks permission inclusion between two stateful source chains.
Every label and every modeled header is covered through ACL specialization and exact partitions.
The contexts include related, invalid, and untracked, even though the ordinary lifecycle only produces new and established.
A context in this comparison need not occur in a native history.

Both chains must have the same hook and priority.
The default budget is 100,000 header cells summed across all five labels.
A context mismatch or exhausted budget gives an error without a refinement answer.
A failed inclusion check returns a label and header permitted by the proposed stronger chain and denied by the weaker chain.
Theorems connect both successful inclusion and returned counterexamples to the structured source-chain semantics.

This is a static filter comparison.
It does not compare routing, NAT tables, allocations, stored bindings, or execution histories.
It does not prove revocation of old flows or a complete network upgrade contract.
Those claims require the relevant state transitions and intermediate-state obligations.

## Operational output exclusion

A late-filter barrier denies every header in a forbidden class for every modeled state label.
Its exact certificate includes policy and selection boundaries and preserves first-match order and explicit chain defaults.
A failed certificate has a concrete selected state/header context that the filter permits.
It need not be a packet in the supplied replay.

Every forwarded lifecycle output passed the late filter after both NAT stages.
The barrier therefore excludes the forbidden output class for fresh and cached bindings alike.
The theorem covers original and reply attachments without requiring deletion or a changed NAT allocation.
Ordered operations retain the result through packet calls and record deletion.
Certified upgrade snapshots supply the same contract when each packet pipeline selects one of those snapshots.

`lifecycle-blocks TRACE.json MATCH.json --from N` checks the complete replay and a selected event suffix.
`N` is a zero-based list position, including deletion events.
The suffix starts with the state produced by the full preceding replay.
The CLI requires at least one packet event in the suffix and rejects out-of-range positions.
It checks every late filter selected by suffix packet events; unused configurations are outside that check.
The default budget covers 100,000 partition cells across those events and all five state labels.
Repeated configurations are charged for every packet event.

The result separates the barrier certificate from replay agreement.
Success requires both.
The report proof then excludes the forbidden class from every supplied suffix output observation.
Prefix observation failures still prevent success.
The model exclusion theorem only needs the barrier certificate.

The forbidden class describes output headers after NAT.
It does not automatically describe a credential, user, session, or both directions of a connection.
Cutover follows effective barrier installation; packets already beyond the hook need a separate drain boundary.
The checker does not prove native install completion, barrier retention between observations, or absence of unreported configuration changes.
The [output exclusion guide](REVOCATION.md) states those obligations and the inherited lifecycle assumptions.

## Stateful processing and shared execution

`Netlib/Packet/Processor.lean` models ordered packet processing with a shared store.
These compositional interfaces are Lean library definitions.
Each processor returns the next store and either an output packet or a drop.
Composition passes both the store and the packet to the next stage.
A drop skips later stages and retains earlier state updates.
Processor invariants must cover those drop results too.

`Netlib/Packet/Stateful.lean` gives forwarding vertices a node, header, and complete store.
A successful edge must use the exact store produced by its processor.
It cannot independently choose a store for the next hop.
Physical adjacency limits these steps.
Physical isolation, gateway mediation, and processor store invariants transfer to their paths.
Stateless processors retain their store and agree with the existing packet-transfer semantics.

This forwarding graph contains successful packet steps.
It does not account for every call or state change between packets.
`Netlib/Packet/ProcessorTrace.lean` supplies ordered executions for that purpose.
Its observations include calls that drop packets after changing the shared store.
An explicit ordered call list supplies the execution schedule.
Each valid finite observation trace agrees with the computed execution.
These are model executions. Actual event coverage and implementation correspondence still require evidence.

`Netlib/Packet/StatefulTrace.lean` projects each successful graph walk to its ordered processor observations.
The resulting execution retains the same initial and final stores and every hop's physical adjacency.
This is a one-way bridge from a valid walk.
It does not infer a walk from packet headers without the required intermediate stores.

`Netlib/Protocol/NATPipeline.lean` connects the local NAPT model to these processors.
ACLs can act before or after translation.
An earlier denial prevents the translation and grant update.
A later denial can leave the new mapping and grant installed.
A return-flow origin therefore identifies an earlier policy-permitted input, which may have dropped at a later stage.
State refinement preserves the underlying NAT updates while filtered packet outputs can differ.
Two successful translations restore their reverse reply in the opposite processing order.
This local NAPT pipeline does not define native Linux lifecycle behavior.

The campus NAPT example uses separate primary and standby stores on the duplex campus topology.
It proves management isolation, gateway mediation, store invariants, and session-controlled forwarding.
An accepted primary outbound call establishes the store used by its restored reply path.
After primary failure, physical connectivity alone cannot supply missing standby grants.
With an empty standby grant list, every modeled return to the client fails.

An exact copy of the accepted outbound state supplies a return path under each admissible single internal-node fault.
The fault model excludes independent link failures and keeps client/server endpoints live.
The copy is an explicit ideal operation before the fault.
The clock-preservation result requires the original clocks to agree.
Each path uses a static fault snapshot and fixed session and clock states.
Shared-alias ownership and suitable return routing remain assumptions.
The result establishes a permitted path, not physical delivery, temporal liveness, or routing convergence.
Replication protocols, delayed or stale copies, revocation, and packet freshness remain outside this example's guarantees.

## Request model

`Netlib/Security/ZeroTrust.lean` models a principal's operation on a resource.
A request policy supplies authentication and authorization functions.
Admission requires both results to be true. The model assumes that the supplied
functions describe the intended identity and permission checks.

An admitted request retains the base network and all its paths.
A denied request loses every link that enters or leaves the enforcement gateway
set. It retains links that avoid that set.

All selected sources and targets must lie outside the gateway set for the
denial-isolation equivalence. Under that assumption,
`denied_isolated_iff_mediated` proves that denial gives isolation exactly when
every base path visits a gateway. A surviving denied-request path must bypass
the gateway set. A bypass can therefore preserve unauthorized access.

A gateway still reaches itself through a zero-step path after denial.
The outside-endpoint condition prevents that case from invalidating the isolation
claim. Stronger request policies cannot introduce request paths.

The data-plane importer reads declared principals, identity results, and permission facts.
It does not query a live identity service.
These proofs do not establish cryptographic authentication or live enforcement behavior.

## Standards catalogue

Each source record contains the document, version, clause ID, and URL.
Each requirement also records its meaning, applicability, and assumptions.
Each finding preserves the requirement and its evidence.

The catalogue uses five finding statuses:

| Status | Meaning |
| --- | --- |
| Satisfied | The selected model condition holds under its assumptions. |
| Violated | The selected model condition fails. |
| Unsupported | The checker does not model the required property. |
| Missing evidence | The checker lacks a required input or observation. |
| Not applicable | The requirement does not concern the stated scope. |

Only satisfied and not-applicable findings can pass.
An empty report cannot pass.
Evidence completeness means that no finding is unsupported or missing evidence.
It does not mean that every requirement is satisfied.

## Enterprise Wi-Fi pilot

The strict hostapd importer covers one AP and one BSS from hostapd 2.12.
It preserves source lines and rejects unsupported configuration syntax.
Unknown fields, repeated fields, includes, multiple BSS declarations, and invalid numbers cause errors.
Reports hide the RADIUS shared-secret value.
The parser preserves SSID and shared-secret bytes.

The selected AP profile checks 12 explicit obligations.
Each obligation identifies a hostapd field or Campus WLAN 3.2.0 clause.
An AP setting establishes only its declared configuration condition.
It does not establish client behavior, negotiated algorithms, product approval, or operational assurance.

The deployment profile adds five fixed network requirements:

1. Permit selected guest HTTPS traffic to services.
2. Isolate guest traffic from the management network.
3. Mediate service paths through the boundary gateway.
4. Mediate service paths through the imported AP.
5. Isolate service traffic for the unauthenticated request.

The input cannot remove or reorder these queries.
The AP interface and bridge must match the deployment binding.
Exactly one modeled access point must have the bound identity.
That AP must belong to the enforcement group.

The report connects source clauses, imported settings, model queries, and checked path evidence.
Its 17 findings cover the selected AP and network obligations.
The separate coverage report identifies unsupported requirements and missing evidence.
The [Wi-Fi guide](WIFI.md) records the source versions, configuration fragment, and deployment assumptions.

## Session and 5G profile

The shared session model records identity results, a credential, a clock, and guarded admission.
Model transitions preserve its admission invariant.
Clock transitions cannot decrease time.
Credential changes and time changes clear the previous admission record.
Generic local revocation clears the current credential.
It does not maintain a persistent token blacklist.

The 5G profile checks a direct NF-instance service-request trace.
Its source is TS 33.501 version 19.5.0, clause 13.4.1.1.2.
Every observed admitted request must satisfy the selected guards.
The guards check identity, token presence, issuer, integrity, subject, audience, scope, and expiration.
Correct denied requests do not violate admission safety.
Valid token reuse remains permitted.

The trace supplies identity and integrity observations.
The model does not verify TLS certificates or token signatures.
It also assumes that the trace includes every actual service admission.
The selected procedure has no token-revocation step.
The profile rejects that event instead of inventing a standard requirement.

`FiveG.check_compliant_safe` establishes the guards for every observed admission in a passing report.
A separate coverage report identifies missing identity evidence, missing cryptographic evidence, and unsupported optional claims.
The [5G guide](FIVEG.md) defines the trace schema and exact procedure scope.

## Requirement language

The text interface accepts one requirement per line:

```text
ID: SOURCE must reach TARGET for SERVICE.
ID: SOURCE must be isolated from TARGET for SERVICE.
ID: SOURCE must traverse GATEWAYS before TARGET for SERVICE.
ID: if CLAUSE then CLAUSE.
```

A selector is `node:NAME`, `zone:NAME`, `role:NAME`, or `group:NAME`.
A clause uses one of the first three forms without the ID or final period.
The parser ignores blank lines and full-line `#` comments. Requirement IDs must
be unique. The parser keeps source line numbers and rejects other sentence forms.

Each requirement applies to every ordered source and target pair:

| Requirement | Meaning |
| --- | --- |
| `must reach` | Every pair has a permitted path. |
| `must be isolated` | No pair has a permitted path. |
| `must traverse` | Every path for every pair visits the gateway group. |

Universal reachability and the existence of some reachable pair are different
observations. A selector must select at least one device. This condition also
applies to conditional clauses with false premises.

A gateway visit at either endpoint satisfies mediation. Mediation can hold when
no path exists. A separate reachability requirement must express availability.

An abstract role can represent several nodes, such as a gateway cluster.
A path visits that role when it visits at least one cluster member. A cluster
name alone does not establish high availability or encryption. Those properties
need separate models and assumptions.

## Abstract analysis

The formula language supports Boolean connectives and atoms with explicit
interpretations. Propositional analysis considers assignments to atoms
independently. Some assignments describe combinations that no network can realize.
A countermodel therefore identifies a logical gap. It need not describe a
deployable configuration.

`Netlib/Policy/Analysis.lean` extracts observations from the requirements and goals.
It needs no configuration. Requirement minimization keeps these domain laws fixed:

- Universal reachability implies some reachability when both selections contain
  devices.
- Universal and existential reachability agree for two node selectors.
- Isolation implies mediation by any gateway set.
- Each nonempty selection has some reachability to itself.
- Universal reachability composes through a nonempty intermediate selection for the same service.

`Netlib/Policy/Observation.lean` proves these laws under explicit assumptions about
nonempty selections and node identities. Analysis infers no other relationships
unless supplied formulas state them.

Concrete evaluation validates each selector against the configuration. Offline
analysis assumes a stated interpretation. It cannot detect an undeclared device
or group in a configuration that it does not receive.

Completeness concerns the supplied goals, vocabulary, and model. The checker
cannot discover an unstated operational goal. An inconsistent policy has no
model. Classical implication from that policy does not establish a secure network.

## Policy and network changes

Redundancy removal must preserve the complete policy. Each removal must account
for dependencies between requirements. Independent removal of all individually
redundant clauses can delete both copies of a duplicate. Netlib removes clauses
in sequence and proves that this process preserves the policy models.

Removal of permitted links preserves isolation and mediation. It can remove
availability. Additional links can create bypasses and need a new compliance
evaluation.

Refinement transfers security from an abstract architecture to physical nodes
only under the stated transition relation. Device labels alone do not establish
that relation. Mediation needs the stronger stuttering refinement conditions.

`Netlib/Network/Change.lean` also gives conditions for reuse of query results.
Two networks must agree on every outgoing link from a closed region.
That region must contain all queried sources. Under these conditions, reachability,
isolation, and mediation have the same values in both networks.
These theorems do not implement an incremental CLI cache.

Labeled transitions also describe protocol and operational state changes.
Finite trace refinement transfers invariants between abstraction levels.
Independent and synchronized state transitions compose through the product model.
The existing session model supplies one concrete adapter.

Certified update plans check the initial state, final state, and every intermediate snapshot.
Plan concatenation preserves the same contract.
Projection transfers update guarantees when concrete and abstract steps commute.
Real device update adapters remain outside the current implementation.

Domain graphs compose through explicit border transitions and shared abstract refinements.
The sum node type keeps domain identities disjoint.
Each border transition must preserve the abstract contract.
The graph union theorems use a common closed region.
Separate isolation of the inputs does not establish isolation of their union.

The fault model states permitted node and link removals.
Internally disjoint paths establish availability after one internal-node failure.
This theorem excludes endpoint failures and independent link failures.
The campus example composes these results with session enforcement and management isolation.
The [roadmap](ROADMAP.md) separates this foundation from the complete deployment objective.

## Trust boundary

Linux snapshot import and packet-intent compilation have structured translation proofs.
The native forwarding graph preserves source route lookup and source firewall evaluation under the documented transit assumptions.
The intent compiler rejects incompatible permits and prohibitions before it emits a certified ACL.
The emitter's structured native-format snapshot preserves that ACL for every header.
JSON parsing, serialization, kernel execution, and deployment operations need separate evidence.
The [Linux](LINUX.md) and [compiler](COMPILER.md) guides distinguish these guarantees.
The transfer checker separately certifies header-changing paths and cuts.
The NAT auditor separately certifies agreement with supplied packet observations.
Their current theorems do not connect those models to native NAT implementations.
The conntrack adapter adds checked visible tuples and status-aware endpoint algebra.
The separate lifecycle checker proves agreement with an explicit sequence of modeled route, filter, NAT, and deletion operations.
Its structural invariant does not establish transport validity or an arbitrary security contract.
The separate barrier proof establishes selected output exclusion through that sequence under its certified late-filter contract.
Collectors and native experiments supply evidence without proving kernel C refinement, complete kernel state, or historical admission beyond the supplied observations.

Lean verifies the theorem statements and proofs with the pinned toolchain.
Each theorem establishes its conclusion under its explicit hypotheses.
Review must establish the accuracy of source translation and the relation between
imported configurations and deployed equipment.

The input parser, configuration representation, abstractions, and reports need
review with the formal definitions. A path validator verifies the endpoints and
every step for the selected service. A cut validator verifies three properties:

1. The cut contains the source.
2. The cut excludes the target.
3. Every permitted step from the cut ends within the cut.

Gateway evaluation excludes the whole gateway set from bypass paths. It handles
endpoints in that set explicitly.

`Verification.evaluate` and `Verification.evaluateFormula` carry proofs of their
network and logical meanings. `VerifiedCompliance.check` audits reported
observations and certifies the original requirements. The CLI uses this function.

`check_compliant_iff` connects a successful report's final status to the formal
meaning of every original requirement. `check_results_covered` preserves their
exact list and order. The wrapper repeats certificate searches. This keeps the
report adapter separate from certified evaluation at the cost of repeated work.

Tests exercise the input and report code. They do not establish parser proofs or
vendor importer proofs. A theorem's stated model defines the scope of its claim.

The search returns a `Decision` with an accepted path or cut.
`Decision.correct` connects its Boolean value to finite network reachability.
A rejected certificate causes an internal error. It cannot produce an accepted
compliance result.

The build must contain no unfinished proof through `sorry` or `admit`.
Project-added axioms must not assert network properties. Examples supply
executable validation. Reusable theorems supply formal evidence.
The [proof inventory](PROOFS.md) lists the individual guarantees.

## Validation criteria

All Lean validation runs locally. CI must not compile Lean or invoke commands
that compile it indirectly. Documentation CI validates and deploys saved HTML.

1. The project builds with the pinned Lean version. No external theorem
   assumptions make examples pass.
2. Examples distinguish a compliant architecture, a bypass, an isolated target,
   and a change that invalidates an earlier claim.
3. Path evaluation terminates on cyclic graphs. It handles disconnected nodes,
   self reachability, and gateway endpoints according to the model.
4. Cluster examples distinguish a visit to one member from a bypass of all
   members. Unknown or empty selections cause errors.
5. Logical analysis distinguishes satisfiable policies, contradictions, redundant
   requirements, and goals with countermodels.
6. Requirement removal preserves meaning for duplicates and implication cycles.
   Analysis reports inconsistency before goal coverage can serve as evidence.
7. Malformed input causes errors. The parser rejects unsupported syntax.
   Concrete evaluation rejects selectors without devices.
8. Reports state their finite scope. They distinguish abstract countermodels from
   concrete path witnesses.
9. Packet, routing, and request suites contain 94 theorem examples.
   The request examples distinguish admission, denied mediated paths, surviving
   bypasses, and gateway self paths.
10. Transfer examples retain packet changes in witnesses and distinguish DNAT, bypasses, cycles, and exhausted state budgets.
11. Flow-state tests distinguish collisions, exact replies, independent peer grants, expiration, closure, and public-alias reuse.
12. The alias-reuse theorem identifies packet freshness that the current invariant cannot establish.
13. Lifecycle tests distinguish fresh preconfirmation drops, cached unreplied bindings, dropped-reply state updates, explicit deletion, and observation mismatch.
14. Static stateful refinement covers all five labels and every modeled header, with checked counterexamples and budget errors.
15. Output exclusion covers cached bindings, rule order, deletion, suffix state retention, unsafe unobserved contexts, and observation mismatch.

## Scope limits

Netlib does not translate arbitrary PDFs or recursively resolve external
requirements. It does not infer mission intent, device roles, or natural-language
meaning. Reviewers must supply and assess those inputs.

The implementation imports its declared hostapd fragment, selected Linux forwarding snapshots, and versioned model formats.
The [Linux guide](LINUX.md) defines the native input subset and its transit assumptions.
The [compiler guide](COMPILER.md) defines the proved intent-to-firewall translation and remaining correspondence work.
It does not inspect live networks or deploy network changes.
It does not certify complete CSfC, NIST, or 5G compliance.
Reference architectures show formal patterns within the stated model.

The current models exclude dynamic routing protocols and cryptographic algorithm correctness.
Full authentication protocols, transport handshakes, temporal liveness, and adversarial compromise remain outside their scope.
Constant packet rewrites and one local timed source-NAPT model have the separate guarantees above.
Fixed-endpoint tuple translation and ordinary forwarded-packet replay also have explicit domain and evidence limits.
Processors support ordered stateful composition with explicit stores.
Network-wide concurrent execution, distributed replication protocols, and native implementation correspondence remain future work.
Extensions need semantics, proofs, and rules that connect their input to those semantics.

The executable analysis has no fixed atom limit.
Its branch solver simplifies formulas after each assignment.
Every completed result carries a proof.
The default search node budget is 100,000 for each query.
An exhausted query returns an error without a consistency or entailment claim.
The budget does not limit total analysis time or memory.
Worst-case search can still require exponential work.
The exact truth-table interface remains available for reference checks.

Exhaustive network evaluation also has finite resource costs. The DARPA notice
targets a reduction of two to three orders of magnitude in time and cost.
This repository has no measurement that establishes that target.

Scalable symbolic solvers and external certificate generators can extend the
existing interfaces. Each extension must establish its connection to the formal
semantics.
