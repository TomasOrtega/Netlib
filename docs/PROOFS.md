# Proof inventory and trust boundary

Run `lake build` locally to verify the Lean declarations. The library adds no
axioms and uses no `sorry` or `native_decide`. Tests in
`NetlibTest/Core/Reasoning.lean` use kernel reduction or the general theorems below.

## Requirements and logic

`Netlib/Core/Logic.lean` defines a Boolean evaluator and propositional semantics
for formulas. `Formula.eval_eq_true_iff` connects the evaluator to those semantics.
`Formula.eval_eq_of_agree` proves that evaluation depends only on atoms in the
formula. `eval_map` and `holds_map` prove that atom translation preserves meaning.

`Netlib/Core/Reasoning.lean` enumerates every assignment to the distinct atoms in
the premises and conclusion. Its guarantees apply to this finite propositional
language:

| Declaration | Guarantee |
| --- | --- |
| `valuations_complete` | Each interpretation agrees with an enumerated assignment on the supplied atoms. |
| `satisfiable_iff` | The satisfiability check succeeds exactly when a model exists. |
| `model?_sound` | Each returned model satisfies all premises. |
| `model?_eq_none_iff` | No model exists exactly when the premises contradict. |
| `entails_iff` | The entailment check succeeds exactly when all premise models satisfy the goal. |
| `countermodel?_sound` | Each returned countermodel satisfies the premises and makes the goal false. |
| `countermodel?_eq_none_iff` | No countermodel exists exactly when the premises imply the goal. |
| `not_entails_iff`, `mem_missingGoals` | Each missing goal has a countermodel. |
| `minimize_preserves`, `minimize_subset` | Minimization keeps only original clauses and preserves all models. |
| `minimize_irredundant` | Removal of any retained clause changes the policy's meaning. |
| `completion?_sound` | A completion is satisfiable. It has the same models as the original policy together with the supplied goals. |

The minimizer removes one requirement at a time. It compares each requirement
with the policy that remains. Thus, two identical clauses become one clause.
They cannot both disappear through independent redundancy checks.

In classical logic, contradictory premises imply every formula. Callers must
establish consistency before they interpret goal coverage. Completion rejects a
contradiction between the policy and goals.

This truth-table interface remains an exact reference.
The executable analysis uses the budgeted solver below.
Neither solver guarantees fast answers for every formula.

## Budgeted search

`Netlib/Core/Solver.lean` assigns atoms and simplifies constant connectives.
Each completed answer contains a model proof or an impossibility proof.
`eval_assign` connects replacement to valuation updates.
`solve_model_sound` proves each returned model.
`solve_unsat_sound` excludes every model after an impossibility result.
`entails_correct` connects every completed entailment answer to the reference semantics.
`countermodel_sound` establishes each reported countermodel.

Each solver query has a search node budget.
The default is 100,000 nodes.
Both branches share that query's remaining budget.
An exhausted query returns an error.
It cannot report consistency, inconsistency, or entailment.
The executable has no fixed atom limit.
The budget does not limit total analysis time or memory.
See the [solver guide](SOLVER.md).

## Network laws and analysis

`Netlib/Policy/Analysis.lean` keeps domain laws fixed during requirement
minimization. The reference `Analysis.simplifyUnder_preserves` theorem proves preservation
for the original minimizer.
The executable uses `Analysis.simplifyUnderFast`.
Its `Reduction.correct` field proves the same model equivalence for every valuation.
Every deletion requires a completed solver entailment proof.

A completion can add only supplied goals. Analysis proposes no completion when
the combined requirements and goals contradict.

`Netlib/Policy/Observation.lean` connects abstract observations to networks.
`Observation.laws_sound` proves the generated domain laws for faithful network
interpretations. Its assumptions require nonempty selections and unique node IDs.
`Observation.entails_sound` transfers abstract entailments to these interpretations.

`Observation.inconsistent_excludes_interpretation` excludes compliant network
interpretations when the abstraction is inconsistent. The converse does not hold.
A satisfiable abstraction does not establish that a concrete network exists.

## Network architectures

`Netlib/Network/Basic.lean` defines directed reachability and walks. Its theorems
establish path composition, isolation after link removal, and region cuts.
They also connect mediation to gateway visits on every walk. Separate inner and
outer cuts establish two distinct gateway visits on every walk.

`Netlib/Network/Architecture.lean` transfers isolation through reachability
refinement. Its stuttering refinement also transfers mediation. These results
apply after link removal during failover. Availability needs an available
subnetwork whose links remain. Security alone does not imply availability.

`Netlib/Examples/Architecture.lean` gives reference architectures, a primary and
standby cluster, gateway layers, and a bypass example. The bypass example shows
why reachability refinement alone cannot establish mediation.

`Netlib/Network/Certificate.lean` connects executable validators to network
propositions. An accepted path establishes reachability. An accepted cut
establishes isolation in the declared finite network.

## Network changes

`Netlib/Network/Change.lean` defines closed regions and agreement between networks.
`reachable_iff_of_agreesOn` preserves reachability when networks agree on a closed
region that contains the source. `reachable_iff_of_unchanged_reachable` uses the
original source's reachable region.

`isolated_iff_of_agreesOn` and `mediated_iff_of_agreesOn` preserve isolation and
mediation when all sources lie within that region. The assumptions specify when
a saved query result remains valid. They do not implement an incremental CLI
cache.

## Packet policies and routing

`Netlib/Packet/Basic.lean` defines finite address, protocol, and port fields.
Prefix theorems cover `/0`, `/32`, containment, refinement, and disjointness.
Port range theorems cover single ports, all ports, and reversed bounds.
`Match.accepts_iff` connects the executable matcher to its field conditions.

`Netlib/Packet/ACL.lean` defines ordered access control lists.
`ACL.lookup_eq_some_iff` proves first-match semantics.
`ACL.default_deny_iff` connects the standard deny default to a first permit match.
Other theorems cover appended lists, leading deny rules, shadowed rules,
refinement, and serial controls.

Per-link access control lists restrict the forwarding graph for each header.
`Forwarding.reachable_original` proves that this restriction adds no paths.
`Forwarding.isolation_preserved` and `Forwarding.mediation_preserved` preserve
those security properties. Stronger link policies also preserve existing
isolation.

`Netlib/Routing/Basic.lean` selects the longest matching destination prefix.
Equal prefix lengths preserve the first route. The routing result supplies a next
hop or a drop action. The library connects routing and access control lists to
packet-specific forwarding.

These ACL and routing graph models preserve the header along each path.
The original `check` command uses named services.
The `dataplane` command uses the composed graph below.
Separate transfer and flow-state models appear below.

## Request enforcement

`Netlib/Security/ZeroTrust.lean` defines requests with a principal, resource, and
operation. A request policy supplies Boolean authentication and authorization
functions. `Policy.allows_iff` connects admission to both successful checks.
The model assumes that those input functions represent the intended checks.

`allowed_network_eq` proves that admission preserves the base network.
`admitted_reachable_iff` therefore preserves exactly its paths.
`denied_network_eq_without` removes every link incident to an enforcement gateway
after denial.

`denied_isolated_iff_mediated` gives the exact condition for denied-request
isolation. Every selected source and target must lie outside the gateway set.
Under that assumption, the denied request is isolated exactly when the gateways
mediate every base path.

`unauthenticated_isolated` and `unauthorized_isolated` apply this result to each
failed check. `bypass_survives_denial` proves that a bypass remains available after
denial. An unauthorized request can therefore retain access through a bypass.
Stronger request policies preserve existing isolation and cannot add paths.

The outside-endpoint assumption is necessary. A gateway retains its zero-step
path to itself after denial. These results do not prove authentication protocols,
cryptography, or live enforcement behavior.

## Validation examples

These three suites contain 94 theorem examples:

| Suite | Examples | Scope |
| --- | --- | --- |
| `NetlibTest/Packet.lean` | 42 | Header bounds, matches, rule order, and packet filtering. |
| `NetlibTest/Routing.lean` | 31 | Prefix selection, equal lengths, drop routes, and route-plus-ACL forwarding. |
| `NetlibTest/ZeroTrust.lean` | 21 | Admission, denial, mediated endpoints, bypasses, and policy refinement. |

The request suite includes the gateway self-path case.
It shows why gateway endpoints need a separate assumption.

## Composed data-plane checks

`Netlib/Model/DataPlane.lean` combines four controls.
Each step needs an enabled physical link, a selected route, a permitted ACL result, and any required gateway admission.
`Config.finiteNetwork_eq_model` proves that certificate search uses exactly this composed graph.
A route cannot create physical adjacency.
An empty ACL denies every packet.

`Netlib/Check/DataPlane.lean` gives each query a quantified proposition.
`Check.evaluate` returns the value, evidence, and proof for every endpoint pair.
`Check.Report.covered` preserves the original query list and order.
`Check.Report.compliant_iff` connects the final status to every original query.
Input validation rejects empty selections and invalid references before a report.

## Standards and Wi-Fi

`Netlib/Standards/Basic.lean` preserves document versions, clause IDs, applicability, assumptions, and evidence.
`Status.passes_iff` permits only satisfied and not-applicable results.
Unsupported requirements and missing evidence cannot pass.
An empty report also cannot pass.

`Netlib/Standards/IEEE80211/Enterprise.lean` checks 12 explicit AP obligations.
`Condition.evaluate_true_iff` connects each Boolean result to its independent setting predicate.
`status_satisfied_iff` preserves the meaning of missing settings.
`Wifi.check_sound` and `Wifi.check_complete` connect a passing report to every selected AP predicate.

The strict importer accepts one BSS from the hostapd 2.12 configuration fragment.
Reports preserve line numbers and hide the RADIUS shared-secret value.
These parser and presentation properties have runtime tests.
They do not follow from the configuration-predicate theorems.

`Netlib/Standards/IEEE80211/Deployment.lean` adds five fixed network queries.
The input cannot remove or reorder these obligations.
The importer binds the AP interface and bridge to exactly one modeled access point.
`network_finding_correct` connects each network status to its data-plane query.
`deployment_report_iff` proves equivalence between the combined report and both input reports.

The selected AP obligations include parts of Campus WLAN 3.2.0 requirements.
A setting establishes only its stated configuration condition.
Full EAP-TLS, negotiated algorithms, product approval, and operational evidence remain outside that result.
The [Wi-Fi guide](WIFI.md) identifies source clauses and coverage gaps.

## Sessions and 5G service admission

`Netlib/Protocol/Session.lean` records identity results, a credential, a clock, and guarded admission.
`Session.permits_iff` gives the independent credential conditions.
`Session.step_safe` and `Session.run_safe` preserve the admission invariant.
`Session.admitted_valid` establishes all guard conditions for a recorded admission.
`Session.clock_mono` preserves monotone time.
`Session.policy_allows` connects the session guard to the Zero Trust policy.

Generic local revocation clears the current credential.
It does not maintain a persistent token blacklist.
The selected 5G trace profile has no revocation event.
Valid token reuse remains permitted.

`Netlib/Standards/ThreeGPP/ServiceAccess.lean` checks a direct NF-instance procedure.
Its source is TS 33.501 version 19.5.0, clause 13.4.1.1.2.
`FiveG.check_compliant_safe` establishes the guards for every observed admitted request in a passing report.
Correct denied attempts do not violate admission safety.

Identity and integrity results remain supplied observations.
The trace must record every actual admission.
`FiveG.coverage` reports missing identity evidence, missing cryptographic evidence, and unsupported optional claims.
The [5G guide](FIVEG.md) gives the exact procedure and trace scope.

## Additional validation

The local solver suite compares small policies with the exact truth table.
It also checks 100-atom policies and contradictions.
Analysis tests cover 40-clause and 80-clause policies, conflict reduction, duplicates, and exhausted budgets.
The session suite includes 30 theorem examples and parser tests.
The profile fixtures include a separate failure for each selected admission guard.
CI runs Python source, text, package, and tool tests.
Lean theorem checks and compiled CLI fixtures run locally through the manual hook stage.

## Certified compliance results

`Compliance.Decision.correct` connects every accepted search result to
reachability in the queried finite graph. The search reports an internal error
if its certificate fails validation. An accepted decision carries its proof.

`Netlib/Check/Verification.lean` defines the configuration model and observation
semantics. `Verification.evaluate` returns a `CertifiedValue`. This value carries
a proof that its Boolean result agrees with the full quantified observation.

`Verification.evaluateFormula` gives the same guarantee for formulas with all
logical connectives, including implication. Gateway evaluation removes every edge
that touches a gateway. It handles gateway endpoints separately.

The CLI uses `VerifiedCompliance.check` from
`Netlib/Check/VerifiedCompliance.lean`. This function audits the observation values
from the input-facing checker. It also certifies each original requirement formula.
Its guarantees apply after a successful check:

| Declaration | Guarantee |
| --- | --- |
| `check_findings_correct` | Every reported observation value agrees with its network semantics. |
| `check_results_covered` | The results cover all original requirements in their original order. |
| `check_results_correct` | Each requirement status agrees with its formal meaning. |
| `check_compliant_iff` | The compliance flag is true exactly when every original requirement holds in the configuration model. |

The input-facing checker validates the configuration and every selector.
It also validates selectors in conditional branches whose premises are false.
Empty selections cause errors. They cannot produce a passing result through an
empty universal quantifier.

The status guarantee concerns the supplied formulas and model. It does not prove
parser correctness or report correctness. Inspection of the axioms for
`check_compliant_iff` and `check_results_covered` finds only standard Lean
foundations: `propext`, `Classical.choice`, and `Quot.sound`.

## Composition foundations

`Theory.Queue` implements a discrete FIFO queue with explicit arrivals and service capacity.
Its sequence conservation theorem covers complete runs.
It preserves modeled packet order without loss or duplication.
Backlog bounds require the stated arrival and service assumptions.
Repeated service drains a finite queue when no new arrivals occur and capacity is positive.
The queue has no finite storage limit or physical timing model.

`Packet.Interval` constructs bounded-field representatives from cut points.
`Packet.Partition.representative_mem` proves coverage of every header.
`match_stable`, `acl_lookup_stable`, and `route_lookup_stable` prove equal decisions within each cell.
`packetNetwork_eq` transfers those equalities to forwarding graphs.
`Check.Traffic` extends the equality through physical adjacency and request enforcement.
Its result proves the query for every selected header and endpoint pair.
Budget errors do not produce a result.

`Protocol.Transition` defines labeled traces and independent or synchronized state composition.
Invariants transfer through finite traces.
`TraceRefinement` permits concrete steps to denote finite abstract traces, including empty traces.
Its composition and safety theorems connect several abstraction levels.
The session adapter reuses the existing admission invariant.

`Network.Contract` composes domain graphs with disjoint node types through explicit border transitions.
Their local refinements must share the abstract architecture contract.
The border transitions must also satisfy that contract.
The union theorems use common closed regions.
Separate isolation proofs alone do not establish isolation after union.

`Network.Failure` states explicit node and link fault models.
Isolation and mediation survive link removal.
`robustAvailable_disjoint_walks` proves that internally disjoint paths preserve availability after one internal-node failure.
The model excludes endpoint failures and independent link failures from that availability claim.

`Network.Upgrade.check_correct` connects snapshot checks to every intermediate state.
`certify` returns a proof-bearing plan only after an accepted check.
Plans compose by concatenation.
Projection transfers the contract when concrete and abstract update steps commute.
The migration tests reject outages and bypass windows whose initial and final states both pass.

`Standards.Composition` gives clauses formal applicability, feature guards, and obligations.
Clause evaluation and profile conjunction preserve their declared semantics and original source records.
Compatibility returns a satisfying valuation or a proof that no valuation exists.
Version refinement returns an implication proof or a counterexample.
Unsupported clauses and exhausted solver budgets return errors.
Compatibility and refinement reject unsupported clauses even when a guard could make them inactive.
Compatibility concerns the supplied propositional facts.
Conflict sources include the entire input set and need not be minimal.
Logical version refinement does not establish that the stronger profile has a model.
An inconsistent context can make implication vacuous.

`Examples.Campus` composes domains, session enforcement, failure availability, and intermediate session updates.
It proves the declared application contract under the [roadmap's campus assumptions](ROADMAP.md#campus-landmark).
It supplies a foundation for the complete campus demonstration.

The offline network laws also cover reflexive and transitive reachability.
They require nonempty selectors and preserve the difference between universal and existential paths.
Sparse transitivity laws compose relevant relation pairs through each endpoint selector and service.
Independent reach requirements generate two local laws each and no transitivity laws.
Dense connected policies can still generate many laws before solver search starts.

## Native snapshots and intent compilation

`Import.LinuxRoute` preserves native route records and resolves explicit device/gateway bindings.
`Snapshot.nextHop_correct` proves compiled routing decisions equal the structured snapshot lookup for every destination.
Equal canonical prefixes cause errors before metric or multipath ambiguity can enter the model.

`Import.Nftables` preserves source-chain predicates, verdicts, policies, handles, and expression locations.
Its compilation theorems connect ACL evaluation to the independent structured source-chain meaning.
Transport port matches retain their protocol guard.
The parser rejects every unsupported expression, including expressions after a verdict.

`Import.LinuxDeployment` generates physical links, ACLs, and routes from the snapshots and bindings.
The parser checks node coverage and constructs a proof of unique router identities.
Lookup lemmas connect the generated configuration to the source router records.
`model_correct` proves equality with the structured native graph and declared external request enforcement.
Its scope is [main-table IPv4 transit](LINUX.md#guarantees-and-assumptions).

`Compile.ACL` checks permit/prohibition overlap over the complete packet partition.
A conflict includes a concrete header and both original source requirements.
`Conflict.unsatisfiable` rules out every ACL satisfying that conflicting demand pair.
Successful compilation preserves source IDs and proves all-header intent equivalence.
Input and budget errors cannot produce a successful certificate.

`Compile.Nftables.Emitted.correct` transfers that certificate to a structured native-format snapshot.
Capability checks reject port predicates without the required TCP/UDP protocol and native comment limits.
The separate JSON serializer has exact-partition roundtrip tests.
Pinned native nftables accepted and loaded generated JSON in a disposable Linux container.
Its re-export remains equivalent under bidirectional all-header refinement checks.
These tests supply interoperability evidence rather than parser or kernel proofs.

`Import.Json.parse` rejects duplicate decoded object keys throughout nested input.
The regression first failed with the original parser and now covers existing JSON commands.
A separate differential check matched Python key detection on 2,500 generated nested cases.
Parsing remains part of the reviewed implementation.

## Packet rewrites and transfers

`Netlib/Packet/Rewrite.lean` defines constant overwrites for the five packet fields.
`Rewrite.comp_apply` connects sequential overwrites to function composition.
`Rewrite.comp_assoc` proves associativity.
`Header.reverse_reverse` proves that reversing a flow twice restores its header.
The endpoint reply-roundtrip theorems require the original endpoint as explicit information.

`Rewrite.Universe.ofRewrites` collects initial values and every overwrite constant.
Its finite header product also supports reversal.
`initial_mem`, `rewrite_mem`, and `reverse_mem` prove closure for those operations.
`headers_length` proves the exact product size.
The construction does not enumerate all IPv4 addresses.

`Netlib/Packet/Transfer.lean` defines packet programs and forwarding over device/header states.
`Program.seq_assoc` and `rewrite_seq` connect program composition to rewrite composition.
`Program.guard_rewrite` states the incoming-guard, then rewrite order.
`Transfer.physicalProjection` connects program steps to declared physical links.
Physical isolation and mediation therefore transfer to packet-state paths.
`Transfer.fixed_reachable_iff` embeds the previous header-preserving graph semantics.

`Netlib/Check/Transfer.lean` checks one initial header against every modeled path and resulting target header.
Each link tests the incoming header before applying its rewrite.
The link fixes its target node.
It supplies no implicit routing lookup or native hook order.
`Config.edge_correct` connects the executable edge test to that step relation.
`states_closed` proves that paths cannot escape the generated finite state space.
`finite_reachable_iff` connects finite search to the complete query graph.

`Result.correct` covers reachability, isolation, and gateway mediation.
`Result.path_sound` preserves the exact packet-and-device walk.
`Result.cut_valid` retains a checked separation certificate for every target header.
Gateway endpoints and zero-step paths follow the existing network semantics.

The default budget is 4,096 device/header states.
`states_length` connects the preflight count to the generated state list.
Budget exhaustion and rejected certificates produce errors.
The proofs cover every returned answer.
They do not establish successful search completion for every valid input.
The [stateful guide](STATEFUL.md) defines the command scope.

## Timed flow grants and source NAPT

`Netlib/Protocol/Conntrack.lean` grants one TCP or UDP flow and its exact reverse reply.
`permitsReply_iff` gives the live-entry conditions.
`closed_reply_denied` proves exact-flow revocation.
`step_safe` and `run_safe` preserve live deadlines.
`clock_mono` prevents time reversal.
These results do not establish transport handshakes or TCP connection states.

`Netlib/Protocol/NAT.lean` separates source mapping from return-flow filtering.
`mapping_independent_of_remote` makes mapping depend on the inside endpoint and protocol.
Each remote flow still needs its own live reverse grant.
`outboundState_safe`, `step_safe`, and `run_safe` preserve live mappings and grants.
They also preserve unique inside/protocol and public/protocol keys.
`inbound_sound` requires a live public mapping and an exact live reverse grant.
`accepted_roundtrip` restores the private reply after an accepted outbound step.
`trace_reply_origin` connects a restored reply to an earlier authorized outbound event.

The allocator and expiration deadlines remain supplied inputs.
Close removes the selected flow grant while its endpoint mapping can remain.
Expiration purges old entries, and flush clears both tables.
The Linux snapshot adapter continues to reject native NAT and connection-tracking expressions.
These local models do not prove Linux behavior or complete RFC conformance.

## Stateful composition and execution

`Netlib/Packet/Processor.lean` returns an updated store and an optional packet.
`seq_assoc` proves ordered composition.
`seq_run_some_iff` threads the intermediate store and packet through both processors.
`seq_run_none_iff` covers drops in either stage.
`seq_drop_first` retains updates from a stage that drops its packet.
`Preserves` concerns every returned store, including drops.
Its composition and product-lift theorems preserve those store invariants.

`Netlib/Packet/ProcessorTrace.lean` records ordered calls that share one store.
`execute_covered` preserves the complete input list and order.
`execute_trace` connects computed observations to the transition relation.
`trace_eq_execute` proves that each valid observation trace agrees with the deterministic execution.
`execute_preserves` covers final states after successful outputs and drops.
These traces describe the model. They do not establish the accuracy of external observations.

`Netlib/Packet/Stateful.lean` puts the node, packet header, and complete store in each vertex.
Each graph edge requires physical adjacency and a processor result with an output packet.
`reachable_physical`, `isolated_of_physical`, and `mediated_of_physical` transfer the physical graph guarantees.
`invariant` transfers processor store invariants along successful forwarding paths.
`stateless_reachable_iff` connects stateless processors to the existing transfer graph and proves that their stores remain unchanged.
The graph alone does not account for all traffic or store updates between packets.
Ordered processor executions retain updates from calls that drop packets.

`Netlib/Packet/StatefulTrace.lean` connects each successful graph walk to its exact ordered processor calls.
`calls_length` records one call for each hop.
`walk_processor_trace` retains the walk's initial and final stores and observed packet outputs.
`walk_execute` proves agreement with deterministic execution of those calls.
`walk_calls_physical` preserves every hop's physical adjacency.
These results have one direction. They do not infer a graph walk from header observations alone.

`Netlib/Protocol/NATPipeline.lean` adapts the local NAPT model to processors.
`processor_roundtrip` restores an accepted outbound packet's reverse reply.
`tandem_roundtrip` composes two translations and reverses them in the opposite order.
`prefilter_denied_unchanged` proves that an earlier ACL denial prevents the NAT update.
`postfilter_drop_keeps_reply` proves that a later ACL denial retains the installed grant.
Its return-flow theorem therefore concerns a permitted outbound input, which need not have produced a final output packet.

`pipelineRefinement` and `pipeline_trace_state` connect shared-store executions to the underlying NAT state transitions.
They preserve store behavior, not equality between filtered outputs and raw NAT outputs.
`pipeline_safe` preserves mapping and grant invariants through those executions.
`pipeline_reply_origin` connects a restored reply to an earlier policy-permitted input.
These adapters do not establish native kernel processing order or execution behavior.

`Netlib/Examples/CampusNAT.lean` threads a separate NAPT store for each campus gateway.
`stores_safe`, `management_isolated`, and `gateway_mediated` lift the store and physical guarantees to packet paths.
`StoreSafe` states live deadlines and unique mapping keys.
It does not establish authorized provenance for arbitrary initial stores.
`denied_isolated` blocks client-to-server forwarding when the fixed session denies access.
`primary_roundtrip` constructs outbound and restored-reply paths with the exact primary store update.

`topology_without_grants_insufficient` combines surviving physical reachability with the absence of every stateful client output.
The standby gateway has no grants in that case.
`replicated_return_survives` constructs a return path under each admissible single internal-node fault when both stores contain the exact accepted outbound state.
`replicatePrimary` models an ideal copy made before the fault.
`replication_clock` requires synchronized clocks to preserve both recorded clock values.

Each path uses a static fault snapshot and fixed session and clock states.
The model assumes the shared public alias and suitable return routing.
These are existential permitted paths, not delivery or routing-convergence guarantees.
The example does not verify a replication protocol, delayed or stale copies, revocation, or packet freshness.
Its native implementation correspondence remains unproved.

## Observed flow traces and packet input

`Netlib/Check/NATTrace.lean` derives outbound permission from the certified packet-intent ACL.
Its parser rejects an input authorization flag.
The auditor advances the model independently of the observed output.
`Report.compliant_iff` states exact agreement for every supplied packet observation.
The report preserves the original event indices and order.
`Report.inbound_policy_origin` proves an earlier source flow permitted by the declared intent for every matched restored reply.

Accurate observations, complete event coverage, and clock interpretation remain assumptions.
The audit starts from the declared empty state.
Its default budget covers 100,000 policy partition cells.
It does not bound trace length, table size, or total execution time.

`Netlib/Import/PacketFields.lean` reads dotted IPv4 addresses and bounded numeric fields.
`Netlib/Import/TransferConfig.lean` reads explicit guards, rewrites, queries, and device references.
Input validation rejects unknown fields, duplicate declarations, and unsupported query forms.
The shared JSON parser rejects duplicate decoded keys.
Codec roundtrip and malformed-input tests supply implementation evidence.
These tests do not prove JSON parser or serializer correctness.

## Alias reuse and information loss

`Netlib/Theory/NATReuse.lean` proves an abstraction limit.
`translated_eq_iff` states exactly which flow fields source-alias translation retains.
Distinct inside endpoints can produce identical wire replies when their remote endpoint and protocol agree.
`header_only_indistinguishable` covers every deterministic decision using the same current state and packet header.
`cannot_reject_old_accept_new` and `cannot_recover_inside` rule out distinguishing those packets through that interface.

`retired_state` proves that an old flow expires completely before alias reuse.
`delayed_reply_restored_to_new` then delivers its delayed reply to the new inside endpoint.
`delayed_reply_not_original` separates that endpoint from the original recipient.
`safe_but_not_retired_reply_rejection` proves that the current safety invariant still holds.
Mapping consistency and authorized-flow provenance cannot establish packet freshness.
The result concerns the five-tuple abstraction, not full TCP packets or native kernels.

## Scope of the proofs

The proofs apply to the mathematical model. Reviewers must compare the model,
observation vocabulary, and source interpretation with the intended deployment.
Domain laws restrict abstract assignments only where network semantics justify
those laws.

Source citations and retained requirement text support review. They do not prove
that a translation preserves unrestricted natural language. Completion concerns
only supplied goals. It does not discover unstated security intent.

The examples do not certify an external standard or live equipment.
Packet transformations and flow state have the separate model scopes above.
Their native implementation correspondence remains unproved.
Cryptographic correctness and operational performance targets also remain unproved.
See the [specification](SPECIFICATION.md) for the complete scope.
