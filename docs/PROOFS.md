# Proof inventory and trust boundary

Run `lake build` locally to verify the Lean declarations. The library adds no
axioms and uses no `sorry` or `native_decide`. Tests in
`NetlibTest/Core/Reasoning.lean` use kernel reduction or the general theorems below.

## Native stateful failover

`Protocol.ConntrackReplication` selects a record from a valid source table and checks a collision-free install into another valid table.
Installation preserves both direction keys, supported NAT fields, inverse rewriting, seen-reply classification, and unrelated records.
Completeness holds for valid targets with both keys absent and a positive bounded timeout parameter.
Timeout remains metadata; the model does not evolve lifetimes.

`Protocol.StatefulFailover` separates cache staging, kernel commitment, each endpoint route change, and gateway fencing.
Every successful packet step uses its route owner, an unfenced gateway, and the current supplied pipeline.
Both gateway tables remain valid through accepted operations.

`Check.StatefulFailover` starts both tables and the cache empty.
Cache and commit provenance theorems identify an actual earlier staging event within the replay's actual preceding prefix.
They bind the staged record to that prefix's computed primary table and operation epoch.
Observed-output facts connect payload, TTL, ordinary NAT binding, and current policy to the actual accepted packet step.
Native evidence correspondence, aging, reliable replication, automatic detection, and convergence remain explicit open obligations.

## Safe handoff with outstanding assignments

`Protocol.TrackedFlow` derives ordinary attachment from any valid table containing the protected NAT binding.
The gateways can retain different seen-reply knowledge without changing that binding.
Selected packet processing completes and preserves readiness even when routing, TTL, or current policy prevents output.
The service theorem constructs an emission when routing, live TTL, and both current filter permits hold.
Its target, payload, checksum effects, and TTL decrement follow the existing wire semantics.

`Theory.Outstanding` allocates unique identities and completes an actual pending item by identity.
It permits arbitrary completion order without requiring equality of stored payloads.
Its invariants preserve exact membership, retirement history, and targeted counts.
An identity cannot complete twice.

`Protocol.SafeHandoff` separates route assignment from processing at the assigned gateway.
Lean uses `assign` and `serve`; JSON retains `admit` for assignment.
`Admissible` states operation conditions entirely on the preceding state.
`admissible_progress` constructs an actual successful step and proves preservation without assuming success or a safe result.
`arbitrary_interleavings` and `arbitrary_prefixes` cover every modeled admissible packet and control interleaving.
They preserve protected readiness, unfenced active gateways, ticket identities, and further admissible progress.
A current policy denial remains compatible with that structural invariant.

`serve_service` uses the assigned gateway's current configuration and local classification, including later seen-reply changes.
`drain_gateway` constructs a retirement sequence with exactly the initial outstanding target count.
`drain_then_fence` permits fencing after that drain and both endpoint route changes.
These are operation counts without time, fairness, delivery, or physical queue correspondence guarantees.

`Check.SafeHandoff.Report.every_served_source` identifies each served item's actual earlier assignment prefix.
It binds immutable bytes, identity, gateway, direction, and operation epoch to that prefix's computed state.
`observed_output_facts` transfers matched Ethernet output to that source's payload, TTL, NAT boundary, and current filter permits.
`commit_source` identifies the earlier actual primary-prefix stage behind the installed record.
Observations never replace ticket input or computed tables.

`Examples.SafeHandoffDeployment` connects service to a current certified EAP session policy under an explicit installation premise.
Its synthetic integration test covers Logoff, queued denial, and a stale installed-policy counterexample.
The native example records 20 operations, seven datagrams, and six protected tickets; it establishes no native EAP enforcement claim.
The [safe handoff guide](SAFE_HANDOFF.md) states the command, source pins, proof premises, and evidence limits.

## TCP byte and serial foundations

`Protocol.TCP.Segment` proves the two exact codec directions, offset and length bounds, and mandatory pseudoheader checksum validity.
The codec verifies checksum zero normally. Recomputation uses the actual complement.
`Protocol.TCP.Options` preserves unknown well-formed TLVs. Its option parser has positive progress.
MSS placement remains a separate predicate.

`Protocol.TCP.Seq` proves modular distances, translation invariance, asymmetry, and exact half-space incomparability.
Its transitivity and common-arc laws include explicit bounded-span premises.
The library has no global sequence ordering instance.
SYN and FIN accounting is separate from transport-state meaning.

`TCPRewrite.Certified` keeps the transport control fields and payload. It computes the two checksums again.
Its pure `FlowNAT` helper connects derived wire headers to the existing bidirectional tuple projection.
`TCP.Reassembly.Source` certifies the transport bytes of a supplied completed IPv4 packet.
Earlier fragment provenance remains a separate reassembly proof.
The [TCP guide](TCP.md) distinguishes these results from connection semantics and native implementation refinement.

## TCP receive projection

`TCP.ReceiveWindow` proves the exact four sequence tests, translation invariance, and explicit edge laws.
Its counterexample distinguishes first-or-last sequence acceptance from general interval overlap.
The segment adapter counts SYN and FIN positions and derives the occupied-length bound from codec validity.

`TCP.EstablishedReceive` proves the fixed ACK arc, bounded buffer changes, and exact payload append.
ACK advancement removes the acknowledged prefix and preserves `SND.NXT`.
An old ACK inside the permitted arc can accompany new data.
The NAT result preserves the receive decision for matching valid endpoint contexts after certified rewriting.
The checked replay retains source bytes and actual computed results through its processed prefix.
It stops at the first `Unsupported` result.

The caller supplies the pre-established seed and its assumed sent bytes.
The proofs do not establish a handshake, actual transmission history, ACK emission, or Linux conntrack acceptance.
The [receive-state guide](TCP_RECEIVE.md) states the bounds and remaining obligations.

## TCP application path

`TCP.Output` constructs checked IPv4/TCP packets from current endpoint fields.
It proves the reverse tuple, payload, cursors, advertised window, selected flags, and mandatory checksums.
`TCP.Endpoint` preserves state validity across writes, sends, reads, and peer-window updates.
A strictly old ACK cannot update the peer window.
A duplicate ACK at `SND.UNA` can update it when the freshness condition holds.
Window shrink preserves validity even when outstanding bytes exceed the new peer window.

`TCP.ApplicationTrace.Chain` proves byte conservation for actual computed events.
Its paired theorem connects earlier peer outputs, preserved sequence values, and bounded byte positions to the application prefix property.
The theorem requires delivery-history evidence and a finite epoch below half the sequence space.
Seed construction, native transmission, eventual delivery, and congestion control remain separate obligations.
The [application guide](TCP_APPLICATION.md) states the proof contract and command limits.

## Checked TCP startup

`TCP.ControlOutput` proves exact empty SYN, SYN,ACK, and ACK packets without an established-state premise.
`TCP.Handshake` separates pending SYN control positions from application byte buffers.
Its successful operations derive application cursors, windows, empty storage, and the default MSS from checked startup messages.

`TCP.HandshakeExchange.Complete` retains actual successful operation equations, exact selected byte paths, and strictly ordered event times.
It derives complementary cursors and valid endpoint states without caller-supplied seed or cursor proofs.
Its application theorem connects these states to the paired application prefix result.
Supported continuation, future delivery history, bounded epochs, a quiet boundary, and current-instance conditions remain explicit assumptions.

`Check.TCPHandshake.Report` retains the actual computed prefix, exact event indices, and the unprocessed suffix.
A passive seed is absent before final ACK receipt.
The [startup guide](TCP_HANDSHAKE.md) states the selected interpretation and remaining protocol obligations.

## Authenticated campus TCP path

`Protocol.WireSource` shares checked immutable byte sources across UDP and TCP.
The existing UDP handoff remains a specialization with its original replication restriction.
`TCP.WireForwarding` uses the common lifecycle pipeline and constructs output from the actual selected tuple and decremented TTL.
Its proofs retain NAT, route, forward-filter, late-filter, payload, and mandatory checksum facts.

`TCP.Admission` derives a bounded ordinary TCP history from checked segments and the actual lifecycle attachment.
It proves control positions, data and ACK bounds, and window-history comparison ages.
Commit retains observed progress against the actual confirmed table.
A dropped existing reply can retain progress; an unconfirmed fresh drop leaves no confirmed history.

`Check.CampusTCPService` compares actual stored ingress and forward policy with the current consumed authentication prefix.
For compliant services, its output facts derive credential validity, method readiness, and the current ingress attachment.
Denial prevents new output without deleting the cached NAT entry or earlier receive storage.
Stale allow rules retain their actual computation and fail comparison.

`CampusTCPModel` records actual endpoint, assignment, service, and receipt operations.
`CampusTCPOrigins` and `CampusTCPFacts` derive the causal references and delivery history used by the application theorem.
Their service facts connect compliant output to the declared primary campus path and modeled management isolation.
The concrete trace has nonempty application reads through the same gateway as startup.
The [campus TCP guide](CAMPUS_TCP.md) states the selected model and remaining deployment assumptions.

## Admission around reassembly

`Packet.IPv4Envelope` projects validated IPv4 fragments without transport selectors.
`IngressPolicy.NoPorts` records a syntactic requirement, separately from complete-header equivalence.
The coarse attachment compiler certifies that requirement and derives current validity and exact live ingress for every admitted application envelope.

`Protocol.IPv4ReassemblySourcesBy` propagates source predicates through the actual user/vif queue domain.
`Protocol.FragmentAdmission` composes installed early decisions, actual reassembly, installed full-datagram decisions, and ordinary MTU forwarding.
Early rejection preserves queues and tracking; fine rejection preserves tracking after the computed reassembly change.
`Accepted.output_bound_receipt` supplies matching admitted-byte provenance in the correct namespace and domain, with a timestamp bounded by completion.
It does not promise unique attribution among identical duplicate occurrences.

Active-only residency preserves archives and excludes later operations after retirement.
Session residency requires a fresh namespace lifetime when the authentication round changes.
Current coarse and full-datagram permission have separate checker theorems.
The [fragment admission guide](FRAGMENT_ADMISSION.md) states the formal contracts and open runtime integration.

## Interface-bound current sessions

`Packet.IngressPolicy.check_correct` proves complete equivalence across every numeric interface index and header.
`Import.NftablesIngress.Snapshot.compile_evaluate` connects imported source-rule evaluation to that policy.
Current name resolution preserves numeric `iif` semantics; namespace and interface births remain separate controller evidence.

`Protocol.IngressAttachment` records actual session origins and current attachment validity.
`Compile.IngressAttachment.actual_application_permission` derives current application validity, EAP readiness, exact ingress, and the configured principal.
Its premises include live unique interfaces, namespace agreement, policy equivalence, and maintenance/application disjointness.
The compiler also proves rejection at every unmentioned numeric index.

`Protocol.GuardedHandoff.Dropped.tables_unchanged` proves exact modeled table preservation on early rejection.
Retirement preserves immutable ticket provenance and exact outstanding counts.
Its completeness theorem starts from a safe preceding state and a pending identity.
`Protocol.IngressProbe` supplies actual ordinary processing outside the route-ticket stream.
Protected completeness follows from the preceding ready binding and unfenced gateway.
Probes preserve route work and archived primary state.

`Check.AttachmentCampus.PacketCheck.application_origin` connects a permitted application execution to current permission and its actual historical EAP prefix.
`wrong_ingress_rejected` excludes application packets whose live ingress differs from every staged attachment under the same checked policy premises.
Replay provenance checks bind every stored source state to the authentication computation at that prefix.
`Report.finding_prefix` identifies each finding's actual preceding replay state.
Each historical owner must cite a staged origin and an actual table entry.
Replication inherits that origin from the selected source record and checked installed table.
The [ingress attachment guide](INGRESS_ATTACHMENTS.md) records observation scope and remaining trust assumptions.

## Joint campus session and withdrawal

`Examples.CampusDuplex` adds request and reply continuity under endpoint-safe single internal-node faults.
Current application permission holds exactly when both directions remain reachable in the enforced graph.
Management isolation and mandatory gateway traversal hold in both application directions.
`Examples.CampusDirect` interprets the direct wired data roles without inferring physical access points.
Its stuttering refinement collapses abstract access-point vertices to the client role.
Its expansion simulates each direct edge by an existing campus path.

`Protocol.CampusWithdrawal` extends the handoff contract with a separate physical-withdrawal phase.
Withdrawal requires both routes at standby, no outstanding primary work, and a primary fence.
The retained primary table becomes historical archive data.
Subsequent operations preserve that archive and permit no live primary processing or control.
Progress follows from conditions on the preceding state, including after withdrawal.
The actual pending tickets remain assigned to the standby.
Current session permission supplies their paths in both interpretations.

`Check.SessionInstallation.Checked.forward_equivalent` derives policy equivalence from the actual source configuration and a successful current-prefix comparison.
It checks configuration identity, compiled rules, fallback, hook context, and decisions for every modeled state and header.
The joint checker requires those certificates rather than a caller-supplied equivalence hypothesis.
Installations persist across authentication changes, so a stale installed permit cannot inherit a later session certificate.

`Check.CampusDeployment.Report.prefix_counts` identifies each finding's actual preceding replay prefix.
Its authentication and network counters equal the corresponding prior payload counts.
`served_source` identifies the served ticket's actual earlier assignment within that same joint timeline.
`observed_output_nat_facts` proves exact captured NAT headers, payload preservation, and one TTL decrement from that retained source.
It also supplies current application validity, method readiness, and duplex graph reachability at the actual consumed authentication prefix.
`denied_output_none` excludes emission when the current application denies access.
`forward_iff_duplex` connects the certified forward decision to duplex reachability under an explicit covered-header premise.
`CheckedReport.served_class_route` derives actual served-header coverage and the selected endpoint route from compliance.
`CheckedReport.served_forward_iff_duplex` uses that derived coverage without another caller premise.

The checked report additionally requires full observation consumption, actual withdrawal, application-class coverage even for drops, and selected next-hop role agreement.
These are finite replay checks alongside the reusable interleaving and topology theorems.
The native example records 26 operations, eight datagrams, and seven protected tickets.
Its joint model timeline has 21 authentication operations, 23 network operations, and one withdrawal.
The [campus deployment guide](CAMPUS_DEPLOYMENT.md) separates these results from cryptography, wireless deployment, anti-spoofing, physical correspondence, and automatic recovery obligations.

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
The stateless nftables deployment adapter rejects native NAT and connection-tracking expressions.
These local models do not prove Linux behavior or complete RFC conformance.

## Visible conntrack tuples and status-aware translation

`Netlib/Protocol/FlowNAT.lean` models original and reply tuples in one implicit namespace.
Both directional lookup keys include their effective zone and complete packet header.
`Snapshot.check_correct` and `validate_ok_iff` connect validation to bounded TCP/UDP fields and unique combined keys.
The uniqueness check includes collisions between one entry's original key and another entry's reply key.
Different remote peers can share a public endpoint when those complete keys remain distinct.

`lookup_sound`, `lookup_unique`, and `lookup_complete` establish exact lookup over a valid supplied snapshot.
`translate_sound` identifies the source entry and direction of every projected output.
`roundtrip` and `reverse_roundtrip` prove the two directional tuple inversions.
The original tuple projects to the reversed reply tuple; the reply tuple projects to the reversed original tuple.
Remaining timeout seconds are recorded evidence, including zero.
This frozen model has no clock advancement, timeout refresh, allocation, or packet-admission transition.
A lookup miss means no association in the supplied table.

`Netlib/Protocol/NetfilterNAT.lean` selects endpoint rewrites using source/destination NAT flags.
Reply processing reverses those selections.
`Entry.Compatible` requires unchanged endpoint values where the corresponding NAT flag is absent.
`Entry.rewrite_correct` proves equality with the tuple projection under that checked condition.
`no_nat_identity` proves that two absent NAT flags leave every packet unchanged.
These are Lean tuple-algebra results informed by upstream Linux v6.8 source.
They do not prove refinement of kernel C code or execution of individual hooks.

`Netlib/Import/Conntrack.lean` imports the supported conntrack-tools 1.4.9 / libnetfilter_conntrack 1.1.1 XML slice.
It preserves tuples, metadata, source spans, and original records.
XML omits the complete status mask, so its tuples cannot establish native NAT activation.
Marker presence remains evidence rather than inferred permission or complete status.

`Netlib/Import/ConntrackNetlink.lean` imports the collector's full-status JSON records.
Its supported status requires confirmation and rejects expected, sequence-adjustment, dying, template, NAT-clash, explicit-helper, and offload bits.
Unknown bits above the supported 16-bit mask also cause rejection.
Enabled source/destination NAT requires the corresponding initialization bit.
`SourceEntry.rewrite_correct` connects accepted tuple/status conditions to the status-aware rewrite theorem.
The explicit-helper bit does not detect every automatically assigned helper extension.
Such metadata can remain only in opaque raw evidence; helper payload behavior lies outside these proofs.

The Python collector checks matching request sequence, port, kernel sender, framing, multipart completion, and resource limits.
It accepts the fixed IPv4 request's family-filter flag and rejects interrupted or lost dumps.
It retains raw messages, unknown attributes, and nullable optional metadata.
The Lean importer checks hexadecimal syntax but does not decode those bytes or prove agreement with the structured fields.
Collector decoding, capture identity, and observation accuracy remain trust boundaries.
Visible dumps can omit transient clash entries and do not establish complete kernel state or an atomic history.

`Netlib/Check/Conntrack.lean` checks each reported original tuple against a certified packet-intent policy.
`Report.covered` retains every supplied row in order.
`Report.compliant_iff` proves that a passing report means every reported original tuple satisfies that intent.
This applies to supported XML and full-status JSON inputs.
It does not establish historical firewall admission or authorization of restored replies.
The separate mapping command reports only a frozen full-status tuple association.

The retained [native capture](../examples/conntrack/native) contains four flows and six successful socket round trips.
It uses kernel `6.8.0-117-generic`; upstream v6.8 source is a reference, not a proved identity with that Ubuntu kernel.
Raw-message decoding agrees with the structured fields and the XML tuple/ID projection.
TCP and UDP each share one public endpoint across two remote peers.
Recorded server wire and client restored headers agree with the tuple algebra.
Reply tuples in `packets.json` are derived by reversing the server wire tuple.
They are not independent captures of reply IP headers before NAT.
The collision and late-drop attempts are finite observations, not universal kernel guarantees.

## Stateful filters and fixed NAT compilation

`Netlib/Packet/StatefulACL.lean` adds an optional connection-state selection to each ordered header rule.
`Rule.accepts_iff` connects Boolean evaluation to the independent `Rule.Matches` predicate.
`Policy.lookup_eq_some_iff` and `default_deny_iff` retain first-match semantics.
`lookup_specialize`, `evaluate_specialize`, and `allows_specialize` prove that fixing one state gives an equivalent ordinary ACL.
`allows_ofACL` and `evaluate_eq_of_unguarded` recover the original stateless behavior.
These results consume a supplied state label; they do not classify native packets.

`Netlib/Import/NftablesSyntax.lean` shares the pinned envelope and header-match decoder.
The original `Import.Nftables` adapter remains stateless and forward-only.
It continues to reject connection-state predicates and NAT statements.
The separate `Import.NftablesStateful` profile retains header and state expression indices, handles, and source IDs.
`SourceRule.compile_accepts` preserves each structured source match.
`Snapshot.compile_evaluate` and `compile_allows` preserve the entire ordered chain and explicit policy for every state and header.
Parser tests check symbolic and numeric state forms, rejected expressions, and the unchanged stateless subset.
They do not prove JSON decoding or native execution.

`Netlib/Import/NftablesNAT.lean` represents fixed endpoint targets in separate destination and source chains.
`SourceRule.compile_accepts`, `compile_translate`, and `compile_rules` connect compiled rules to independent structured source evaluation.
`Snapshot.destination_correct` and `source_correct` preserve the first matching target at each stage.
A matching identity target still stops the chain; a miss preserves the incoming header.
`candidate_original`, `candidate_reply`, and `candidate_output` define the resulting tuple proposal.
`candidate_compatible` proves compatibility under the stated protocol, zone, and direction-key conditions.
The proposal does not establish allocation, port preservation by a native allocator, or successful confirmation.

## Ordinary forwarded-packet lifecycle

`Netlib/Protocol/ConntrackLifecycle.lean` attaches one tuple before the modeled hooks.
It separates a fresh unconfirmed candidate from a confirmed record.
Processing applies destination NAT, longest-prefix destination routing, the forward filter, source NAT, and the late filter.
A fresh candidate reaches ordinary confirmation only after these stages permit it.
Confirmation rejects combined-key collisions.
Intermediate headers retain the original attachment; they do not trigger another lookup.

| Declaration | Guarantee |
| --- | --- |
| `State.check_correct`, `State.markReply_valid` | Validation and seen-reply updates preserve compatible entries and unique combined tuple keys. |
| `prepare_model` | Attachment and seen-reply updates preserve the stored tuple table. |
| `stages_correct`, `step_output` | A forwarded exact input produces the stored flow's complete boundary output. |
| `step_filters` | A forwarded result has a selected route and passes the forward filter after destination NAT and the late filter after source NAT. |
| `step_forwarded_iff` | An output exists exactly for a forwarded disposition. |
| `step_fresh_drop` | A fresh route, forward, or late drop leaves the confirmed state unchanged. |
| `step_reply_state` | An existing reply is established and marks seen-reply even when a later stage drops it. |
| `step_existing_original` | An existing original retains its stored binding and is new or established according to the prior seen-reply flag. |
| `run_trace`, `run_valid` | Ordered calls agree with model transitions and preserve structural table validity. |

An unreplied existing original remains `new` while its attachment has `fresh = false`.
The model therefore reuses its binding after NAT rules change.
`established_first_permits` proves the effect of a leading established permit.
The lifecycle tests combine it with a dropped first reply to show later original traffic passing a policy that denies new traffic.
Deleting the entry makes that original a fresh lookup and exposes it to the new-flow denial.
Structural table validity does not establish policy authorization or transport handshakes.

`Netlib/Protocol/ConntrackOperations.lean` adds explicit deletion and policy selection for each packet call.
`State.erase_valid` preserves table validity; `erase_lookup` removes the selected association's lookup result.
Both direction keys disappear together.
`Operations.ExecutionTrace` binds every returned result to its exact operation and preceding state.
`ExecutionTrace.toTransition` transfers this trace to the generic transition relation.
`Operations.invariant` and `Execution.final_valid` preserve structural validity through packet calls and deletions.

`Netlib/Check/ConntrackLifecycle.lean` derives fresh proposals from the selected parsed NAT table.
`Event.existing_binding` excludes candidate regeneration on every lookup hit, including an unreplied `new` original.
`Event.fresh_candidate` identifies the source of each proposal on a miss.
Observations never advance the model.
`Report.covered` preserves every supplied event and its order.
`Report.compliant_iff` proves exact agreement with all supplied packet fields and table observations along the modeled operations.
`ReplayTrace` binds each finding's actual result to its dynamic preceding state.
`Report.prefixes_valid` covers the final table and every reported prefix.

`sameRecords_correct` proves mutual record membership after timeout normalization.
Comparison keeps both tuples, zones, NAT flags, and seen-reply.
It ignores timeout seconds, native IDs, marks, use counts, record order, and other supported status metadata.
Raw records and source metadata remain retained evidence.
A null event state means no table observation; a null initial state declares an empty initial table.
Mismatch produces a noncompliant report, while unsupported input or model errors produce no report.
The audited proof dependencies use only standard Lean foundations.

The retained lifecycle experiment contains nine UDP packets, 30 traced chain visits, and eight table snapshots.
The replay matches all ten operations, including one explicit deletion.
The independent evidence verifier checks the retained native traces, raw messages, and socket observations.
The [lifecycle guide](LIFECYCLE.md) records the pinned producers and capture recipe.
This is finite native evidence, not a formal refinement of kernel C or a full TCP lifecycle validation.

The input domain requires valid unfragmented IPv4 TCP/UDP packets whose transport tracker accepts the modeled attachment.
TCP reopen, replacement, and `NF_REPEAT` are excluded.
So are expiry, concurrent changes, helpers, related traffic, offload, hidden clash objects, and race or allocator recovery.
Routing and the exclusive NAT/filter hook sequence must match the supplied stable context.
Selected traffic must have faithful observations and complete event coverage.
The proofs do not establish those assumptions or physical delivery.

## Static stateful filter refinement

`Netlib/Check/StatefulRefinement.lean` compares all five labels: new, established, related, invalid, and untracked.
For each label, `rules_allows` connects ACL specialization to the structured source chain.
Exact header partitions then cover every modeled header.
`check_correct` proves permission inclusion for every state/header context.
`sameContext_iff` characterizes the equal-hook and equal-priority check used by the budgeted command.
`checkBudget_correct` gives the same meaning to each completed result.
The default budget is 100,000 cells, summed across all five states.
Exhaustion or a context mismatch returns an error without a refinement answer.

`counterexample_sound` proves that each returned state/header context is permitted by the proposed stronger filter and denied by the weaker filter.
`counterexample_none_iff` connects absence of a counterexample to universal permission inclusion.
These contexts need not be reachable in a native packet history.
The comparison does not cover routes, NAT allocation, stored bindings, revocation, or a whole-network upgrade contract.
In particular, static inclusion does not prove that a policy update removes old flows.

## Operational output exclusion

`Netlib/Check/StatefulExclusion.lean` defines `Blocks` over a native stateful filter and a forbidden header class.
`check_correct` covers every modeled state label and selected header.
The exact partition includes both policy and selection boundaries.
`counterexample_sound` supplies a selected header that the chain permits.
`counterexample_none_iff` proves completeness.
`checkBudget_correct` retains that meaning for a completed budgeted check.
`checkBudget_context` requires a postrouting priority strictly between source NAT and confirmation.

`Netlib/Protocol/Revocation.lean` defines output exclusion and a late-filter barrier.
`step_output_property` transfers any property of late-filter-permitted headers to every forwarded output.
`step_output_excluded` specializes this result to the forbidden class.
It covers arbitrary compatible stored bindings, original and reply directions, and fresh attachments.
It does not require state deletion.

`Operations.ExecutionTrace.excludes` transfers the barrier through ordered packet and deletion operations.
`ExecutionTrace.drop` retains the intermediate state reached before the suffix.
`suffix_excludes` covers the selected suffix.
`excludes_of_upgrade` connects the guarantee to `Network.Upgrade.Preserves` when every packet pipeline comes from a certified upgrade snapshot.
It does not implement the update commands or establish a physical packet-drain boundary.

`Netlib/Check/ConntrackRevocation.lean` specializes the contract to imported replay configurations.
`blocksFrom_correct` certifies every packet configuration in a suffix selected by list position.
`Report.model_outputs_excluded` excludes selected modeled outputs without requiring observation agreement.
`Report.observed_outputs_excluded` also requires a compliant report and covers every supplied output observation in that suffix.
The complete replay computes the cutover state; observations never replace it.

The CLI requires a nonempty suffix with at least one packet.
It checks the aggregate partition budget before certificate searches.
A failure can identify an unsafe state/header context absent from the supplied packet history.
The [output exclusion guide](REVOCATION.md) records the exact scope.
Translated header selection, effective barrier installation, complete interval coverage, hook traversal, and packets already beyond the hook remain deployment obligations.

## Buffered cutovers and FIFO drain

`Netlib/Theory/QueueDrain.lean` tracks a finite old prefix independently of later arrivals.
`run_tail_bound` bounds the remaining old prefix by the initial bound minus total declared service capacity.
`run_pending_clean` establishes a clean pending queue once capacity covers the initial backlog and all new arrivals are clean.
`served_after_prefix` excludes unclean packets from later service.
The last draining batch and earlier delivered history remain outside that conclusion.

The result permits arrivals that exceed service.
The total queue can remain nonempty and grow while the old prefix clears.
`pending_after_old_prefix` gives the exact remaining arrival suffix after sufficient service.
The served-capacity bounds distinguish declared opportunities from actual delivered packet counts.
`minCapacity_totalCapacity` supplies a lower capacity bound from a per-tick premise.
Physical time needs a separate service interpretation.

`Netlib/Protocol/BufferedLifecycle.lean` interleaves tracked operations with FIFO service.
`step_operation` enqueues only the computed optional output and serves nothing.
`step_serve` leaves tracking unchanged and removes the exact FIFO prefix allowed by its capacity.
`Trace.operations` preserves the exact tracked-operation execution while erasing service events.
`Trace.queue_run`, `Trace.delivered`, and `Trace.conservation` connect the full execution to queue semantics.
`Trace.split` retains actual intermediate states and aligned event/result lists.
`Trace.clean_after_budget` connects certified late barriers to clean service after the draining segment.

`Netlib/Check/BufferedReplay.lean` consumes every embedded lifecycle event exactly once and in order.
`Report.compliant_iff` establishes agreement with all operation, pending-queue, and served-batch observations.
The model state advances independently of those observations.
The replay trace binds each dynamically compiled operation to its source and actual incoming state.

`Netlib/Check/BufferedDrain.lean` selects separate admission and delivery boundaries by list position.
`Report.ready_correct` certifies barrier retention, boundary order, and sufficient capacity for the computed cutover backlog.
`pending_clean_of_ready` establishes a clean pending queue even when the delivery boundary is the end of the schedule.
`model_served_excluded` covers later modeled service without requiring observation agreement.
`observed_served_excluded` also requires a compliant report.
`continuation_served_excluded` covers arbitrary later modeled executions that retain the barrier.

The [buffering guide](BUFFERING.md) states the input format, native delayed-delivery evidence, and correspondence assumptions.
Queue counts alone do not identify packets or establish a general FIFO, native liveness, or a wall-clock drain bound.

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

## EAP framing, authentication, and campus admission

`Netlib/Protocol/EAP.lean` defines the RFC 3748 base packet header and opaque method payloads.
`decode_encode` and `decode_encodeDecoded` preserve encoded packets and padding.
`encode_decode` reconstructs arbitrary accepted packet bytes exactly.
Declared terminal data and truncated lengths are rejected.
Bytes beyond the declared length remain preserved padding.

`Netlib/Import/EAPOL.lean` adds the selected EAPOL and untagged Ethernet formats.
`decode_encodeDecoded` and `decodeEthernet_encodeEthernet` preserve structured encodings.
`encode_decode` and `encodeEthernet_decodeEthernet` reconstruct every accepted binary frame.
The text hex and MAC parsers have tests without general parser proofs.
Unsupported versions, packet types, and encapsulations produce errors.

`Netlib/Protocol/EAPAuth.lean` keeps method evidence separate from packet Success.
`step_safe`, `run_safe`, and `trace_safe` preserve authorization's current evidence and message-correlation requirements.
`authorized_evidence` provides an accepted result for the current round, expected subject, and selected method.
`authorized_response` provides the matching Request, Response, and terminal identifier.
`authorized_not_identity` excludes a control Identity exchange as the selected authentication method.
Wrong responses and terminal identifiers remain ignored.
Duplicate requests and responses preserve state.
Reset and stale-evidence theorems cover the local failclosed policy.

`Netlib/Protocol/EAPSession.lean` derives session authentication from that guarded state.
Its application event type has no direct authenticate operation.
`step_safe` and `run_safe` preserve the session guard and its coupling to current EAP authorization.
`synchronize_resets` clears credentials and admissions after round or authorization changes.
`admitted_valid` combines the full credential guard with current method readiness.
`run_session_trace` supplies a corresponding session execution, including internal authentication updates.

`Netlib/Check/EAP.lean` maps decoded Ethernet roles to protocol events.
`Report.compliant_iff` covers every supplied authorization and request observation in order.
`observed_authorization_ready` transfers observed authorization to current method readiness.
`observed_admission_valid` adds the complete current credential guard for observed application admission.
Observations never replace the computed state.

`Netlib/Examples/CampusEAP.lean` composes the bridge with the original campus context and upgrade contract.
`Netlib/Examples/EAPDeployment.lean` uses a configurable principal and the actual report context.
`observed_admission_available` connects a compliant recorded application admission to current method readiness, a valid credential, and campus availability under each admitted internal-node fault.
`without_credential_isolated` retains application isolation at an authenticated native checkpoint that lacks an application credential.
Management isolation and gateway mediation reuse the campus topology guarantees.

Native EAP-TLS observations and producer logs supply finite evidence rather than TLS cryptographic proofs.
Certificate policy, method freshness, round attribution, clock meaning, physical enforcement, and complete wireless behavior remain assumptions.
The [EAP guide](EAP.md) records the source clauses, selected profile, native evidence, and input schema.

## Session-derived firewall enforcement

`Netlib/Compile/SessionFirewall.lean` derives unordered packet requirements from current scope guards.
`Certified.permits_iff` gives exact selected-class permission.
`permitted_valid` supplies the current complete credential guard and EAP readiness.
`denied_requirement` excludes every header in each denied requirement.
`statefulSnapshot_permits` preserves the generated policy for every conntrack state.
Existing conflict certificates reject incompatible scope mappings with a header witness.

`Netlib/Check/SessionFirewall.lean` computes each checkpoint from its authentication-event prefix.
`Finding.correct` equates successful bidirectional comparison with exact native state/header equivalence.
`Report.permitted_valid` transfers native permission to current authentication and credentials.
The report covers every supplied snapshot and checks the generated hook and priority.
Its total partition budget includes source compilation and both comparison directions.

`Netlib/Examples/SessionFirewallDeployment.lean` uses actual lifecycle output and its post-DNAT forward header.
`output_current_permission` supplies a selected valid scope and current method readiness.
`output_matching_scope_valid` establishes validity for each matching requirement.
`postlogoff_output_none`, `postclose_output_none`, and `postrevoke_output_none` exclude output for arbitrary cached tables with current policy installed.
Buffered results cover new admissions and retain the distinction from earlier queued deliveries.

The [session firewall guide](SESSION_FIREWALL.md) defines the native evidence and trusted installation, identity-binding, and cryptographic assumptions.

## IPv4 and UDP wire semantics

`Netlib/Protocol/InternetChecksum.lean` defines network-order word pairing, odd padding, and one's-complement normalization.
`fold_endAround` connects normalization to end-around carry.
`synthesize_valid` proves checksum insertion after every aligned prefix and arbitrary payload.
`synthesize_nonzero_valid` proves UDP's computed-zero remapping.
The arithmetic retains both zero representations.

`Netlib/Protocol/IPv4.lean` validates the selected header, total length, flags, and checksum.
`decode_encode` verifies canonical packet encodings.
`decode_encodeDecoded` verifies preserved checksum and padding encodings.
`encode_decode` reconstructs every accepted byte sequence exactly.
`decode_valid` supplies bounded packet and checksum conditions.

`Netlib/Protocol/UDP.lean` checks the pseudoheader against actual decoded addresses, protocol, ports, length, and payload.
`computed_valid` and `computed_nonzero` establish checksum synthesis.
`decode_checksum` separates omission from validation; `decode_verified` requires a present checksum.
The standalone and composed IPv4 codecs have both roundtrip directions.

`Netlib/Import/EthernetIPv4.lean` preserves untagged capture headers and all payload bytes.
`Netlib/Check/Wire.lean` packages decode equations, exact reconstruction, header projections, and present-checksum verification.
JSON cannot substitute a supplied packet header for the decoded bytes.

`Netlib/Examples/WireSessionDeployment.lean` connects decoded bytes and transport payload to checked native session policy and lifecycle output.
`checked_output_current_permission` supplies a matching valid scope and current method readiness at the declared forward stage.
`checked_matching_scope_valid` applies to each matching requirement.
These proofs retain the current-installation and identity-binding assumptions.
These original header-level results leave payload forwarding and TTL updates to the separate extension below.
Neither layer establishes cryptographic integrity.

The [wire guide](WIRE.md) defines the profile and native capture limits.

## Payload-preserving NAT and TTL forwarding

`Netlib/Protocol/UDPRewrite.lean` constructs translated IPv4 UDP bytes from a validated decoded input and a target tuple.
`SourceValid` requires coherent UDP fields, bounded IPv4 length, and a valid received IPv4 checksum.
`transformed_encoded` proves encoding succeeds before the forwarding wrapper uses the total `rewrite` constructor.
This prevents a later codec failure after modeled confirmation.

`Certified.decoded` proves the generated bytes decode to the reported packet.
`header`, `payload`, `ttl`, `metadata`, and `length` establish the selected tuple, exact payload, chosen TTL, preserved metadata, and unchanged IP length.
`bytes_length` excludes unexplained bytes from the emitted datagram.
The emitted datagram has no link padding.
`checksum_omitted_iff` preserves UDP omission exactly.
Present UDP checksums cover the translated pseudoheader and unchanged payload.
Synthesis maps a computed zero to 65535.
`ipv4_checksum` proves validity of the canonical IPv4 checksum.

`Netlib/Protocol/WireForwarding.lean` attaches tracking once, applies destination NAT, and selects a route before checking TTL.
A routed packet with TTL zero or one produces no selected UDP output.
It does not reach forward filtering, source NAT, late filtering, or fresh confirmation.
`ttlExpired_fresh` preserves the confirmed table after a fresh expiry.
`ttlExpired_reply` retains the reply's earlier seen-reply update despite expiry.
`ttlExpired_model` preserves the tuple-table projection.

`step_output` connects every emission to the existing lifecycle step and proves the incoming TTL exceeds one.
`step_filters` supplies the current forward and late decisions and the selected route.
`step_lifecycle` refines successful longer-TTL execution, including filter drops.
`step_completes` establishes completion under its validated-input, attachment, and successful lifecycle hypotheses.
Emission theorems prove exact payload preservation, TTL decrement, metadata preservation, and checksum validity.

`Netlib/Check/WireForwarding.lean` uses byte-derived packets and the existing configuration adapters.
The shared public parsers retain the earlier lifecycle adapter semantics.
`Trace.steps` binds each finding to its actual preceding model state and operation.
`Trace.valid` preserves structural table validity for every finding and the final table.
`Report.compliant_iff` states agreement with every supplied observation in order.
`Report.observed_output_payload` transfers compliant observed output to exact input-payload equality and TTL decrement.
Observed bytes never replace modeled state or select a candidate.

Output comparison covers decoded IP fields and the complete UDP datagram.
IPv4 checksums and present UDP checksums are validated in both observed and generated packets.
Ethernet adjacency, link padding, and the IPv4 checksum's zero representation remain outside that equality.
Null intermediate fields remain unobserved.
Null output asserts no selected UDP egress within the declared complete observation scope.

`Netlib/Examples/WireNATDeployment.lean` constructs forwarding input from the checked capture packet.
`output_current_permission` combines emitted-byte properties with a valid scope and current EAP readiness.
`checked_output_current_permission` obtains that guard from the checked native session snapshot.
The scope match uses the computed post-destination-NAT header.
No separate supplied header can replace the decoded tuple.
`postlogoff_output_none` excludes emissions from arbitrary cached tables when the current deny policy is installed.

The native capture retains 17 IP frames: 14 UDP frames and three ICMP frames.
It covers four EAP admission stages, an expired cached reply, a later delivered reply, targeted deletion, TTL boundaries, and UDP omission.
These finite observations support the selected behavior without proving kernel C refinement.
MTU handling, ICMP generation, fragmentation, full transport behavior, concurrency, principal-to-tuple binding, and global installation timing remain separate obligations.
The [wire forwarding guide](WIRE_FORWARDING.md) defines the replay and native evidence scope.

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

## Effective MTU and output fragments

`Netlib/Protocol/IPv4Fragment.lean` proves both codec round trips for arbitrary accepted IHL-five fragment bytes.
It validates reserved flags, DF consistency, MF alignment, bounds, and header checksums.
Received checksum representation and trailing padding are preserved.

`Netlib/Protocol/IPv4Fragmentation.lean` proves contiguous aligned layouts and exact whole-IP-payload recovery.
Every generated fragment fits the validated effective MTU.
The total certificate prevents encoding failure after confirmation.
Strict reassembly rejects inconsistent metadata, gaps, overlaps, duplicates, and incomplete families.
`Certified.reassembled_perm` proves exact packet recovery for every permutation of the generated family.

`Netlib/Protocol/MTUForwarding.lean` reuses one conntrack preparation and one lifecycle execution.
Route failure precedes TTL expiry, which precedes oversized-DF rejection.
DF rejection preserves prepared state and prevents fresh confirmation.
Permitted translated packets are fragmented after successful confirmation.
Emission facts preserve the full UDP datagram, translated tuple, metadata, and decremented TTL.

`Netlib/Check/IPv4Fragments.lean` checks Ethernet fragments, strict reassembly, and subsequent UDP decoding.
`Netlib/Check/MTUForwarding.lean` compares complete normalized families and their recovered datagrams.
`Report.observed_output_payload` connects observed recovery to the exact input payload and TTL decrement.
`Report.observed_fragments_fit` bounds every observed part by its actual emission's selected MTU.

`Netlib/Check/Replay.lean` supplies the shared execution certificate for both forwarding checkers.
`Report.compliant_iff` characterizes ordered agreement.
`Trace.invariant` preserves any supplied state invariant at every prefix.
Mismatching observations never overwrite computed state.

`Netlib/Examples/MTUDeployment.lean` composes fragment facts with current scope permission and EAP readiness.
Its Logoff theorem excludes output families through arbitrary cached records under the current policy.
The native capture supplies independent socket reassembly, fragment bytes, MTU readbacks, hook observations, and table dumps.

ICMP generation, input reassembly, resource failures, concurrency, kernel refinement, and physical deployment correspondence remain open.
The [MTU guide](MTU.md) records the selected profile and effective-MTU assumption.

## Generated ICMP errors and quotation NAT

`Netlib/Protocol/ChecksumRewrite.lean` proves modular incremental checksum updates with explicit UDP omission preservation.
Universal inverse, identity, and composition results cover arbitrary changed-word totals.
Aligned-byte and full UDP results prove checksum validity for both odd and even payloads.

`Netlib/Protocol/IPv4Quote.lean` preserves original declared lengths while accepting a shorter quoted UDP prefix.
Its generic round trips reconstruct accepted bytes, and source construction proves exact prefix selection.
`Netlib/Protocol/ICMP.lean` supplies exact supported error-message codecs and whole-message checksum validity.

`Netlib/Protocol/ICMPNAT.lean` changes the quoted tuple and adjusts the transport checksum without requiring missing payload bytes.
It preserves quoted application bytes, declared length, metadata, and checksum omission.
Round-trip translation restores the exact quoted packet, including the UDP checksum.
Only the validated IPv4 checksum zero representation can differ.

`Netlib/Protocol/ICMPForwarding.lean` derives TTL and DF errors from actual MTU forwarding.
It checks eligibility, chooses a return path, and applies related output and late filters.
The effective return MTU bounds the quote and outer packet independently of the reported forward MTU.

`Netlib/Protocol/ICMPForwardingFacts.lean` proves necessary and sufficient generation guards.
Actual accepted steps bind the error to the same prepared NAT attachment.
The intermediate translated quote is a prefix of a complete accepted UDP datagram.
The final quotation restores the input packet prefix through incremental inverse NAT.
Fresh errors retain no confirmed candidate; cached records and earlier reply updates retain their established effects.

`Netlib/Check/ICMPError.lean` packages raw decoding, reconstruction, and the conditional complete-UDP checksum guarantee.
Partial quotations make no full transport-checksum claim.
`Netlib/Check/ICMPForwarding.lean` reuses the MTU observations and shared replay certificate.
`Report.observed_quote` connects each compliant observed error to its actual emission, source prefix, and generation facts.

`Netlib/Examples/ICMPDeployment.lean` preserves current-session permission for UDP transit.
Its Logoff theorem excludes UDP transit while allowing independently guarded control errors before forward filtering.
Native evidence covers related hooks, tuple restoration, full and partial quotes, odd lengths, TOS, and omission.

Identification allocation, return-routing metadata, successful allocation, current installation, capture attribution, and kernel refinement remain explicit boundaries.
This generation layer excludes received ICMP and host PMTU feedback; the next layer connects both.
Rate-limit state, input fragments, options, extensions, and concurrency remain open.
See the [ICMP guide](ICMP.md).

## Received errors and host PMTU composition

`Netlib/Protocol/IPv4QuotePrefix.lean` reconstructs untrusted IHL-five quotations without validating their embedded checksums or declarations.
Its raw flags and accessible transport bytes remain exact data.
`Netlib/Protocol/ChecksumRewriteRaw.lean` treats IPv4 checksum zero as arithmetic rather than UDP omission.
`Netlib/Protocol/ICMPPrefixNAT.lean` preserves checksum validity or invalidity, raw metadata, application bytes, and checksum residue through inverse NAT.

`Netlib/Protocol/RelatedICMP.lean` binds reversed quoted tuples and zones to unique confirmed records.
Association also requires the native outer-destination guard.
The error's outer source supplies no authentication premise.
Received processing preserves the complete frozen ordinary table and its existing reply observations.

Related destination translation precedes routing, TTL and DF checks, and forward policy.
Related source translation and the late policy precede certified fragmentation.
Theorems establish restored boundary tuples, unchanged quoted TTL, one outer TTL decrement, checksum conditions, and exact family reassembly.
Inactive NAT stages preserve quoted bytes, including a raw checksum zero.

`Netlib/Protocol/PMTU.lean` models connected-host feedback, floor locking, exception refresh and expiry, and local DF capacity.
`Netlib/Protocol/PMTUFacts.lean` proves state bounds and all-prefix invariants.
At one event time, updates cannot raise effective PMTU when the configured lifetime is positive.
Expiry can restore the physical route MTU across times.
Matching feedback from an arbitrary reporter can strictly reduce an unlocked cached estimate.

`Netlib/Check/RelatedICMP.lean` compares mixed UDP, received-error, and erase events using the shared replay certificate.
Its fragment-family comparison includes embedded IPv4 checksum residue, even when that checksum is invalid.
`Netlib/Check/PMTU.lean` derives updates from received bytes and verifies queries and drained-error send capacity.
`Report.observed_send` transfers matched send observations to the actual computed cache and capacity result.

`Netlib/Examples/PMTUDeployment.lean` constructs the delivered decoder certificate from actual forwarded and reassembled bytes.
Its update theorem connects the restored sender tuple to the host's actual PMTU operation while gateway conntrack remains frozen.
The native four-namespace experiment observes 600-byte discovery, local oversized-send rejection, smaller-payload delivery, and forged-source reduction to 576.
Post-episode snapshots remain unobserved at earlier intermediate prefixes rather than being attributed to unmeasured states.

Physical timer correspondence, complete host error queues, source identity, broader protocol coverage, concurrency, and implementation refinement remain open.
The [received-error guide](RECEIVED_ICMP.md) records the exact input and evidence boundaries.


## Ingress queues, completion policy, and timeout errors

`Protocol.IPv4InputFragment` proves exact IHL-five framing before fragment-shape validation.
DF/MF combinations, empty payloads, and unaligned payloads reach the queue transition unchanged.

`Protocol.IPv4Reassembly` computes queue effects for each arrival.
`IPv4ReassemblyFacts` proves normalized-byte provenance, key isolation, bounds, duplicate suppression, completion, removal, and expiry separation.
`IPv4ReassemblyLayout` proves run coverage, disjoint ordering, unique keys, and preservation through every computed prefix.
Its readiness theorem establishes completion from complete coverage and valid metadata.
The defensive invalid-layout result is unreachable from the initial state.

The permutation result compares actual outputs with equivalent retained pieces.
It does not establish completion for every permutation of arbitrary arrivals.
Run grouping and conflicting duplicates can depend on arrival order.

`Protocol.ReassemblyForwarding.step_incomplete` proves that incomplete arrivals leave conntrack unchanged.
Its output facts derive current routing, live TTL, DF checks, and the effective fragment cap from actual processing.
`Examples.ReassemblyDeployment` connects completion to the current compiled EAP scope and method readiness.
Its Logoff and credential-revocation results exclude output under current installed policy, regardless of the earlier buffering policy.
Installation timing and identity-to-packet binding remain deployment premises.

`Protocol.IPv4Refragmentation` supports budgets from 28 bytes and proves payload, header, coverage, and size contracts.
Observed layouts have computed semantic checks rather than an assumed copying-path shape.
A fitting whole input still requires one whole output.
The internal kernel allocation path remains outside the model.

`Protocol.IPv4ReassemblyTimeout` derives errors from actually expired queues and their stored first fragments.
Its quotation uses the original fragment header and normalized accepted bytes.
The selected local-output path proves a reversed-quote lookup miss, invalid-state output permission, unchanged conntrack, and bounded ICMP type 11/code 1.
Unsupported associations remain outside this selected timeout path.

The reassembly checker carries ordinary-table, queue, and layout invariants through actual fragment, wait, and erase events.
The timeout checker compares expired-queue errors alongside the same queue and ordinary-table history.
The [ingress guide](REASSEMBLY.md) records framing, clocks, control-policy scope, native observation boundaries, and remaining work.
