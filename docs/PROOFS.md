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

These packet models are stateless and preserve the header along each path.
The original `check` command uses named services.
The `dataplane` command uses the composed graph below.

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

## Scope of the proofs

The proofs apply to the mathematical model. Reviewers must compare the model,
observation vocabulary, and source interpretation with the intended deployment.
Domain laws restrict abstract assignments only where network semantics justify
those laws.

Source citations and retained requirement text support review. They do not prove
that a translation preserves unrestricted natural language. Completion concerns
only supplied goals. It does not discover unstated security intent.

The examples do not certify an external standard or live equipment. The models
also exclude packet transformations, cryptographic correctness, and performance
targets. See the [specification](SPECIFICATION.md) for the complete scope.
