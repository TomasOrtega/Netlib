# Proof inventory and trust boundary

Run `lake build` locally to verify the Lean declarations. The library adds no
axioms and uses no `sorry` or `native_decide`. Tests in
`NetlibTest/Reasoning.lean` use kernel reduction or the general theorems below.

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

The solver needs exponential time in the number of distinct atoms. A complete
truth table establishes correctness for a finite scope. It does not establish
scalability.

## Network laws and analysis

`Netlib/Policy/Analysis.lean` keeps domain laws fixed during requirement
minimization. `Analysis.simplifyUnder_preserves` proves that the retained
requirements have the same models under those laws. Analysis accepts at most
16 distinct atoms, including atoms in laws and goals.

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
They do not model a vendor parser or a live device. The configuration CLI uses
named-service topology separately.

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
