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

These forwarding models are stateless.
They keep the same header throughout a path.
They exclude packet rewriting and dynamic routing protocols.
The `dataplane` command imports these models through JSON schema 1.

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

## Trust boundary

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

## Scope limits

Netlib does not translate arbitrary PDFs or recursively resolve external
requirements. It does not infer mission intent, device roles, or natural-language
meaning. Reviewers must supply and assess those inputs.

The implementation imports only its declared hostapd fragment and versioned model formats.
It does not inspect live networks or deploy network changes.
It does not certify complete CSfC, NIST, or 5G compliance.
Reference architectures show formal patterns within the stated model.

The models exclude dynamic routing protocols, packet rewriting, cryptographic
algorithms, full authentication protocols, stateful middleboxes, temporal liveness,
and adversarial compromise. Extensions need new semantics, proofs, and rules
that connect their input to those semantics.

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
