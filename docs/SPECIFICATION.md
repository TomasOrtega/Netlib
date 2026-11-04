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

The CLI model contains a finite set of nodes and directed links. Each node has
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

These models are stateless. They keep the same header throughout a path.
They exclude packet rewriting and dynamic routing protocols. They form a Lean
library interface. The JSON importer and requirement CLI still use named services.

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

The request model is a Lean library interface. The JSON CLI does not import
identity systems or request policies. These proofs do not establish cryptographic
authentication, protocol correctness, or live enforcement behavior.

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

The implementation does not parse vendor configurations, inspect live networks,
or deploy network changes. It does not certify CSfC, NIST, or another external
standard. Reference architectures show formal patterns within the stated model.

The models exclude dynamic routing protocols, packet rewriting, cryptographic
algorithms, authentication protocols, stateful middleboxes, temporal liveness,
and adversarial compromise. Extensions need new semantics, proofs, and rules
that connect their input to those semantics.

Exhaustive propositional analysis needs exponential time in the number of atoms.
The executable adapter rejects more than 16 distinct atoms. This limit includes
goals and atoms from domain laws. It does not sample a larger scope.

Exhaustive network evaluation also has finite resource costs. The DARPA notice
targets a reduction of two to three orders of magnitude in time and cost.
This repository has no measurement that establishes that target.

Scalable symbolic solvers and external certificate generators can extend the
existing interfaces. Each extension must establish its connection to the formal
semantics.
