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
 * `Netlib.Network` defines paths, cuts, gateways, and refinements.
 * `Netlib.Packet` defines packet fields, matches, and access control lists.
 * `Netlib.Model` defines configuration data.
 * `Netlib.Policy` connects requirement text and network observations.
 * `Netlib.Check` checks configurations and constructs certified results.
 * `Netlib.Examples` gives proved architecture examples.

The packet library adds 32-bit addresses, protocol numbers, and port ranges.
An address prefix selects addresses with the same first bits.
A match can restrict any supported header field.
An absent field accepts every value for that field.
The JSON CLI uses named traffic classes instead of packet headers.

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
Finite logical analysis enumerates every assignment within its declared scope.
The input adapter rejects more than 16 distinct atoms.
It includes background laws in this count.

Check consistency before goal coverage.
An inconsistent policy entails every goal in classical logic.
Reduce requirements in sequence so that two duplicate requirements cannot both disappear.
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
python3 scripts/check_cli.py
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

Run the local website command from the repository root:

```
python3 scripts/build_docs.py
```

The script saves the site in `docs/site.tar.gz`.
It records source hashes in `docs/site-manifest.json`.
The combined site contains a manual and an API directory.
Review the generated pages with an HTTP server before a push.
Commit the Lean source before the docs build.
This gives each source link a stable commit.
Then commit the source documentation, archive, and site manifest.

CI checks the saved source hashes and site links.
CI unpacks the archive and publishes static files.
CI must not install Lean or run Lake, doc-gen4, or Verso.
CI must never compile Lean code.
A dependency cache does not change this rule.

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
