# Linux forwarding snapshots

The Linux adapter imports route and firewall snapshots into the checked data-plane model.
It reads iproute2 6.19.0 main-table routes and nftables 1.1.3 JSON schema 1.
It preserves original route records, rule handles, expression indices, and comments.

The `linux` and `linux-traffic` commands keep this stateless forwarding scope.
The separate [conntrack evidence guide](CONNTRACK.md) covers reported flow-policy audits and frozen tuple associations.

## Run the examples

```sh
lake exe netlib linux examples/linux/deployment.json --json
lake exe netlib linux examples/linux/bypass.json --json
lake exe netlib linux-traffic examples/linux/deployment.json AVAILABLE examples/linux/https-class.json --json
```

The first command checks the declared fixed-header queries.
The second finds a path around the enforcement gateway.
The third checks every header selected by the HTTPS match.
Reports include source locations and the model assumptions.

The scenario fixtures use controlled native-format inputs.
`deny-first.json` puts a drop before the service permit.
`route-drop.json` adds a more specific blackhole route.
`management-leak.json` adds a route and permission to the management segment.
These scenarios represent modeled transit locations, not captured campus hosts.

## Bundle schema

Schema 1 has four fields:

| Field | Meaning |
| --- | --- |
| `schema` | The integer `1`. |
| `scope` | The string `main-table-ipv4-transit`. |
| `intent` | Data-plane schema 1 without `links` or `routes`. |
| `routers` | Exactly one snapshot for every declared device. |

Each router has `node`, `routeVersion`, `bindings`, `routes`, and `nftables` fields.
The route version must be `6.19.0`.
The routes are the native array from `ip -j -4 route show table main`.
The firewall is the complete object from `nft -j -nn list ruleset`.
Each binding has `device`, `nextNode`, and `gateway` fields.
The gateway is a dotted IPv4 address or null.

Bindings declare physical adjacency and the interpretation of an output interface and gateway pair.
The reviewer must check that interpretation against the deployment.
The adapter generates all modeled physical links, ACLs, and route tables.
It rejects handwritten `links` or `routes` in the intent object.

## Accepted forwarding subset

Route lookup uses destination prefixes and the longest matching prefix.
Unicast routes need an exact device and gateway binding.
Blackhole, unreachable, and prohibit routes compile to a drop.
The adapter rejects repeated canonical prefixes, including metric alternatives.
It also rejects multipath, policy-routing fields, encapsulation, unsupported scopes, and nonempty route flags.

The firewall contains one IPv4 table and one forward filter base chain.
Each rule has supported header matches and one terminal accept or drop verdict.
The importer preserves first-match order and the explicit chain policy.
TCP and UDP port selectors retain their implied protocol guards.
Unknown expressions, extra chains, NAT, connection tracking, jumps, sets, and expressions after a verdict cause errors.

Every JSON text entry point rejects duplicate decoded object keys.
For example, `a` and `\u0061` identify the same key.
The strict check also covers nested objects and existing network, Wi-Fi, and 5G inputs.

## Guarantees and assumptions

`LinuxRoute.Snapshot.nextHop_correct` connects compiled routing to structured source lookup for every destination address.
`Nftables.Snapshot.compile_allows` connects ACL decisions to the structured source chain for every header.
`LinuxDeployment.Snapshot.model_correct` connects their composed graph to the source snapshots and declared request policy.
The existing certificate checker then proves the supplied graph queries.

These theorems assume valid, unfragmented IPv4 transit headers after main-table selection.
The graph uses declared interface and gateway bindings.
Additional hooks or packet transformations must not change the modeled decisions.
Declared identity results and request enforcement describe external controls supplied through the intent.
The firewall snapshot alone does not establish authentication or authorization.
All snapshots must describe the same stable deployment state.

Parsing and correspondence with live kernel execution require separate evidence.
Local delivery, host input/output, the routing policy database, fragmentation, neighbor discovery, and packet rewriting remain outside this subset.
Permitted graph paths do not establish physical delivery or timing.

## Native evidence

The repository includes genuine exports from disposable Linux containers:

- [iproute2 6.19.0 routes](../examples/linux/captured-routes.json).
- [nftables 1.1.3 ruleset](../examples/linux/captured-nftables.json).
- [Generated compiler input](../examples/linux/captured-compiler-input.json).
- [Original compiler requirements](../examples/linux/captured-compiler-intent.json).
- [Native compiler re-export](../examples/linux/captured-compiler-output.json).
- [Producer versions, source hashes, and fixture hashes](../examples/linux/capture-provenance.json).

Pinned nftables accepted the generated JSON in syntax checking and actual isolated loading.
Kernel export changed handles and removed redundant protocol tests.
Exact partition checks establish equivalence of the two imported policies for every modeled header.
This is native interoperability evidence, separate from the structured translation proofs.

The capture recipes run inside a disposable container with a private network namespace and `NET_ADMIN` capability.
For example:

```sh
docker run --rm --cap-add NET_ADMIN -i \
  alpine@sha256:ff7f0c727dd796aa36787bfcd9a64bf35a6ce72a73451b3359fde849b6703d63 \
  sh < examples/linux/capture-nftables.sh > nft-capture.tar
```

The [route recipe](../examples/linux/capture-routes.sh) also builds the pinned iproute2 source.
Addresses and handles can change between captures.
The recipes verify the recorded producer source hashes.

Use the [compiler guide](COMPILER.md) to generate a policy from packet requirements.
Use the [conntrack guide](CONNTRACK.md) to audit reported state against a separate declared policy.
