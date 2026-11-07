# Independent native network plans

Netlib checks two local update plans against fixed public contracts and border bindings.
Each operator supplies an initial native snapshot and a finite list of later revisions.
Every pair of checked revisions satisfies the public queries for all selected packet headers.

## Entry points and input

[`Netlib.Federation.Deployment.certifyJson`](../Netlib/Check/FederatedDeployment.lean) accepts raw JSON text.
It returns an error or the parsed `Input` with its `Deployment.Checked input` certificate.
`Deployment.certify input` accepts the typed input directly.
These are library functions; this feature has no separate CLI command.

The [complete example](../examples/federation/deployment.json) uses schema `1` and scope `two-domain-ipv4-transit`.
The strict schema requires these fields:

| Object | Fields |
| --- | --- |
| Root | `schema`, `scope`, `left`, `right`, `intent`, `limits` |
| Local plan | `contract`, `initial`, `updates` |
| Contract | `id`, `version`, `nodes`, `cases` |
| Public node | `id`, `role` |
| Case | `id`, `selector`, `request`, `upper`, `must` |
| Request | `principal`, `resource`, `operation` |
| Arc | `source`, `target` |
| Revision | `id`, `snapshot`, `projection`, `anchors` |
| Projection row | `localNode`, `publicNode` |
| Anchor row | `publicNode`, `localNode` |
| Intent | `borders`, `queries` |
| Public reference | `side`, `node` |
| Border | `source`, `target`, `sourceDomain`, `targetDomain`, `sourceVersion`, `targetVersion`, `cases` |
| Query | `id`, `kind`, `case`, `source`, `target`, `gateways` |
| Limits | `cells`, `work` |

The parser rejects unknown fields, missing fields, duplicate object keys, and unsupported native input.
Public roles are `endpoint`, `enforcement`, `ingress`, `egress`, and `internal`.
References use side `left` or `right`; queries use kind `reach`, `isolate`, or `mediated`.
Each revision uses the [Linux transit snapshot schema](LINUX.md#bundle-schema).
Revision IDs must be nonempty and unique within each plan.
Public node names, case IDs, and query IDs also pass their inventory checks.

## Checked contracts

Each case supplies an `upper` graph and a `must` graph.
Every native edge must project to an upper edge or remain at the same public node.
Every must edge must have a checked native path between its exact anchors.
Thus, upper cuts prove isolation and mediation; must paths prove availability.
An upper path alone cannot establish availability.

Peer cases must have the same case ID, packet selector, and principal/resource/operation request.
Query endpoints must have the endpoint role.
Each named gateway must have the enforcement role.
Borders must cross operators from an egress node to an ingress node.
They bind both exact contract IDs, both versions, and the selected case IDs.
Egress anchors must be native terminals.
Native projections, anchors, request policy, and actual enforcement selectors must pass their local checks.

`limits.cells` bounds each native packet partition.
`limits.work` admits a complete estimate for both plans and the public checks.
The estimate includes input rows, every revision, packet partitions, borders, queries, and graph search terms.
The complete work guard runs before native header enumeration.
This estimate is not a proved runtime or processor-cycle bound.

## Public guarantees

[`Checked.snapshot`](../Netlib/Check/FederatedGuarantees.lean) applies to any pair of local cursors.
Its query results cover every retained query and every query in the supplied intent.
Each result applies to every header accepted by its selected case.
A reach result retains its exact public must-path and proves an actual native walk.
Each adjacent native step has route and firewall evidence or a declared border origin.
Local origins retain the exact revision, router, selected route, and nftables rule or default policy.

A mediated result excludes bypass through every native preimage of its public gateway list.
The `mediatedOn` field also proves enforcement by the named operator when the checked gateway list lies on that side.
The result retains both that operator and the exact public gateway labels.

`Checked.interleaving_guarantees` covers every admitted interleaving of the two plans.
`Checked.prefix_guarantees` covers every prefix of each such trace.
The results retain local operation order, counts, exact revisions, and native certificates.
Each local step selects only its next declared revision.
The theorem does not depend on an enumerated schedule.

## Checked finite case

The [tests](../NetlibTest/FederatedDeployment.lean) check six native snapshots across two three-revision plans.
Each first update adds a private relay to the forwarding path.
Each second update changes only its revision ID.
Private node names overlap across operators; native node types keep the two inventories distinct.
The public contracts and border remain fixed through all nine revision pairs.

| Query | Requirement |
| --- | --- |
| `APP` | The campus client has a native path to the provider service. |
| `CAMPUS_POLICY` | Every such path visits campus enforcement. |
| `PROVIDER_POLICY` | Every such path visits provider enforcement. |
| `MANAGEMENT` | The campus client cannot reach provider management. |

Tests reject stale border versions, wrong roles, unknown nodes, mismatched cases, missing must paths, and exhausted budgets.
They also reject an unsafe intermediate revision and a real native campus-enforcement bypass.
The intermediate failure affects source port `50001` inside the selected interval.
Separate universal proofs cover all selected headers and arbitrary traces and prefixes.

## Model limits

The native profile models selected unfragmented IPv4 forwarding with main-table routes.
The same header applies throughout each path.
Each revision change is atomic in the model.
The proofs do not describe native update commands or a packet that crosses several revisions during one path.
Unbounded concurrent changes, packets in flight, delivery time, and physical delivery remain outside this result.

The supplied topology, principal identities, public port and interface bindings, and border connectivity must match the deployment.
Source provenance does not authenticate snapshots or prove live kernel behavior.
Identity protocols, signatures, contract negotiation, and topology confidentiality remain outside the certificate.
This result excludes NAT, connection tracking, and packet rewriting.
The raw parser rejects unsupported Linux features.
