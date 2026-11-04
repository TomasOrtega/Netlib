# Formal networking roadmap

Netlib aims to formalize networking as a discipline.
The objective includes theory, standards, implementations, deployments, and operational changes.
Composition connects these parts.
A proved module must support proofs about larger systems that use it.

## Full objective and current evidence

Each row records an ongoing goal.
The evidence column identifies partial results.
It does not establish completion of the goal.

| Goal | Evidence now | Work still required |
| --- | --- | --- |
| Mathematical foundations | Paths, refinement, traces, domain composition, faults, and FIFO bounds. Header transformation closure and alias-reuse indistinguishability. | Broader information flow and adversary models, network calculus, probability, physical timing, congestion, reliability bounds, and foundational literature. |
| Connected protocol stacks | Packet policies, routes, sessions, shared stores, tuple translation, and ordinary hook lifecycles. Ordered traces compose stages and successive packets. | Connected Ethernet, IP, TCP, DNS, BGP, TLS, QUIC, Wi-Fi, and cellular semantics with implementation correspondence. |
| Machine-checkable standards | Selected Wi-Fi and 5G profiles. Formal clause guards, profile composition, compatibility, and version refinement. | Broader clause coverage, reference resolution, reviewed translations, interoperability cases, and connections between formal profiles and existing importers. |
| Complete architectures | Campus session enforcement, isolation, and single-fault paths. Stateful reply failover under exact grant replication. Separate Linux snapshots supply checked forwarding. | Connections between those imports and the campus theorem, complete protocol bindings, quantitative guarantees, and broader architecture deployments. |
| Verified implementations and compilers | Certified packet intent compilation and structured nftables emission preserve every header. Native loading and re-export have fixture evidence. | Verified parsers and deployment operations, protocol implementations, broader configuration compilation, synthesis, and optimization. |
| Safe operation | Certified update snapshots and packet traces preserve explicit invariants. Native filter refinement covers every modeled state and header. | Real deployment commands, verified update adapters, routing transients, runtime evidence, monitoring, and recovery. |
| Internet-scale assurance | Local graph refinements compose through checked border transitions. Domain node types remain disjoint in the composed graph. | Contract exchange, partial observations, changing routes, independent operators, hidden topology, and larger end-to-end demonstrations. |

## Campus landmark

`Netlib.Examples.Campus` is a foundation for the requested campus demonstration.
It proves management isolation and mandatory gateway traversal.
Two internally disjoint client-to-server paths preserve availability under any admitted single internal-node fault.
Client and server failures fall outside that fault model.
Independent link failures also fall outside it.

The session guard controls application access.
The proof connects a recorded admission to credential conditions and an available path after the fault.
Every intermediate session update preserves the stated application contract.

The example uses an abstract forwarding graph.
It does not import physical APs, routing tables, firewall rules, or upgrade commands.
Identity and token integrity remain supplied observations.
The complete campus landmark requires those additional connections and their evidence.

The separate [Linux adapter](LINUX.md) now reads native route and firewall snapshots.
Its compiled graph matches the structured source semantics under explicit transit assumptions.
The [packet compiler](COMPILER.md) generates a native-format firewall from checked intent.
The abstract campus theorem and these imported forwarding models still need a common protocol and failure interpretation.

`Netlib.Examples.CampusNAT` connects the campus graph to session-gated packet processing and per-gateway NAT stores.
It proves primary request/reply paths with the actual updated store.
A surviving physical return path can still block every reply when the standby has no grants.
Exact pre-fault replication permits a return path under each admitted single internal-node fault.
The model assumes a currently permitted session, unchanged grant clocks, and a usable shared public alias.
It does not implement replication, ownership transfer, route selection, or convergence.
Native configuration bindings and the complete campus landmark remain open.

The [conntrack adapter](CONNTRACK.md) now reads visible XML records and full-status Netlink capture JSON.
Its per-flow model uses complete zone and tuple keys, including shared public endpoints across different peers.
Status-aware rewrite algebra and original-flow policy audits have separate proofs.
Native TCP/UDP socket observations agree with the retained tuple projections.
The collector and byte decoding remain reviewed implementations rather than verified parsers.
These results do not establish kernel refinement, complete state visibility, native admission, or campus deployment correspondence.

The [lifecycle checker](LIFECYCLE.md) composes imported destination routes, stateful filters, and fixed NAT rules for ordinary forwarded packets.
It distinguishes tentative candidates from confirmed records and proves ordering, binding reuse, and drop-state effects.
The native replay covers policy changes and deletion with observed intermediate headers and selected table snapshots.
Static chain refinement checks all five state labels and every header at the same hook and priority.
These results still need transport validation, concurrency, timing, native control operations, and complete campus authentication bindings.

## Next implementation work

1. Extend ordinary packet lifecycles through transport validation, expiry, concurrency, and additional hooks and routing scopes.
2. Connect stateful failover to native processing, replication behavior, and routing convergence.
3. Connect authentication protocol traces to session evidence.
4. Connect concrete upgrade commands to certified intermediate snapshots.
5. Compose queue guarantees and add physical timing and reliability models.
6. Extend the campus proof through those models and real configuration inputs.
7. Reuse the resulting contracts for other architectures and independent domains.

Standards additions should exercise reusable semantics and preserve exact source clauses.
The [stateful guide](STATEFUL.md) distinguishes full transfer-state coverage from observed-trace auditing.
Its alias-reuse theorem records an adversarial limit that stronger protocol semantics must address.
The complete objective remains open while any row lacks the required evidence.

The [proof inventory](PROOFS.md) records current guarantees.
The [specification](SPECIFICATION.md) records their assumptions and limits.
