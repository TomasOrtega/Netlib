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
| Mathematical foundations | Paths, cuts, refinement, transition traces, domain composition, and fault models. FIFO conservation, backlog bounds, and finite draining. | Information flow, network calculus, probability, physical timing, adversaries, congestion, reliability bounds, and foundational literature. |
| Connected protocol stacks | Packet fields, ordered ACLs, destination routing, session guards, and generic trace refinement. | Connected Ethernet, IP, TCP, DNS, BGP, TLS, QUIC, Wi-Fi, and cellular semantics with implementation correspondence. |
| Machine-checkable standards | Selected Wi-Fi and 5G profiles. Formal clause guards, profile composition, compatibility, and version refinement. | Broader clause coverage, reference resolution, reviewed translations, interoperability cases, and connections between formal profiles and existing importers. |
| Complete architectures | A campus foundation composes domains, session enforcement, management isolation, and availability under one internal-node fault. | Real configuration adapters, complete protocol bindings, quantitative guarantees, and campus, cloud, cellular, data-center, and federation deployments. |
| Verified implementations and compilers | Executable checkers connect results to graph and logical semantics. ACL refinement checks cover every header. | Protocol implementations, verified configuration compilation, certified synthesis, and optimization. |
| Safe operation | Certified finite update plans cover every intermediate state. Trace refinement transfers safety between models. | Real deployment commands, verified update adapters, routing transients, runtime evidence, monitoring, and recovery. |
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

## Next implementation work

1. Connect strict router and firewall adapters to the quantified packet checker.
2. Model stateful forwarding, packet rewriting, and routing convergence.
3. Connect authentication protocol traces to session evidence.
4. Connect concrete upgrade commands to certified intermediate snapshots.
5. Compose queue guarantees and add physical timing and reliability models.
6. Extend the campus proof through those models and real configuration inputs.
7. Reuse the resulting contracts for other architectures and independent domains.

Standards additions should exercise reusable semantics and preserve exact source clauses.
The complete objective remains open while any row lacks the required evidence.

The [proof inventory](PROOFS.md) records current guarantees.
The [specification](SPECIFICATION.md) records their assumptions and limits.
