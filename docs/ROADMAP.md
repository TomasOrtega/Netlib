# Formal networking roadmap

Netlib aims to formalize networking as a discipline.
The objective includes theory, standards, implementations, deployments, and operational changes.
Composition connects these parts.
A proved module must support proofs about larger systems that use it.

## Full objective and current evidence

Each row records an ongoing goal.
The evidence column identifies partial results.
It does not establish completion of the goal.
All seven goals remain OPEN.

| Goal | Status | Evidence now | Work still required |
| --- | --- | --- | --- |
| Mathematical foundations | OPEN | Paths, refinement, traces, domain composition, faults, and FIFO bounds. Old-prefix clearance under overload. Header transformation closure and alias-reuse indistinguishability. Interval/run invariants, timed input queues, and accepted-byte provenance. Arbitrary-identity retirement preserves exact counts and constructs finite targeted drains. | Broader information flow and adversary models, network calculus, probability, physical timing, congestion, reliability bounds, and foundational literature. |
| Connected protocol stacks | OPEN | IPv4 UDP forwarding preserves payload through tracked NAT, regenerates checksums, decrements TTL, and produces verified MTU-bounded fragment families. Generated and received ICMP errors restore quoted tuples through related NAT. Host PMTU feedback has bounds, expiry, and forgery-limit proofs. Ingress reassembly precedes current policy; timeout errors retain first-fragment bytes and zone templates. Checked EAP evidence and credentials control the selected packet classes. | Full Ethernet, IP, TCP, DNS, BGP, TLS, QUIC, Wi-Fi, and cellular semantics with implementation correspondence. |
| Machine-checkable standards | OPEN | Selected Wi-Fi and 5G profiles, RFC 3748 framing, and selected EAP-TLS evidence guards. Formal clause guards, compatibility, and version refinement. | Broader clause coverage, reference resolution, reviewed translations, interoperability cases, and connections between profiles and implementations. |
| Complete architectures | OPEN | Campus session enforcement, isolation, and single-fault paths. Checked EAP principals and credentials feed a configured-principal campus theorem. Stateful reply failover has exact-replication proofs. Ordered native handoff connects cache staging and observed kernel installation. Protected handoff preserves readiness across every admissible selected interleaving. Joint wired campus replay connects current session installation, duplex topology, actual ticket history, and planned withdrawal. | Native campus configuration and topology bindings, full protocol semantics, distributed state propagation, quantitative guarantees, and broader architecture deployments. |
| Verified implementations and compilers | OPEN | Certified packet intent and current-session compilation preserve every header. Native policy exports match EAP-derived scope guards for every state and header. Typed ICMP output guards retain type/code requirements. Current installation certificates derive policy equivalence at actual consumed authentication prefixes. | Verified parsers and deployment operations, protocol implementations, broader configuration compilation, synthesis, and optimization. |
| Safe operation | OPEN | Certified update snapshots, late barriers, and packet traces preserve explicit contracts. Buffered replay connects admissions to FIFO service and certifies clean delivery after sufficient drain capacity. Outstanding route assignments preserve actual source provenance through arbitrary retirement order. Progress from prior conditions and exact retirement counts support guarded fencing. Planned withdrawal archives the primary and checks current session policy in one timeline. | Verified native install commands, physical queue and service correspondence, routing transients, concurrent updates, monitoring, and recovery. |
| Internet-scale assurance | OPEN | Local graph refinements compose through checked border transitions. Domain node types remain disjoint in the composed graph. | Contract exchange, partial observations, changing routes, independent operators, hidden topology, and larger end-to-end demonstrations. |

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
Their complete campus interpretation still requires broader protocol and failure semantics.

`Netlib.Examples.CampusNAT` connects the campus graph to session-gated packet processing and per-gateway NAT stores.
It proves primary request/reply paths with the actual updated store.
A surviving physical return path can still block every reply when the standby has no grants.
Exact pre-fault replication permits a return path under each admitted single internal-node fault.
The model assumes a currently permitted session, unchanged grant clocks, and a usable shared public alias.
It does not implement replication, ownership transfer, route selection, or convergence.
Native configuration bindings and the complete campus landmark remain open.

The [native failover layer](STATEFUL_FAILOVER.md) now uses ordinary byte-derived UDP processing across two gateways.
Both kernel tables start empty; an actual primary packet establishes the record selected for replication.
The replay separates received cache state, kernel commitment, each endpoint route change, and the primary data fence.
Current standby policy remains effective after installation, including a denied reply's seen-reply update.
Provenance identifies the actual earlier staging prefix and computed source table.
The joint campus layer below connects their selected session and planned-withdrawal interpretation.
Automatic detection, reliable synchronization, expiry, concurrent installs, and bounded convergence remain open.

The [safe handoff extension](SAFE_HANDOFF.md) separates endpoint route assignment from later processing at the assigned gateway.
Its universal theorem covers every admissible selected packet and control interleaving, with progress from conditions on the preceding state.
Each served ticket cites its actual earlier assignment prefix and retains that source's bytes, gateway, direction, identity, and operation epoch.
Current assigned-gateway configuration and local classification govern processing after either endpoint route changes.
Current-session enforcement additionally requires installation of the matching certified policy.

The finite drain constructs exactly the initial target count of processing operations before fencing, without assuming global FIFO order.
It does not establish physical time, fair scheduling, native queue correspondence, or eventual delivery.
The native example records 20 operations, seven datagrams, and six protected tickets without a native EAP enforcement claim.
Lifetime stability, physical correspondence, installation coherence, and complete campus integration remain open.

The [joint campus deployment](CAMPUS_DEPLOYMENT.md) connects actual wired EAP, credential installation, current native policies, and the ordinary protected flow.
Its unified history interleaves authentication, network processing, and planned primary withdrawal.
Current installation certificates derive forward equivalence from actual source rules and the consumed authentication prefix.
Each served output has exact NAT, payload, and TTL guarantees from an actual earlier assignment in that same timeline.
Current application validity and method readiness follow at the processing prefix.
The declared class must cover even denied packets, and next-hop roles must match the direct request or reply path.

The direct graph uses four data roles and an explicit collapse of abstract access-point vertices.
Request and reply continuity, management isolation, and mandatory gateway traversal have reusable proofs.
After drain and fencing, primary state becomes an archive and later live primary operations are prohibited.
The saved example records 26 native operations, eight datagrams, and seven tickets.
Its joint replay has 45 operations: 21 authentication, 23 network, and one withdrawal.
Cryptography, wireless deployment, principal anti-spoofing, physical correspondence, automatic failures, lifetimes, and the complete campus objective remain open.

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

The [late-filter barrier](REVOCATION.md) supplies an operational output exclusion contract.
Its certificate covers all state/header contexts, including cached translations and established traffic.
The contract transfers through ordered operations and compliant observed replay suffixes.
The cutover and translated forbidden class remain declared inputs.
Native installation, barrier retention, physical drain correspondence, credential revocation, and complete upgrade protocols remain open.

The [buffered model](BUFFERING.md) now separates barrier-controlled admissions from delivery of earlier queued packets.
Its FIFO proof clears the old prefix after sufficient service even when new clean arrivals keep the total backlog growing.
Ready certificates establish a clean pending queue and clean subsequent modeled service under retained barriers.
A native delayed UDP capture demonstrates delivery after barrier installation.
Physical service bounds, complete queue correspondence, native install proofs, and the campus integration remain open.

The [EAP session layer](EAP.md) now connects raw framed messages to guarded method evidence, session authentication, credential checks, and campus paths.
Its codecs reconstruct arbitrary accepted bytes, including preserved padding.
Native wired EAP-TLS success, Logoff, and server-name rejection supply finite authentication evidence.
The configured-principal theorem uses the checked report's consumer, rather than assuming the outer Identity is authenticated.
Native campus enforcement, wireless key installation, RADIUS paths, trusted method-to-round attribution, and cryptographic refinement remain open.

The [session firewall compiler](SESSION_FIREWALL.md) now binds current EAP-derived credentials to native packet classes.
Lifecycle output requires a matching valid scope and current method readiness.
Current Logoff and revocation policies exclude cached flows without deleting their conntrack records.
The wired native capture measures selected routed application packets and checks exported policies at declared event prefixes.
Identity-to-header binding, credential signatures, native installation correctness, update latency, and complete campus topology correspondence remain open.

The [wire layer](WIRE.md) now derives policy headers from selected Ethernet, IPv4, and UDP bytes.
Generic Internet checksum synthesis and exact codec reconstruction have proofs.
Fresh native UDP captures supply completed checksums and separate gateway forwarding from final transport reception.
The decoded packet theorem composes with the current session firewall and tracked output.

The [wire forwarding extension](WIRE_FORWARDING.md) now preserves complete UDP payloads through tracked destination and source NAT.
It regenerates present checksums, preserves omission, and decrements the emitted TTL.
Routing precedes TTL expiry; expired replies retain tracking updates while fresh expired candidates remain unconfirmed.
Compliant replay transfers observed output to payload equality and TTL decrement.
The checked native session policy supplies the matching scope and current EAP readiness.
Native evidence covers 17 IP frames, including 14 UDP frames and three ICMP frames.
The selected payload, TTL, and NAT checksum model closes the earlier header-only forwarding gap.
The [MTU extension](MTU.md) now orders TTL and DF rejection before filtering and fragments permitted translated output after confirmation.
Generated families fit the selected effective MTU and recover the whole packet under strict reassembly, including arbitrary capture order.
Compliant native replay transfers payload, TTL, and fragment-size guarantees to observed families.
A normal UDP socket receives the complete 1,200-byte payload after native three-fragment forwarding.
The [ICMP extension](ICMP.md) now generates selected TTL and DF errors with bounded quotations, related output filtering, and NAT restoration.
Incremental checksum proofs establish valid translation and exact quoted-packet restoration without requiring missing application bytes.
Compliant replay transfers observed errors to the computed source prefix and generation guards.
A fresh capture checks twelve errors across full and truncated quotations, TOS changes, and both NAT directions.
The [received-error extension](RECEIVED_ICMP.md) associates quoted UDP tuples with confirmed records and preserves their table state.
Raw quotation proofs preserve invalid checksum residues and declarations through staged related NAT.
The host model supplies bounded PMTU updates, floor locking, half-life refresh, expiry, and local DF send-capacity results.
An end-to-end composition theorem connects the actual forwarded error and restored tuple to the host update.
A four-namespace capture demonstrates PMTU feedback and a matching forged-source reduction.
The [ingress layer](REASSEMBLY.md) now buffers IPv4 fragments before ordinary attachment and NAT.
Its proofs preserve byte provenance, queue keys, run geometry, bounds, and layout through actual arrivals.
The completing event evaluates current EAP-derived policy, so pre-Logoff fragments do not retain an earlier permission.
Related output contracts cover re-fragmentation under the retained ingress maximum and the route MTU.
Selected timeout errors preserve original first-fragment headers, normalized data, and inherited zone identity.
A kind-aware output adapter retains native ICMP type/code predicates in its compiled policy.
Full TCP and IPv6 errors, broader ingress reassembly, options, concurrency, and complete kernel refinement remain open.
Principal-to-tuple ownership and global policy-installation timing also need stronger evidence.

## Next implementation work

1. Broaden ingress reassembly through options, disorder heuristics, resources, and associated timeout processing. Extend TCP, IPv6, host behavior, routing, concurrency, and implementation refinement.
2. Extend protected-flow handoff through expiry, deletion propagation, failures, broader concurrency, and bounded routing convergence. Connect it to the complete campus interpretation.
3. Refine EAP method evidence with cryptographic semantics, wireless key installation, and trusted link/session attribution.
4. Connect concrete upgrade commands and physical queue behavior to the certified barrier and intermediate snapshots.
5. Connect physical service lower bounds and concurrent queue models to the FIFO drain proof, then add timing and reliability guarantees.
6. Extend the joint wired campus interpretation through cryptography, wireless deployment, principal anti-spoofing, physical correspondence, lifetimes, and broader fault behavior.
7. Reuse the resulting contracts for other architectures and independent domains.

Standards additions should exercise reusable semantics and preserve exact source clauses.
The [stateful guide](STATEFUL.md) distinguishes full transfer-state coverage from observed-trace auditing.
Its alias-reuse theorem records an adversarial limit that stronger protocol semantics must address.
The complete objective remains open while any row lacks the required evidence.

The [proof inventory](PROOFS.md) records current guarantees.
The [specification](SPECIFICATION.md) records their assumptions and limits.
