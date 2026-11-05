# Admission around IPv4 reassembly

This library layer composes early interface admission, input reassembly, full-datagram admission, and ordinary tracked forwarding.
It extends the [ingress attachment model](INGRESS_ATTACHMENTS.md) and [reassembly provenance](REASSEMBLY.md).
The corresponding Linux capture and joint campus deployment integration remain open.
The supplied Python helpers inspect passive observations and synthetic model histories.
They do not establish that an installation or runtime experiment occurred.

## Two policy meanings

`Packet.IPv4Envelope` contains source address, destination address, and protocol.
It contains no transport ports.
The coarse compiler erases port predicates from application and maintenance classes.
It preserves current session validity, the authenticated subject, and exact live interface attachment.
Coarse permission grants no UDP-port authorization.

The early guard representation requires a proof that every rule lacks transport selectors.
The importer requires IPv4 prerouting priority `-450` and preserves the actual source rules and priority.
It rejects transport reads even when a selected range covers every port.
Such a range can be equivalent in a complete-header model while requiring unavailable fields in a noninitial fragment.

The full-datagram guard uses the existing exact attachment policy at priority `-300`.
Its permission is checked after reassembly and before ordinary conntrack.
The [existing source investigation](research/INGRESS_ATTACHMENTS.md) records these hook priorities and their implementation assumptions.
The parser and model do not establish kernel refinement or installed-command correctness.

## Computed transition

`Protocol.FragmentAdmission.step` evaluates the installed early policy first.
An early reject preserves fragment queues, ordinary conntrack, and admitted-source history.
The observation clock can still advance.
Timer aging remains a separate modeled effect of a later arrival.

An actual early allow enters `IPv4Reassembly.arrive` with the supplied user/vif domain.
The namespace lifetime selects the surrounding state.
Input-interface identity and EAP round do not become artificial reassembly-key fields.
If a datagram completes, its later guard uses the completing arrival's interface and decoded full header.

A fine rejection retains the computed reassembly transition and preserves ordinary conntrack.
A fine allow enters actual ordinary preparation, routing, current filter policy, NAT, and MTU handling.
An ordinary deny can therefore retain tracking effects that an early deny prevents.
Installed stale allows remain executable during checking; policy mismatch does not silently replace them with desired denial.

## Provenance and current permission

The state retains actual admitted fragment values, ingress metadata, supplied authentication context, and the installed early guard.
Queue provenance additionally records the actual user/vif domain.
Every retained receipt has an arrival time bounded by the modeled observation clock.

`Accepted.output_bound_receipt` connects each output piece to a matching admitted receipt in the same namespace and queue domain.
That receipt has the output envelope, and its timestamp does not exceed completion time.
The theorem establishes matching admitted-byte provenance.
It does not identify one unique physical occurrence among identical duplicate fragments.

The checker compares installed coarse and fine policies against current session-derived policies across every numeric index and header.
Maintenance separation is checked after port erasure.
An exception distinguished only by transport ports can overlap the coarse protected class and must fail this check.

`Checked.early_permission` derives current validity and method readiness for coarse admission.
`Checked.completed_permission` derives full attachment permission at completion.
`Contract.at` derives its current state from a bounded prefix of the supplied authentication stream.
It rejects a prefix beyond that stream.
Authenticity, physical attribution, and joint ordering of separate observed streams still require deployment evidence.

## Namespace retirement

The residency interface processes packets only in its active namespace.
Retirement archives the old model state and removes that live processing target.
It does not claim that kernel fragment queues were flushed.
Fresh initialization requires a namespace lifetime absent from the archive and starts with empty model queues, tracking, and source history.
Later operations preserve every archive.

The session residency binds one authentication round to that lifecycle.
A changed round requires explicit retirement and a fresh namespace lifetime.
The low-level reassembly function remains usable independently and retains its unchanged queue semantics.
Runtime creation, routing replacement, interface retirement, and authentic namespace readbacks remain deployment obligations.

## Checks and remaining work

Lean tests exercise fragment-family permutations, both flow directions, queue expiry, duplicate and overlapping pieces, guard ordering, namespace reuse, and current-session mismatches.
Importer tests reject late priorities, transport reads, ambiguous bindings, repeated predicates, and inconsistent decision logs.
Passive Python tests cover unchanged fragment bytes, domain-aware provenance, guard transactions, observation metadata, and qualified counter deltas.
Counter deltas do not establish a complete inventory of kernel queues.

This component supplies reusable formal composition before a new native experiment.
Native fragmented campus histories, complete stream correspondence, transparent same-namespace reauthentication, cryptographic packet origin, and broader protocol coverage remain open.
All seven [research programs](ROADMAP.md) and the complete campus landmark remain OPEN.
