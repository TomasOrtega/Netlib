# TCP bytes through the campus gateway

This note records the selected path from an endpoint output to an application read.
The example uses constructed TCP bytes, EAPOL frames, nftables JSON, and route JSON.
It does not send packets or collect native traffic.

## Source rules

TCP startup uses SYN, SYN,ACK, and ACK.
The active endpoint enters ESTABLISHED on the accepted SYN,ACK.
The passive endpoint enters ESTABLISHED on the final ACK.
SYN occupies a sequence position without adding an application byte.
[RFC 9293, sections 3.4 and 3.10.7](https://www.rfc-editor.org/rfc/rfc9293.html#section-3.10.7).

An acceptable acknowledgment can advance the oldest unacknowledged cursor.
Window updates also require fresh sequence and acknowledgment history.
An old ACK does not replace the peer window.
The selected no-option startup derives the absent-option IPv4 MSS of 536.
[RFC 9293, sections 3.7.1 and 3.10.7.4](https://www.rfc-editor.org/rfc/rfc9293.html#section-3.10.7.4).

NAPT changes addresses and transport ports.
The TCP checksum covers the changed addresses through its pseudoheader.
Thus, address translation requires a corresponding TCP checksum update.
The selected rewrite recalculates the checksum from the resulting bytes.
[RFC 3022, sections 4.1 and 4.2](https://www.rfc-editor.org/rfc/rfc3022.html#section-4.1).

The nftables prerouting hook precedes routing.
Forward filtering applies to traffic sent through the host.
Postrouting applies after that traffic passes through the host.
Numeric `iif` rules select an interface index; an exported name can resolve that index.
The rule retains its index meaning after an interface rename.
[nftables manual, hooks and meta expressions](https://www.netfilter.org/projects/nftables/manpage.html).

EAP request and response identifiers support message correlation.
A terminal Success packet does not supply a proof of its authentication method.
The selected guard combines the correlated frames with a supplied method result.
Credential scope, issuer, subject, audience, integrity, and expiry remain separate session tests.
[RFC 3748, sections 4.1, 4.2, and 7.16](https://www.rfc-editor.org/rfc/rfc3748.html#section-4.2).

## Actual execution path

The input supplies local endpoint configuration rather than established endpoint states.
The endpoint constructs each TCP output.
Assignment stores that exact earlier output in a new immutable ticket.
The ticket also records the selected ingress interface lifetime.
Service consumes the ticket once.
An observed input string cannot replace its stored bytes.

At service, the model compares the actual stored forward rules with the current session requirements.
It also compares the actual stored ingress rules with the current attachments.
These comparisons use the authentication prefix at service time.
The configuration identity does not grant permission.
The native rules determine the actual packet result even when a comparison fails.

The actual ingress rule runs before transport admission or conntrack preparation.
If it denies the packet, the tracker and TCP admission history stay unchanged.
If it permits the packet, one conntrack preparation supplies the exact selected entry and direction.
The TCP admission gate uses that same preparation.
An invalid TCP gate does not commit a prepared reply observation.

For accepted ingress, the selected order is:

1. Attach the packet and observe its reply direction.
2. Apply destination translation and select the route.
3. Test TTL when a route exists.
4. Evaluate the forward filter on the destination-translated header.
5. Apply source translation and evaluate the late filter.
6. Confirm a fresh entry only after a successful forward result.
7. Construct the exact output bytes with decremented TTL and valid checksums.

A valid reply observation can remain in an existing entry after a later filter denial.
A dropped fresh SYN does not create a confirmed entry or retain an admission history.
The gate retains an existing admission history only when the actual resulting tracker still contains its selected entry.

The resulting emission derives its TCP `BytePath` from the actual certified rewrite.
The receipt must equal those actual emission bytes.
The input cannot supply a separate arbitrary path or a replacement gateway output.
The receipt then drives the startup or application transition at the opposite endpoint.

## Selected TCP admission

The gateway starts without a TCP history.
It learns the client SYN position and window from the first accepted SYN.
It learns the server SYN position and window from the accepted reply.
The final ACK creates two application lanes from these observed control positions.
The server lane receives its peer window from that final ACK.

Later data must have the next observed sequence position, ACK or PSH,ACK flags, and no options.
The payload limit is 536 bytes.
Acknowledgments must remain within the observed peer byte epoch.
The sender must obey its advertised peer window for nonempty data.
The finite epoch and outstanding-byte bounds prevent ambiguous serial interpretation.
The stored window positions remain within the learned control and application history.

This gate is a selected Lean model.
It does not establish acceptance by the Linux TCP conntrack implementation.
The imported native forward predicates still receive the selected lifecycle classification.
Transport admission and native implementation refinement remain distinct obligations.

## Constructed example

The client socket is `192.0.2.2:41000`.
It opens `203.0.113.2:8080`.
The gateway maps that destination to `198.51.100.2:9000` and maps the client source to `203.0.113.1:40000`.
The reply uses the inverse mapping through the same confirmed entry.
The imported route bindings select the client and server roles.

The trace consumes the selected EAP observations and installs a scoped credential.
It stages the current client and server ingress attachments and installs their numeric guard.
It then runs startup through the gateway in each direction.
The active application state appears before the passive application state.
Their empty application buffers and cursors come from those actual startup receipts.

The client writes and sends `abc`; the server receives and reads `616263`.
The server writes and sends `xyz`; the client receives and reads `78797a`.
The return ACK passes through the same gateway path.
These reads exhibit nonempty application bytes with earlier write, output, assignment, service, and receipt events.

The client then queues `def` while access is permitted.
The trace consumes Logoff and installs the deny forward configuration and deny ingress guard.
Service emits no packet for that old ticket.
The existing confirmed NAT entry remains present, including its reply observation.
The result does not depend on clearing the cached entry.

The stale-allow variant retains the actual permit rules after Logoff.
It computes the resulting packet emission and reports failed current-policy comparisons.
It does not replace those rules with a generated deny policy.
The wrong-route variant likewise retains the actual emission and reports a route-role mismatch.
Observed byte mismatches affect comparison results without changing the computed bytes.

## Evidence and limits

The independent Python oracle parses the constructed native source predicates and routes.
It uses address and port interval partitions for policy comparison.
Its TCP calculations use signed serial coordinates and construct the IP and TCP checksum fields directly.
The frozen fixtures include exact endpoint outputs, gateway emissions, state, decisions, and read bytes.
The compiled CLI helper compares these independent expectations with the Lean report.
Python unit tests do not compile or execute Lean.

The static artifacts are:

- `scripts/campus_tcp_reference.py`: independent policy, transport, and event calculations.
- `scripts/test_campus_tcp_reference.py`: component and frozen-fixture tests.
- `scripts/check_campus_tcp_examples.py`: compiled CLI comparison and strict input tests.
- `examples/campus-tcp/trace.json`: the authorized exchange and queued Logoff denial.
- `examples/campus-tcp/fixtures.json`: 16 execution cases and 18 input-error cases.
- `examples/campus-tcp/guards.json`: constructed native ingress rule sources.
- `examples/campus-tcp/configs.json`: constructed native forward, late-filter, and NAT sources.
- `examples/campus-tcp/routing.json`: constructed native route input and role bindings.

The model derives byte origin within the supplied execution history.
It does not derive physical transmission, physical delivery, genuine capture, or faithful native installation.
Method acceptance, credential integrity, local ISS choices, local send limits, and physical interface meaning remain supplied facts.
The connection instance, finite epochs, and quiet startup boundary remain explicit.
Startup copies cannot serve as application delivery origins.

This first path uses one gateway and one selected TCP flow.
It excludes loss recovery, reordering, timers, reset and close processing, MSS options, scaling, fragmentation, and TCP state replication.
It leaves the existing UDP replication restriction intact.
Revocation prevents new selected gateway emissions after the current deny installation.
It does not erase bytes that the receiver already buffered.

All seven research programs remain OPEN.
Wireless enforcement, failover, upgrades, native TCP refinement, and the full campus demonstration need further work.
