# Timed TCP ACK reactions and receiver windows

This note connects receiver feedback to actual local output and campus packet history.
The independent oracle uses static packets, stream coordinates, and local clock readings.
It does not execute Lean, send traffic, or collect captures.

## Primary rules

RFC 9293 requires delayed ACK delay below 0.5 seconds.
It recommends an ACK for each second full segment or twice RMSS in new bytes.
RMSS is the receiving endpoint's own advertised MSS or its default.
The specification also requires ACK aggregation when processing a series of queued segments.
Established processing permits piggybacking without undue delay.
Unacceptable sequence input receives an empty ACK and is dropped.
[RFC 9293, sections 3.8.6.3 and 3.10.7.4](https://www.rfc-editor.org/rfc/rfc9293.html#section-3.8.6.3).

RFC 5681 makes the second-full-segment rule a SHOULD and the delay bound a MUST.
It recommends ACKs at least every second segment when smaller packets could otherwise stretch feedback.
It recommends immediate ACKs for out-of-order data and gap filling.
It limits generated ACKs to one per incoming segment, except actual window updates caused by application consumption.
[RFC 5681, section 4.2](https://www.rfc-editor.org/rfc/rfc5681.html#section-4.2).

Receiver silly-window avoidance is mandatory.
The suggested algorithm holds the offered right edge until withheld space reaches the smaller of half the buffer and own outgoing MSS.
The receiver then offers all free space.
The specification explicitly uses the receiver's own effective outgoing MSS for this threshold.
This value differs from the receive MSS used for delayed-ACK byte counts.
[RFC 1122, section 4.2.3.3](https://www.rfc-editor.org/rfc/rfc1122.html#section-4.2.3.3).
[RFC 9293 retains this receiver algorithm](https://www.rfc-editor.org/rfc/rfc9293.html#section-3.8.6.2.2).

A zero-window receiver acknowledges arriving data probes with its current cursor and window.
Reliable reopening also depends on sender probing, because a window update can be lost.
Receiver window updates alone do not prove that the peer will learn of reopening.
[RFC 9293, section 3.8.6.1](https://www.rfc-editor.org/rfc/rfc9293.html#section-3.8.6.1).

The selected RFC 5961 DATA check discards an unacceptable ACK and sends a response.
Its separate challenge-ACK throttling guidance is a SHOULD and recommends a tunable limit.
The selected timed profile stops before omitted challenge throttling.
[RFC 5961, sections 5.2 and 7](https://www.rfc-editor.org/rfc/rfc5961.html#section-7).

## Selected timing and credit boundary

Timed ACK mode requires the existing recovery clock.
Activation derives own receive MSS from the checked handshake seed.
It accepts no replacement RMSS, timer, credit, owed cursor, or completion flag.
Campus activation occurs before actual application send or receive operations.
Thus, its initial full offered window has startup evidence.

A delayed cause at local time `t` is due at `t+499` milliseconds, inclusive.
This selected integer bound satisfies the strict delay limit.
An immediate cause is due at the current local time.
Coalescing retains actual causes and the earliest due time.
A later receipt cannot postpone the first cause.
The selected counter counts packets at least as large as own RMSS.
Two such packets, or twice RMSS in new bytes, make the group immediately due.
Smaller packets can coalesce while retaining the first deadline.
This follows the explicit RMSS-byte alternative without assuming knowledge of the peer's outgoing MSS.
Each endpoint keeps its own clock domain.
Global event indices record causal order rather than elapsed time.

Accepted new data grants a response cause.
A supported sequence rejection with a cumulative ACK request grants an immediate cause without adding application bytes.
An ordinary accepted pure ACK grants none.
A successful SWS window release can grant a cause from the actual application read.
A zero-length read grants none.

One actual response retires the whole covered group.
Unused per-input credit cannot fund a second pure response.
An independently permitted new send or retry can discharge a group through its actual ACK field.
Its data transmission does not create extra pure-ACK credit.

The ACK-only dispatcher checks pending credit and due time, then constructs the output.
Pure explicit ACK output in timed mode also requires credit.
Local output denial preserves the cause and deadline.
A clock cannot advance past the pending due time while retaining checked timed behavior.
Simultaneous RTO processing remains a separate operation.
An actual retry can carry the ACK first, leaving no credit for another pure response.

This model selects one receipt per processing batch.
It does not establish a native implementation's queued-batch processing or physical dispatch latency.
A finite prefix with pending causes does not receive a closed timed assurance.
It can retain its separate application-byte assurance.

## Independent receiver-window calculation

The oracle tracks the accepted-byte frontier and offered right edge in unbounded stream coordinates.
The current offered width is the edge minus the frontier.
Free space is physical capacity minus unread bytes.
Withheld space is free space minus offered width.

Receiving data advances the frontier and consumes buffer space while preserving the edge.
An application read frees storage without moving that edge.
The selected integer release threshold is `min(ceil(capacity/2), own outgoing MSS)`.
At or above the threshold, an output can offer all free space.
Below it, every output retains the old edge, including piggybacked ACKs.
Only a successful actual output commits a larger offered edge.
Denied output leaves the pending opening intact.

Receive acceptance uses the offered width, bounded by physical free space.
It cannot use space withheld after a small read.
Window-update credit requires a positive offered-edge advance.
Capacity zero and zero-length reads cannot manufacture credit.
Wire sequence fields are modular projections of these coordinates.
The application history supplies the separate finite-epoch bound.

With capacity 4096, the asymmetric startup provides useful distinct values:

| Endpoint | Own receive MSS | Effective outgoing MSS | SWS threshold |
| --- | ---: | ---: | ---: |
| Client | 1200 | 800 | 800 |
| Server | 800 | 1200 | 1200 |

The recovery profile allows at most one outgoing MSS in flight.
Two smaller sends can exercise receive coalescing within that bound.
Two full outgoing-MSS segments before an ACK require a different focused test boundary.
The connected witness must not assume an inconsistent congestion window to exercise a threshold.

## Connected evidence boundary

The connected evidence retains checked startup and native-format policy imports.
It retains actual endpoint output, immutable assignment, current gateway processing, exact receipt, and application read history.
Timed reaction evidence must use those same endpoint chains.
An ACK-success Boolean or separately supplied compatible output cannot replace actual discharge.

A gateway transfer leaves local endpoint obligations and clocks intact.
An ACK generated after resume enters the actual standby pipeline.
Sender retirement still requires its exact later receipt.
A timely local ACK can be lost, delayed, or denied at the gateway.
Those outcomes do not undo local generation or establish delivery.

Current Logoff denial applies at gateway service time.
Previously received bytes remain readable after that denial.
Stale allow rules retain their actual packet outcome and fail the current-policy comparison.
They must not be rewritten into a fictional drop.

Scope tests must include duplicate data without duplicate application bytes, repeated dispatch, and ordinary pure-ACK input.
They must distinguish own receive MSS from outgoing MSS and distinguish free space from offered window.
Boundary cases include odd buffer capacity, threshold accumulation, zero-window reopening, and serial wrap.
Timing cases include the last permitted millisecond, a forbidden clock jump, local denial, and delayed network delivery after generation.

## Constructed campus witness

[The trace](../../examples/tcp-ack/trace.json) has 154 operations, 21 endpoint outputs, and 22 gateway service results.
It reuses the existing checked startup and native-format campus configuration inputs.
The client sends two 400-byte segments at local times 100 and 150.
Their server-side causes coalesce without postponing the first deadline.
The server's actual 1200-byte output at time 150 piggybacks the cumulative ACK and discharges both causes.

The client's resulting data-ACK obligation remains pending during gateway transfer at local time 200.
An explicit `copyPacket` action copies an earlier actual output before pause.
Assignment consumes that new ingress identity.
Its service during drain advances the source cut from six transitions to seven.
The final checkpoint preserves that actual cut and the directional MSS offers.
Installation leaves the endpoint obligation and its due time 649 unchanged.
Dispatch at 648 rejects as early; actual dispatch at 649 traverses standby and retires the server's outstanding range.

A later 800-byte client output receives gateway service but no receipt.
Its receiver-link identity remains pending.
Retries occur at 1700 and 3700.
The first recovery ACK is generated at 2199 and served, but its receiver-link identity also remains pending.
The second data receipt is wholly old and creates an immediate cumulative response without additional application bytes.
The server's later 1200-byte emission has no receipt and uses retries at 5297 and 8291.
Its first recovery ACK is also left pending.
Omitted receipts do not prove packet loss.
The [packet-custody trace](../PACKET_CUSTODY.md) uses explicit data and ACK drops on the actual recovery path.
Both directions retain their original byte ranges and Karn ambiguity.

The server then reads 1199 bytes, below its 1200-byte SWS threshold.
Its next data output advertises 2496, although physical free space is 3695.
A further one-byte read grants actual window-update work.
The selected output advertises 3696.
The client's separate 799-byte read stays below its 800-byte threshold.
Its pending data ACK still advertises 496 rather than physical free space 1295.

Logoff and current forward and ingress denial precede service of that timely local ACK.
The gateway emits no packet.
Subsequent buffered reads remain valid, and the client's actual read-origin window update also reaches a gateway denial.
The server reads 1600 unique bytes, and the client reads 3600.
Those read prefixes include primary and standby delivery.
The final client ledger has five causes and five discharges.
The server ledger has five causes and four discharges because its first response covered two causes.
The server retains 1200 unacknowledged bytes; denied ACK service does not establish sender retirement.

[The independent fixtures](../../examples/tcp-ack/fixtures.json) contain 24 traces and 17 input-error cases.
They include default MSS, asymmetric offers, one gateway, sequence wrap, and a checkpoint staged before pause.
They exercise zero-window duplicate feedback, accumulated SWS reopening, and both ACK-versus-RTO operation orders.
Separate cases preserve stale-allow output and reject late activation, supplied state, supplied credit, and unmatched receipts.
An unacceptable ACK-only packet can still create sequence feedback.
The no-loop claim concerns ordinary accepted pure ACKs.

[The comparison helper](../../scripts/check_tcp_ack_examples.py) checks full independently calculated steps and actual packet bytes.
Its audit checks earlier actual cause issuers, strict issuer-before-output order, single-use credit, same-clock deadlines, and offered-edge transitions.
It also retains the existing retry-range and application-byte audit.
The automatic custody extension adds packet identities and one-use resolution to the same replay.
Legacy cases that repeat an assignment or delivery now contain explicit copy actions.
Expected custody fields and causal operation indices are updated; packet bytes and host-clock readings are retained.
The [receive-gap extension](../TCP_RECEIVE_GAPS.md) adds the automatic receiver and moves newly covered geometry cases into its corpus.

General receiver conformance requires more than this selected profile.
Gateway-ingress reordering, overlap storage, challenge throttling, sender persist, close, general congestion control, native correspondence, and liveness remain OPEN.
All seven research programs and the full campus landmark remain OPEN.
