# Bounded receive gaps and actual byte origins

This note states the selected receive rules and independent evidence.
The oracle uses a byte-position map, actual packet metadata, and local clock readings.
It does not execute Lean, transmit traffic, or collect captures.

## Primary constraints

RFC 9293 recommends holding data that starts above the receive cursor.
Its processing flow retains new data in sequence and processes queued segments before generating an aggregate ACK.
It describes later processing through an idealized segment that begins at the receive cursor.
The receive window is a sequence range, and its offered right edge should not move left.
[RFC 9293, sections 3.8.6 and 3.10.7.4](https://www.rfc-editor.org/rfc/rfc9293.html#section-3.10.7.4).

RFC 5681 recommends immediate ACKs above a gap and after an arrival fills any part of a gap.
It recommends at most one ACK per incoming segment, except for application-driven window updates.
A packet that releases earlier held bytes remains one arrival.
The selected two-RMSS counter uses novel input bytes; it does not count held bytes again when they are released.
The third qualifying duplicate ACK still requires the omitted fast-recovery actions in the selected sender profile.
[RFC 5681, sections 3.2 and 4.2](https://www.rfc-editor.org/rfc/rfc5681.html#section-4.2).

Receiver SWS control holds the right edge until withheld space reaches its selected threshold.
The suggested threshold uses half the capacity and own effective outgoing MSS.
It does not use the peer's receive MSS for that calculation.
[RFC 1122, section 4.2.3.3](https://www.rfc-editor.org/rfc/rfc1122.html#section-4.2.3.3).

Timeout recovery retries the earliest outstanding data and backs off the timer.
Karn exclusion prevents an ambiguous retransmitted range from supplying an RTT sample.
The selected recovery model excludes a cumulative sample if any fully retired original record was retried.
[RFC 6298, sections 3 and 5](https://www.rfc-editor.org/rfc/rfc6298.html#section-3).

## Retained packets and processing order

Above-gap data retains its original header, segment, and local receipt time.
The initial check uses tuple, selected control scope, and sequence acceptability.
ACK-bit, ACK-range, ACK-retirement, and peer-window effects wait until the retained run becomes contiguous.
Ordinary empty ACK input keeps its existing immediate path.
This is a selected interpretation of the receive flow, without a full TCP conformance claim.

An exact queued copy retains the first bytes and metadata.
It consumes no new storage, but it can request immediate feedback from that actual arrival.
A later copy cannot replace the first ACK field, window, or receipt clock.
Conflicting spans, partial overlap, right-edge trimming, and omitted control processing remain explicit scope outcomes.
They are not RFC-mandated drops.
The new receive class is automatic; it needs no activation event.

Release processes every contiguous run before issuing one cause for the new receipt.
The batch publishes no partial core, store, ACK, or timer changes if a header check fails.
An earlier queued-header failure produces `queuedHeader` scope and identifies that actual retained receipt.
A current packet's own header failure keeps its ordinary input rejection or challenge outcome.
That ordinary challenge can issue feedback without publishing any partial release effects.
The diagnostic distinguishes a committed queued receipt from an uncommitted proposed current tag.
Header and recovery failures retain their separate check kinds.

RTT sampling uses the retained ACK's actual arrival clock.
Timer restart uses the current processing clock.
The endpoint clock does not move backward when an older header is processed.
A raw negative case checks an ACK retained before the acknowledged data was sent; it cannot create a negative RTT sample.
Receipt order must hold for every touched send record, including partial and retried records.
The first failed run wins, including when a later run has a different header error.

## Independent storage and window accounting

The oracle maps each unique stream position to a byte value, receipt identity, and payload index.
Signed serial distance selects one bounded receive epoch, including wrapped sequence origins.
Packet identities are allocated by actual receive operations.
Input cannot supply a queue, receipt identity, release result, or receipt clock.

Let `C` be capacity, `U` ordered unread bytes, `O` unique held bytes, and `W` the offered span.
Physical free storage is `C-U-O`.
Reservation space is `C-U`.
The unfilled portion of the offered span is `W-O`.
Its bound is `W-O <= C-U-O`, with all held positions unique and inside the offered span.
These equations are derived design conditions.
They do not change the RFC's sequence-window definition.

Storing 400 bytes above a gap changes physical free storage from 4096 to 3696.
It leaves the offered width at 4096 and the cumulative frontier unchanged.
A later 400-byte prefix can release 800 ordered bytes while consuming only 400 new storage bytes.
The SWS reduction is `C-U-W`; held occupancy cancels from that value.
The candidate width is `C-U` when the threshold is met, and the held width otherwise.
Reports keep physical free storage and reservation space separate.

A read consumes only ordered unread bytes.
It cannot cross a missing prefix to reach held bytes.
A zero-byte read creates no update cause.
The ACK counter uses novel input bytes, while the receive cursor advances by the released length.
Thus, decision `received` and cause `bytes` can be 400 when `releasedHex` contains 800 bytes.

## Connected campus trace

[The trace](../../examples/tcp-receive-gaps/trace.json) has 97 events, 14 actual endpoint outputs, and 15 gateway service results.
It uses the current imported campus configuration, checked startup, asymmetric MSS, recovery clocks, and ACK profile.

The client sends two different 400-byte payloads within its 800-byte flight bound.
Primary service observes both in sequence order.
Only the suffix arrives first, at event 38.
The server retains 400 bytes, exposes no ordered data, and generates immediate cumulative feedback without shrinking its offered edge.

An explicit copy action creates the old ingress packet used during drain.
The actual gateway checkpoint is installed at event 49.
The held suffix and its receipt metadata remain at the host through pause, drain, installation, route changes, and fencing.
They are not part of the copied NAT image.
At event 55, the client retries its actual first 400-byte original range.
Standby service emits that retry, and receipt 59 fills the gap.
One cause covers the new arrival while the ordered frontier advances by 800.
The released run identities are the current prefix first and the earlier suffix second.
An actual cumulative ACK retires both original records without an RTT sample.
Read 65 returns 800 bytes once.

The reverse path sends 600+600 bytes within the server's 1200-byte flight bound.
A held suffix and an actual retry release 1200 bytes at event 84.
Current Logoff precedes the buffered read at event 93.
The resulting window update is generated locally at event 94, but current gateway service denies its delivery at event 96.
Timely local generation does not establish peer delivery or eventual progress.

The first positive trace reorders delivery after gateway service.
The [sparse gateway extension](TCP_SPARSE_ADMISSION.md) now covers selected ingress reordering.
Its corpus retains the former fresh-ingress input with its supported continuation.

## Receipt-time witness and variants

[The second actual-source trace](../../examples/tcp-receive-gaps/deferred-clock.json) separates ACK arrival from processing.
The helper requires it to equal the existing receipt-clock case input; it adds no new case.
An above-gap packet arrives at server time 150 with an advancing reverse ACK.
An earlier primary prefix emission fills the gap at server time 1100, after gateway transfer.
Its old ACK retires no bytes; the queued header then retires 200.
The RTT sample records arrival time 150 and an elapsed 50 ms.
The remaining timer restarts at current time 1100 with deadline 2100.
Using the gap-release time as the sample's arrival would fail this check.

Other traces cover wrapped startup, exact queued copies, and a one-gateway partial gap fill.
The partial case releases 200 bytes first, retains a 400-byte suffix, and releases the remaining 600 after another actual retry.
A current denial of the gap retry leaves the suffix stored and unreadable.
An authorized earlier gateway emission can arrive after Logoff and release bytes under its original service-time evidence.
A cumulative ACK without a receipt remains pending while a second real retry occurs.
It does not append old bytes or replace their first receipt origins.
Omitted events do not prove packet loss; the [custody trace](../PACKET_CUSTODY.md) uses explicit drops.

## Corpus and audit

[The fixtures](../../examples/tcp-receive-gaps/fixtures.json) contain 13 campus cases and 17 raw endpoint cases.
They also contain five campus input errors and five raw input errors.
Raw seeded cases check receiver mechanics; they do not establish startup or peer-write provenance.
The campus cases use actual generated peer packets and gateway emissions.

The audit derives each released byte from its actual receipt and payload index.
It then checks the earlier peer output, original send range, accepted write, assignment, and gateway service.
It requires writer < original send <= attempt < receipt <= release < read.
Local timing checks remain within one endpoint clock context.
The audit checks actual packet ACK coverage, one-use credit, offered edges, queued header order, and retained receipt clocks.

The optional `receiveGapAssurance` field appears only after an actual gap.
Its scope is `ordered-receive-storage`.
Checked and pending reports count actual receipt allocations, final held bytes, released bytes, and read bytes for each endpoint.
The status is `pending` while either final store holds bytes, and `checked` when both stores are empty.
Pending evidence retains source, storage, and prefix facts without an eventual-delivery claim.
Actual noncompliance produces `failed` with its reason and no success counts.
The helper requires this exact object, rejects an absent gap object, and checks its absence on all 94 valid legacy campus rows.
A stale-permit-after-Logoff variant checks failure after both actual gaps have occurred.

Automatic custody adds identity and resolution fields to all campus reports.
Legacy cases with repeated assignment or delivery now include explicit copy actions.
Expected operation indices change while packet bytes and host-clock readings stay the same.
Three former outside-profile inputs move to the new corpus with their actual continuation outcomes.
The ACK case `actual-out-of-order-data-remains-outside-profile` is now the input error `out-of-order-receipt-reaches-later-emission-mismatch`.
Its packet bytes are retained, and its explicit copy action permits it to reach the later actual-emission mismatch.
The raw in-order `tcp-receive` projection and its fixtures remain unchanged.
Expected packets and state come only from the independent Python model.
No Lean report supplies an expected value.

Physical delivery, connection identity, native clock correspondence, and imported deployment correspondence remain external conditions.
Finite traces do not prove fair scheduling, bounded network delay, or eventual gap filling.
Partial-overlap trimming, broader congestion control, close processing, and native TCP refinement remain OPEN.
All seven programs and the full campus demonstration remain OPEN.
