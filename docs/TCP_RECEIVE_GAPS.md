# Bounded TCP receive gaps

The endpoint can hold non-overlapping future payloads and release them when a gap closes.
Each run retains its actual receipt identity, packet header, payload, and local receipt time.
An exact queued duplicate preserves the first copy.
Input cannot supply queued bytes, receipt identities, or a reassembly-success flag.

This behavior is automatic for endpoint and campus replay.
The lower-level `tcp-receive` command keeps its documented in-order projection.
Partial overlap, conflicting payload copies, and receive-window trimming have explicit scope stops.

## Storage and window reservation

Let `U` be ordered unread bytes and `O` be unique held bytes.
Physical free space is `capacity - U - O`.
The reservation available for the receive window is `capacity - U`.
The offered window spans sequence positions, including positions whose bytes are already held.

A future 400-byte receipt uses 400 bytes of storage without advancing `RCV.NXT`.
It does not move the offered right edge to the left.
An exact queued duplicate uses no additional storage.
When a missing 400-byte prefix arrives, it can release 800 ordered bytes.
Only 400 of those bytes are new storage.

`State.StorageValid` states the sparse-storage bounds separately from the existing endpoint buffer predicate.
`ReceiveStore.State.Valid` checks sorted disjoint spans, receipt identities, occupied storage, and the reserved span.
Its success theorem derives the storage and post-state checks for every supported input span.
The caller does not supply a post-state certificate.

Receiver SWS uses reservation space outside the offered span.
An application read can release that reservation after the selected threshold.
The existing [ACK rules](TCP_ACK.md) still control the actual output that commits a larger edge.

## Packet order and deferred headers

Initial receipt processing checks the tuple, selected control and option scope, and sequence acceptance.
Nonempty future data retains its ACK and window fields for later processing in sequence order.
Empty pure ACKs use the existing immediate processing path.

The receiver processes all contiguous runs before it creates one receive ACK cause.
Above-gap input and gap filling request immediate feedback.
A gap-filling packet creates one cause even when it releases bytes from several earlier packets.
The cause counts novel incoming bytes; the receive cursor advances by released bytes.

Queued headers are checked against the state reached by earlier released headers.
Their cumulative ACK counts can differ from a calculation against the original state.
For example, ACKs for 400 and 800 bytes can retire 400 bytes each in one ordered batch.

The selected batch is transactional.
A failed queued header publishes no partial buffer, store, ACK-retirement, or window update.
Its diagnostic retains the original receipt and the underlying header failure.
The `queuedHeader` scope identifies an earlier held header, rather than blaming the fresh gap-filling packet.
A fresh packet's own header failure keeps the ordinary rejection or challenge interpretation.

This order follows the selected flow in [RFC 9293, section 3.10.7.4](https://www.rfc-editor.org/rfc/rfc9293.html#section-3.10.7.4).
Immediate gap feedback uses the recommendations in [RFC 5681, section 4.2](https://www.rfc-editor.org/rfc/rfc5681.html#section-4.2).
Transactional failure is a selected profile scope, rather than a complete invalid-queue recovery procedure.

## Receipt time and processing time

A queued ACK can arrive before the missing prefix permits its processing.
Its RTT sample uses the original receipt time.
Timer restart uses the current processing clock.
The clock does not move backward during this operation.

An ACK received at 150 ms and processed at 1100 ms retains 150 ms in its sample.
If data remains outstanding, the new deadline starts at 1100 ms plus the resulting RTO.
The receipt cannot precede the original send of any range it retires.
This check also covers partial ACKs and ranges excluded from measurement by Karn's rule.
Retransmitted data still supplies no ambiguous RTT sample.
The [recovery guide](TCP_RECOVERY.md) states the remaining timer and congestion limits.

## Byte origins

`ReceiveStoreHistory` links each held or released run to the operation that allocated its receipt identity.
It proves the original payload index and absolute stream position for each released byte.
A duplicate cannot replace the source identity, header, or receipt time of a queued run.

The input packet remains a whole actual packet with its own gateway byte path.
The released prefix can combine bytes from several such packets.
No synthetic packet stands in for that combined prefix.
The application history must use released bytes for ordered-buffer conservation and cursor advancement.
Its incoming-payload history remains separate.

Gateway transfer preserves the endpoint's stored runs and clocks at the host.
The [gateway checkpoint](CAMPUS_TCP_TRANSFER.md) copies the gateway's actual tracking and admission history.
It does not carry host receive buffers.

## Report fields

After an actual future receipt, endpoint state includes `receiveStore`.
It reports the frontier, next receipt identity, held spans, occupied bytes, physical free space, and reservation free space.
The ACK advertisement reports `physicalFree` and `reservationFree` separately.
Earlier in-order reports retain their existing fields.

Receive steps also show `reassembly`.
`novelBytes` is the unique byte count from the current input.
`releasedHex` and `releasedRuns` describe the ordered release.
`headers` retains the actual per-header ACK retirement counts.
A failed transaction has no committed receipt identity or released bytes.
Its failure detail identifies the original header and checked prefix state.
The source field distinguishes a committed queued receipt from the current input's proposed receipt tag.

Campus reports add `receiveGapAssurance` after an actual future receipt.
Its scope is `ordered-receive-storage`.
`pending` retains checked storage bounds, held receipt sources, and application-prefix evidence.
`checked` also requires both final held stores to be empty.
The report counts actual receipt identities, held bytes, released bytes, and read bytes for each host.
A noncompliant trace has failed assurance.

`CampusTCPGapFacts.Evidence` derives these facts from the actual campus trace and checked startup.
Each read-byte theorem links the byte to its earlier release, original receipt, gateway service, peer output, and application write.
The order is write, original send, attempt, receipt, release, and read.
Receipt and release can be the same operation.
The two hosts retain their own local clocks.

The covered reordering occurs after actual gateway service.
Current gateway ingress admission still requires its selected sequence order.
This profile does not establish arbitrary reordering before the gateway.
General overlap handling, fast recovery, native correspondence, and eventual delivery remain OPEN.
All seven research programs and the full campus demonstration remain OPEN.
