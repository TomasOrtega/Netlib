# Sparse gateway admission and actual byte sources

Source cut: `1816bb875fae6485966b2419ca6eb3ad922a93bf`.
Review date: 2026-11-05.
This report uses source inspection and primary RFC text.
No build, packet transmission, or native experiment was run.

## Decision

Choose bounded sparse gateway admission as the next protocol step.
The gateway must record observation coverage and forward each accepted packet immediately.
Do not add endpoint receive buffering to the gateway.

This choice removes a sequence-order assumption from the current campus path.
It connects existing host gap handling to loss and reordering before gateway service.
The connection includes actual bytes, current policy, exact checkpoint transfer, timers, and application reads.
This is a design judgment from the source dependencies below.

Packet custody and bounded progress are a larger architecture gap.
They can be the next architecture project under an explicit ordered-ingress profile.
Sparse admission is necessary for a useful extension of that project through pre-gateway prefix loss and reordering.
It is not necessary for every honest progress theorem.

All seven programs and the complete campus remain OPEN.
The roadmap states that limit.
[Roadmap](https://github.com/TomasOrtega/Netlib/blob/1816bb875fae6485966b2419ca6eb3ad922a93bf/docs/ROADMAP.md#L13).

## Source boundary at the recorded cut

`Admission.Lane` has one `observed` count.
`Lane.next` adds that count to the sequence base.
`Lane.outstanding` subtracts the cumulative ACK count.
`Lane.Valid` bounds this span to 65535 bytes and one short sequence epoch.
Thus the count also acts as a contiguous source frontier.
[Lane definitions](https://github.com/TomasOrtega/Netlib/blob/1816bb875fae6485966b2419ca6eb3ad922a93bf/Netlib/Protocol/TCP/Admission.lean#L23).

`DataAllowed` requires `segment.sequence = sender.next`.
`RepeatedAllowed` permits an exact slice of an earlier observation for the same entry and direction.
`RangeFrom` checks the payload bytes, not only the sequence and length.
A first observation above a hole has neither admission path.
[Data and repeat admission](https://github.com/TomasOrtega/Netlib/blob/1816bb875fae6485966b2419ca6eb3ad922a93bf/Netlib/Protocol/TCP/Admission.lean#L194).

Fresh admission advances `observed` by payload length.
Repeat admission preserves both observed frontiers and appends one actual observation.
ACK and window checks still use the current packet.
These are different effects and must remain different after sparse admission.
[Phase update](https://github.com/TomasOrtega/Netlib/blob/1816bb875fae6485966b2419ca6eb3ad922a93bf/Netlib/Protocol/TCP/Admission.lean#L290), [repeat facts](https://github.com/TomasOrtega/Netlib/blob/1816bb875fae6485966b2419ca6eb3ad922a93bf/Netlib/Protocol/TCP/AdmissionRecoveryFacts.lean#L78).

Current positive gap traces reorder receipt after gateway service.
The primary first observes both original ranges in sequence order.
The corpus has a separate unsupported case for fresh ingress reordering.
[Trace account](https://github.com/TomasOrtega/Netlib/blob/1816bb875fae6485966b2419ca6eb3ad922a93bf/docs/research/TCP_RECEIVE_GAPS.md#L92), [current negative case](https://github.com/TomasOrtega/Netlib/blob/1816bb875fae6485966b2419ca6eb3ad922a93bf/examples/tcp-receive-gaps/fixtures.json#L42458).

## Comparison

| Candidate | Connected gain | Main source dependency | Assessment |
| --- | --- | --- | --- |
| Sparse gateway admission | Later packets can pass before an unseen lower range. A transferred ledger can admit the missing range on standby. | Replace the contiguous `Lane.observed` interpretation. Preserve exact source bytes, ACK limits, window freshness, and checkpoint equality. | Strongest next protocol seam. It removes a path-order assumption across the existing campus proof. |
| Fast retransmit and recovery | Actual duplicate ACKs can cause recovery before timeout. A larger flight can exercise ordinary multi-segment loss. | Replace `cwnd = smss` and `flight ≤ smss`. Add recovery phase, congestion updates, transmission permission, and actual retry provenance. | A substantial later endpoint project. Removing the third-ACK stop alone is insufficient. |
| Reliable close | The model can cover application completion and retained connection lifetime. | Add control positions, endpoint close phases, FIN acknowledgment, retry state, and TIME-WAIT. Extend gateway admission and transfer. | Necessary for a complete connection. It creates a wider lifecycle seam before the current packet-order assumption is removed. |

The table gives design judgments.
The source and standards facts below support them.

RFC 9293 recommends holding out-of-order endpoint data.
Its processing order retains new data in sequence and processes queued segments before aggregate ACK generation.
These are endpoint rules.
They do not require a forwarding gateway to hold packets.
[RFC 9293, section 3.10.7.4](https://www.rfc-editor.org/rfc/rfc9293.html#section-3.10.7.4).

RFC 5681 defines a duplicate ACK using more than its ACK number.
The test includes outstanding data, no data or SYN/FIN, and an unchanged advertised window.
Its fast-retransmit algorithm uses three duplicate ACKs and connected congestion updates.
[RFC 5681, sections 2 and 3.2](https://www.rfc-editor.org/rfc/rfc5681.html#section-3.2).

Netlib already checks qualifying ACKs against the last accepted advertised window.
The third qualifying duplicate ACK stops replay.
The recovery invariant fixes `cwnd` to one SMSS and bounds total flight by one SMSS.
These limits still permit several smaller original segments.
[Duplicate classification](https://github.com/TomasOrtega/Netlib/blob/1816bb875fae6485966b2419ca6eb3ad922a93bf/Netlib/Protocol/TCP/Endpoint.lean#L305), [recovery state and limit](https://github.com/TomasOrtega/Netlib/blob/1816bb875fae6485966b2419ca6eb3ad922a93bf/Netlib/Protocol/TCP/Recovery.lean#L31).

Fast recovery can first use reordering after gateway service.
Sparse gateway admission is therefore not a logical prerequisite for that narrower result.
It is a prerequisite when later original packets must pass an unseen missing prefix at gateway ingress.
This follows directly from the present `DataAllowed` equality.
[Admission condition](https://github.com/TomasOrtega/Netlib/blob/1816bb875fae6485966b2419ca6eb3ad922a93bf/Netlib/Protocol/TCP/Admission.lean#L194).

FIN occupies one sequence position after data.
Close must preserve ordered delivery and independent send/receive completion.
The active closer retains TIME-WAIT for twice MSL.
Repeated FINs need ACK handling and timer restart.
A FIN flag alone does not implement these rules.
[RFC 9293, sections 3.4, 3.6, 3.10.4, and 3.10.7.4](https://www.rfc-editor.org/rfc/rfc9293.html#section-3.6).

Current established state equates the unacknowledged sequence span with stored application bytes.
Its control gate stops on FIN, SYN, and RST.
The campus event type has no close event.
Thus reliable close needs a control-position model beyond the present byte invariant.
[Established state and controls](https://github.com/TomasOrtega/Netlib/blob/1816bb875fae6485966b2419ca6eb3ad922a93bf/Netlib/Protocol/TCP/EstablishedReceive.lean#L30), [campus events](https://github.com/TomasOrtega/Netlib/blob/1816bb875fae6485966b2419ca6eb3ad922a93bf/Netlib/Check/CampusTCPModel.lean#L315).

## Sparse admission contract

The following points are requirements for this milestone.
The independent Python evidence below does not establish Lean completion.
The lane and report interfaces below keep the ordinary in-order fields unchanged.

Keep these values separate:

- The greatest observed end position.
- The contiguous covered prefix.
- Unique observed byte count.
- Cumulative acknowledged position.
- Current peer window and its freshness coordinates.
- Exact observed payload ranges with entry and direction sources.

A high end position must not prove knowledge of bytes in a hole.
An ACK that passes a hole must not gain support from that high end alone.
The selected admission contract should require coverage of its cumulative ACK prefix.
This is a gateway evidence rule, not a claim that RFC 9293 specifies firewall admission.

Check new data against its sequence end and the current advertised right edge.
Do not replace that check with a unique-byte count.
RFC 9293 defines the window in sequence space.
[RFC 9293, section 3.8.6](https://www.rfc-editor.org/rfc/rfc9293.html#section-3.8.6).

Classify an unseen disjoint lower range as new coverage.
It must not require an earlier observation of its own payload.
Keep the exact earlier-byte requirement for repeated ranges.
Retain explicit stops for unsupported mixed overlaps and conflicting copies.
Do not infer missing bytes from later packet positions.

Specify empty ACK sequence admission separately.
The present equality also constrains pure ACKs.
A new data-only branch would leave that interface decision unresolved.
Preserve the selected bounded epoch and document any remaining empty-ACK restriction.
[Current data profile](https://github.com/TomasOrtega/Netlib/blob/1816bb875fae6485966b2419ca6eb3ad922a93bf/Netlib/Protocol/TCP/Admission.lean#L135).

Each novel disjoint range gets the next per-lane first-source identity.
Its metadata is the actual global observation index.
An exact contained repeat retains that original source and leaves the next identity unchanged.
No coverage or source identity comes from input.

The selected empty-ACK rule permits a distance from the lane base at most its greatest observed end, including either endpoint.
It adds no coverage and consumes no data-window space.
The earlier SYN position and positions beyond that end remain outside the selected epoch.

## Proof and interface dependencies at the cut

These dependencies describe the recorded source cut, before this milestone.

1. `Admission.Lane.Valid`, `WindowHistory`, `acknowledged_history`, `DataAllowed`, `RepeatedAllowed`, and `nextPhase` need coverage-aware statements.
   Their present proofs use one contiguous observed count and the fresh sequence equality.
   Preserve stale ACK bounds and window freshness.
   [Admission source](https://github.com/TomasOrtega/Netlib/blob/1816bb875fae6485966b2419ca6eb3ad922a93bf/Netlib/Protocol/TCP/Admission.lean#L75).
2. `AdmissionRecoveryFacts.Result.repeated_source` and `Result.repeated_frontier` need the new admission cases.
   Preserve exact source slices and one observation per processed repeat.
   Keep `AdmissionMSSFacts.Result.data_payload_bound` for both new and repeated ranges.
   [Recovery facts](https://github.com/TomasOrtega/Netlib/blob/1816bb875fae6485966b2419ca6eb3ad922a93bf/Netlib/Protocol/TCP/AdmissionRecoveryFacts.lean#L13), [MSS fact](https://github.com/TomasOrtega/Netlib/blob/1816bb875fae6485966b2419ca6eb3ad922a93bf/Netlib/Protocol/TCP/AdmissionMSSFacts.lean#L63).
3. `Checkpoint.Image` must contain every new coverage field.
   If coverage is inside `Lane`, its phase image already contains that lane.
   If coverage is elsewhere, add it to the image and its injectivity proof.
   Preserve stale-source and stale-cut rejection.
   `Installation.admission_continuation` and `Installation.continuation` must include sparse states.
   [Image](https://github.com/TomasOrtega/Netlib/blob/1816bb875fae6485966b2419ca6eb3ad922a93bf/Netlib/Protocol/TCP/Checkpoint.lean#L31), [continuation](https://github.com/TomasOrtega/Netlib/blob/1816bb875fae6485966b2419ca6eb3ad922a93bf/Netlib/Protocol/TCP/Checkpoint.lean#L344).
4. `CampusTCPService.Processing` must retain its single prepared attachment and current-policy execution.
   Early denial must preserve both tracker and admission state.
   A sparse observation grants no cached permission for later output.
   [Service order](https://github.com/TomasOrtega/Netlib/blob/1816bb875fae6485966b2419ca6eb3ad922a93bf/Netlib/Check/CampusTCPService.lean#L77), [early denial](https://github.com/TomasOrtega/Netlib/blob/1816bb875fae6485966b2419ca6eb3ad922a93bf/Netlib/Check/CampusTCPService.lean#L210).
5. `CampusTCPModel` must preserve actual output, assignment, service, and receipt identities.
   Delivery must still equal the selected gateway emission.
   Sparse admission changes service order, not the source relation.
   [Service and receipt](https://github.com/TomasOrtega/Netlib/blob/1816bb875fae6485966b2419ca6eb3ad922a93bf/Netlib/Check/CampusTCPModel.lean#L558).
6. Host `ReceiveStore` and `ReceiveStoreHistory` retain first receipt metadata and actual released-byte origins.
   Reuse their range vocabulary where useful.
   Do not reuse host drain behavior as gateway packet behavior.
   Preserve `CampusTCPGapFacts.Evidence.client_read_origin`, `server_read_origin`, and `application_prefix` on the new trace.
   [Host store](https://github.com/TomasOrtega/Netlib/blob/1816bb875fae6485966b2419ca6eb3ad922a93bf/Netlib/Protocol/TCP/ReceiveStore.lean#L16), [connected read facts](https://github.com/TomasOrtega/Netlib/blob/1816bb875fae6485966b2419ca6eb3ad922a93bf/Netlib/Check/CampusTCPGapFacts.lean#L83).

Prove supported input existence as well as successful-result soundness.
Use range geometry and window conditions as premises.
Do not require a caller-supplied successful sparse post-state.
The present `step_exists` is the corresponding admission entry point.
[Existence theorem](https://github.com/TomasOrtega/Netlib/blob/1816bb875fae6485966b2419ca6eb3ad922a93bf/Netlib/Protocol/TCP/Admission.lean#L462).

## Implemented bounded interface

[SparseCoverage](../../Netlib/Theory/SparseCoverage.lean) retains generic disjoint original ranges and exact contained repeat sources.
[Admission](../../Netlib/Protocol/TCP/Admission.lean) connects that ledger to checked TCP packet history, current headers, and the selected window bounds.
[CampusTCPSparseFacts](../../Netlib/Check/CampusTCPSparseFacts.lean) builds the source assurance from actual campus startup, application, current-policy, and gateway histories.
[The typed campus demonstration](../../NetlibTest/TCPSparseCampus.lean) connects unseen gateway starts, transferred coverage, retained host bytes, and actual read origins.
These results concern the selected bounded model.
The later custody and progress proposal remains separate.

## Reports and independent checks

The lane field `observed` remains the contiguous prefix.
An optional `coverage` object contains `highEnd`, `uniqueBytes`, `nextID`, and sorted original `runs`.
Each run retains `position`, `end`, `sourceID`, `observationIndex`, and `payloadHex`.
The observation index includes committed startup packets.
Exact contained repeats retain the first source and do not allocate another source identity.
A prior sparse history remains visible after all holes close through the original source allocation order.
No input flag activates this class.

The optional `sparseAssurance` field has scope `gateway-observation-sources`.
A checked object gives primary and standby summaries for both directions.
Each summary gives the frontier, greatest end, unique bytes, source count, and whether the prefix reaches that end.
A data-phase lane with zero bytes still has a zero summary.
A gateway outside the data phase has null direction summaries.
Checked evidence can retain holes, including holes in the fenced primary image.
It proves observation sources and does not establish packet custody, gap closure, or progress.
Thus, it has no pending queue status.
Actual noncompliance produces a failed object with its reason.
A history without sparse observations has no such field.

[The corpus](../../examples/tcp-sparse-admission/fixtures.json) contains nine campus cases and 14 raw admission cases.
It also has one campus input error and five raw input errors.
The three canonical campus input files must equal their independent case inputs.
The helper checks every actual write, original send, retry attempt, assignment, service, receipt, release, and read source.
It checks source identities and metadata against the actual committed observation list.
Expected bytes and state come only from the independent Python model.

The raw `tcp-admission` command starts with empty tracking and admission state.
Its inputs declare a zone, original and translated headers, and a raw packet history.
The fixed permit pipeline and declared mapping are explicit assumptions.
Raw mechanics cases establish no endpoint-write or campus-authentication origin.
Checked SYN, SYNACK, and ACK bytes build their prehistory.
Semantic negatives use valid checksums for ACKs across holes, changed repeat bytes, mixed overlap, and current right-edge violations.
They also check empty-ACK boundaries, retained repeat slices, and repeats after a zero-window advertisement.
Transport decode stops at the selected model stop, while all hex syntax is checked first.
Input cannot supply coverage, source identities, or a successful state.

The current Logoff case denies an actual unseen-prefix retry and retains both host spans.
A separate stale-permit-after-Logoff case has actual output but fails current-policy evidence and sparse assurance.
An exact checkpoint rejects a stale cut after coverage changes under an equal greatest end.
Another actual campus trace repeats the prefix after gateway ACK observation but before sender ACK receipt.
It retains the first gateway source and later returns all 800 read bytes once.

The old gap case `fresh-ingress-reordering-is-still-outside-gateway-profile` moves with its unchanged input to `fresh-ingress-reordering-keeps-actual-byte-sources`.
Its actual 37-event continuation is now supported.
All other 107 valid legacy campus, transfer, MSS, recovery, ACK, and gap rows retain their expected data and order.
The helper checks strict absence of sparse assurance on those rows.

## Actual campus landmark

[The client trace](../../examples/tcp-sparse-admission/trace.json) has 81 events, 13 endpoint outputs, and 11 gateway services.
Checked startup establishes asymmetric MSS and actual host seeds.
One accepted write supplies four different 200-byte original sends within the existing 800-byte flight bound.

The original ranges `[0,200)` and `[400,600)` are not served before their retries.
Primary service first observes `[600,800)` at event 37, then `[200,400)` at event 45.
Each accepted packet produces its gateway output immediately.
The host receives those actual outputs and holds both spans.
The gateway prefix is zero, greatest end is 800, and unique coverage is 400.
No gateway packet buffer or explicit loss disposition is inferred.

Installation 53 transfers the exact coverage image while both holes remain.
Host receive storage and clocks remain at their hosts.
The actual first-record RTO at event 60 retries `[0,200)`.
Standby service 62 accepts these bytes as new coverage, without an earlier observation of those bytes.
The gateway prefix becomes 400 while its greatest end stays 800 and unique coverage becomes 600.
Receipt 63 releases 400 ordered bytes and retains the final 200-byte span.
The actual cumulative ACK retires 400 at event 68.

The next real RTO at event 71 retries `[400,600)`.
Service 73 closes the remaining gateway hole.
Receipt 74 releases the remaining 400 ordered bytes.
Read 80 returns all 800 bytes once in write order.
Both ambiguous retirements leave the RTT estimator without a sample.

[The reverse trace](../../examples/tcp-sparse-admission/reverse.json) uses actual server outputs and the same two-hole schedule.
[The wrapped trace](../../examples/tcp-sparse-admission/wrap.json) rebuilds startup and all later packets from wrapped local sequence origins.
The existing source audit checks write, original send, attempt, assignment, current gateway service, receipt, release, and read order.
It does not derive expected bytes or state from a Lean report.

Physical delivery, connection identity, local clock correspondence, scheduling, and imported deployment correspondence remain external conditions.
The trace has no explicit packet custody or loss events and proves no eventual gap filling.
All seven programs and the full campus demonstration remain OPEN.

## Custody and bounded progress

Current campus state has separate output, work, service, and receipt lists.
`assign` can select an earlier output.
`deliver` can select an earlier service emission.
There is no explicit loss event or packet disposition in this event type.
Thus ignored outputs and emissions can represent loss only by omission from a finite trace.
[State](https://github.com/TomasOrtega/Netlib/blob/1816bb875fae6485966b2419ca6eb3ad922a93bf/Netlib/Check/CampusTCPModel.lean#L263), [events and execution](https://github.com/TomasOrtega/Netlib/blob/1816bb875fae6485966b2419ca6eb3ad922a93bf/Netlib/Check/CampusTCPModel.lean#L315).

`Outstanding` proves fresh identities and one completion per pending item.
The campus uses it for gateway work tickets.
It does not track the whole packet path to endpoint receipt.
Existing safe-handoff progress constructs admissible steps and a finite gateway drain.
It does not prove a TCP write reaches a peer read within a bound.
[Outstanding work](https://github.com/TomasOrtega/Netlib/blob/1816bb875fae6485966b2419ca6eb3ad922a93bf/Netlib/Theory/Outstanding.lean#L13), [handoff progress](https://github.com/TomasOrtega/Netlib/blob/1816bb875fae6485966b2419ca6eb3ad922a93bf/Netlib/Protocol/SafeHandoffFacts.lean#L240).

A first bounded-progress theorem can honestly retain ordered gateway ingress.
Permit bounded loss after gateway service and bounded ACK loss.
Require stable current permission, a usable peer window, bounded scheduling, and adequate retry budget.
Derive packet assignment, service, receipt, and actual ACK progress from explicit custody assumptions.
Do not assume the final empty store or the desired successful receive events.

RFC 6298 keeps timeout recovery as a fallback.
It retransmits the earliest unacknowledged segment and doubles RTO on expiry.
Karn's rule excludes ambiguous retransmission samples.
These rules supply protocol actions, not network delivery bounds.
[RFC 6298, sections 3 and 5](https://www.rfc-editor.org/rfc/rfc6298.html#section-5).

Such an ordered-ingress progress theorem is useful and nonvacuous.
It can cover loss already exercised by the current connected recovery trace.
Its scope must exclude later ingress packets overtaking an unseen lower range.
A theorem for that broader fault model needs sparse admission first.

The strongest subsequent architecture result combines both seams.
It gives each attempt explicit custody or loss and derives a completion bound under a stated loss budget.
Its positive trace includes the unseen standby hole fill above.
Its negative trace retains pending storage when current permission ends.
This is a proposed result, not a physical delivery claim.

Native TCP acceptance, physical clocks, connection identity, fair scheduling, and full close remain separate obligations.
The current guides explicitly leave native correspondence and eventual delivery OPEN.
[Current limits](https://github.com/TomasOrtega/Netlib/blob/1816bb875fae6485966b2419ca6eb3ad922a93bf/docs/TCP_RECEIVE_GAPS.md#L117).
