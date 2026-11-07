# Selected TCP startup recovery

This note records the selected RFC rules for the implemented ordinary IPv4 startup recovery profile.
The original investigation used source commit `ad7f5216fd32846a375305291d877ef3ed360f7d` on 2026-11-06.
The [startup recovery guide](../TCP_STARTUP_RECOVERY.md) states the current implementation, theorem assumptions, and remaining limits.
The implementation does not cover all TCP requirements.

## Original boundary and implemented extension

[Handshake.lean](../../Netlib/Protocol/TCP/Handshake.lean) derives two empty application states from checked startup packets.
It already preserves directional MSS offers.
[TCPHandshake.lean](../../Netlib/Check/TCPHandshake.lean) has one ordered exchange and one source output per phase.
It has no clock, outstanding control queue, or duplicate transition.
[Admission.lean](../../Netlib/Protocol/TCP/Admission.lean) permits one SYN, SYN,ACK, ACK progression.
Its later repeated-data rule does not admit startup duplicates.
Thus endpoint recovery alone cannot establish recovery through gateway admission.

Those modules retain their ordinary behavior.
[TCPHandshakeRecovery](../../Netlib/Check/TCPHandshakeRecovery.lean) adds actual timed emissions, receipts, duplicate handling, and endpoint histories.
[AdmissionStartupRecovery](../../Netlib/Protocol/TCP/AdmissionStartupRecovery.lean) adds checked duplicate controls without changing the ordinary admission default.
The mixed checkpoint history preserves actual observations and source bindings through installation.
[The campus theorem](../../Netlib/Check/CampusTCPStartupTransferBound.lean) now joins actual startup, setup, both data reads, and planned gateway transfer.
It uses one whole action check, one service check, and one physical loss ledger under its selected raw assumptions.

## Timer rules and selected choices

Initial RTO SHOULD be 1 second; a value greater than 1 second is permitted.
Computed RTO SHOULD have a 1-second floor.
An optional RTO cap must be at least 60 seconds.
[RFC 6298, sections 2.1, 2.4, and 2.5](https://www.rfc-editor.org/rfc/rfc6298.html#section-2).

Section 5 RECOMMENDS these timer operations.
Start an idle timer on transmission.
Stop it after all outstanding sequence space is acknowledged.
Restart it on an ACK of new sequence space.
On expiry, resend the earliest unacknowledged segment, MUST double RTO, then start the timer with that RTO.
A retransmission MUST NOT occur before its applicable RTO interval.
[RFC 6298, section 5](https://www.rfc-editor.org/rfc/rfc6298.html#section-5).

Karn forbids an RTT sample from a retransmitted segment without timestamp disambiguation.
Take at least one sample per RTT when possible; use the specified estimator.
[RFC 6298, sections 2 and 3](https://www.rfc-editor.org/rfc/rfc6298.html#section-3).

After a SYN timeout with RTO below 3 seconds, data transmission MUST begin with RTO reinitialized to 3 seconds.
[RFC 6298, section 5.7](https://www.rfc-editor.org/rfc/rfc6298.html#section-5).

Selected implementation choices:

- Use one timer per endpoint, a monotonic millisecond clock, initial RTO 1000 ms, and no cap.
- Retain the original control output until its SYN position is acknowledged.
  A timeout emits another occurrence of that output.
- Store the deadline, generation, last transmission time, retransmission count, and whether a SYN timeout used RTO below 3000 ms.
  Store this last fact before doubling.
- At data start, use at least 3000 ms when that fact is true.
  Preserve a larger backed-off RTO as a conservative policy.
- Keep RTT eligibility separate from output provenance.
  A later receipt linked to the original output does not restore eligibility after retransmission.
- At an ACK that empties the queue, stop the timer.
  Do not leave a restarted timer running with an empty queue.
  A duplicate ACK supplies no new progress.

The implementation retains this timer state through the actual application handoff.
The startup result does not reset it to the default application RTO.

## Selected transition table

Let active ISS be `a` and passive ISS be `b`.
All additions are modulo `2^32`.
Each accepted control input must match an earlier actual output through its checked byte path.
Use the source rules below; the table also fixes the selected profile's scheduling and scope.

| Endpoint and event | Output and next state | Timer effect |
| --- | --- | --- |
| Active OPEN | SYN `(a,0)`; SYN-SENT | Start active timer. |
| Passive LISTEN receives SYN | SYN,ACK `(b,a+1)`; SYN-RECEIVED | Start passive timer. |
| Either pending SYN timer expires | Repeat its retained SYN or SYN,ACK; same phase | Apply expiry rule above. |
| Active SYN-SENT receives valid SYN,ACK | ACK `(a+1,b+1)`; ESTABLISHED | Acknowledge local SYN; stop active timer. |
| Passive SYN-RECEIVED receives final ACK `(a+1,b+1)` | No output; ESTABLISHED | Acknowledge local SYN; stop passive timer. |
| Passive SYN-RECEIVED or ESTABLISHED receives duplicate original SYN | Bare ACK with current cursors; same phase | Keep existing timer state. |
| Active ESTABLISHED receives duplicate original SYN,ACK | Bare ACK with current send and receive cursors; same phase | Do not arm a final-ACK timer. |
| Active SYN-SENT receives the passive bare ACK above | Discard; same phase | Keep active deadline. |
| Passive ESTABLISHED receives duplicate final ACK before data | No output; same state | No startup timer. |
| An obsolete timer event arrives after cancellation | No output; same state | Reject its generation as obsolete. |

The normal transitions follow
[RFC 9293, sections 3.10.1, 3.10.7.2, and 3.10.7.3](https://www.rfc-editor.org/rfc/rfc9293.html#section-3.10.7.3).
The pending timeout uses
[RFC 9293, section 3.10.8](https://www.rfc-editor.org/rfc/rfc9293.html#section-3.10.8).

Duplicate original SYN and SYN,ACK have length one and end before `RCV.NXT`.
The first sequence test therefore sends ACK and returns.
It does not reach the later SYN test.
This is a derivation from
[RFC 9293, sections 3.4 and 3.10.7.4, first step](https://www.rfc-editor.org/rfc/rfc9293.html#section-3.10.7.4).
In SYN-SENT, a bare ACK has no SYN or RST, so it is discarded at the fifth step.
[RFC 9293, section 3.10.7.3](https://www.rfc-editor.org/rfc/rfc9293.html#section-3.10.7.3).

The final bare ACK has no independent retry timer.
Its loss is recovered by the passive SYN,ACK timeout and the active ACK response.
This follows from the table and the fact that data-free ACKs lack reliable transmission.
[RFC 1122, section 4.2.3.6](https://www.rfc-editor.org/rfc/rfc1122.html#section-4.2.3.6).

## Input limits and source updates

The selected empty SYN profile makes the active ACK bound exactly `a+1`.
Keep the existing final sequence and ACK tests.
General SYN data needs a wider ACK interval.
[RFC 9293, section 3.10.7.3](https://www.rfc-editor.org/rfc/rfc9293.html#section-3.10.7.3).

Retain [the current MSS profile](TCP_MSS.md): absent or one positive offer; valid MSS, NOP, and EOL framing; no final-ACK options.
For retransmissions, retain the selected raw options, ISS, window, and offer.
An exact duplicate does not select a new MSS or recreate application buffers.
A changed offer is outside this duplicate profile.
These are model choices, not new receiver rejection requirements.

Verified erratum 8167 removes the SYN-SENT `RCV.NXT` reset mitigation paragraph.
[RFC 9293, erratum 8167](https://www.rfc-editor.org/errata/eid8167).
Verified editorial erratum 8710 adds SYN to the passive SYN-RECEIVED return-to-LISTEN diagram edge.
It does not bypass the earlier sequence test for an old duplicate.
[RFC 9293, erratum 8710](https://www.rfc-editor.org/errata/eid8710).

RFC 1122's SYN failure thresholds require the general notification mechanism and permit different SYN thresholds.
The SYN abort threshold MUST allow at least three minutes; an application may stop earlier.
[RFC 1122, section 4.2.3.5](https://www.rfc-editor.org/rfc/rfc1122.html#section-4.2.3.5).
These rules remain in
[RFC 9293, section 3.8.3](https://www.rfc-editor.org/rfc/rfc9293.html#section-3.8.3).
Do not present an arbitrary short retry count as this standard abort rule.

After SYN or SYN,ACK loss, the initial data window MUST be one segment of at most SMSS.
Handshake ACKs MUST NOT grow the congestion window.
[RFC 5681, section 3.1](https://www.rfc-editor.org/rfc/rfc5681.html#section-3.1).
IW is the size of `cwnd`; this window limits unacknowledged sequence space.
[RFC 5681, section 2](https://www.rfc-editor.org/rfc/rfc5681.html#section-2).
Select `cwnd = SMSS` and total unacknowledged data bytes at most SMSS.
This permits two positive partial segments whose combined payload fits that bound.
It does not require one output occurrence at a time.
The IETF's later guidance explicitly permits multiple sub-MSS packets within a 1-MSS window.
That guidance is Informational; it supports this interpretation rather than changing the normative window rule.
[RFC 9006, sections 3.2.3 and 3.3.1](https://www.rfc-editor.org/rfc/rfc9006.html#section-3.3.1).
Larger byte windows need explicit congestion-control semantics.

## Actual history and loss accounting

Maintain separate endpoint phases.
The active endpoint can be established while the passive endpoint still has an outstanding SYN.
Both timers can run after passive SYN receipt while the active endpoint still waits for SYN,ACK.
Order all clock, timeout, delivery, gateway-service, and application events in one report.
Equal timestamps use event order.
A receipt can cancel a timer before its queued expiry event; expiry can also occur first.
Check both cases without allowing a deadline to cause two retransmissions.

Record each emitted occurrence with its role, event index, bytes, and control kind.
Record each delivery against that occurrence, including duplicate and delayed original deliveries.
Accept a delayed original through the same state-dependent input checks as a retransmitted copy.
Do not require the receipt to use the most recent equal output.
If a source occurrence can be delivered more than once, record the copy relation explicitly.
Byte equality alone does not identify which equal transmission was delivered.
Do not use IPv4 Identification as this identity.
[RFC 9293, section 3.8.1](https://www.rfc-editor.org/rfc/rfc9293.html#section-3.8.1).

For a claim that a particular output was lost, close that occurrence with an explicit drop or with the selected report's final accounting rule.
An undelivered occurrence in a finite prefix can still be delayed.
Retransmission does not itself prove loss.
Keep endpoint receipt, gateway admission, gateway output, and endpoint application read as different events.
Their counts need not agree.

Preserve the same selected connection instance, tuple-rewrite certificates, checksum checks, options, and output history across primary and standby service.
Recovery must not install supplied established seeds or fabricate startup history at the standby.
The implemented admission duplicate transitions preserve the learned MSS offers and the connection instance.
An ACK response to an old SYN must not advance the admission phase as if it were the missing final ACK in the opposite direction.

## Trust and excluded behavior

Local configuration, ISS selection, clock progress, connection freshness, and the delivery schedule are explicit inputs or assumptions.
Tuple matching and exact bytes do not authenticate a peer or prove physical transmission.
Delayed packets belong to the selected instance; connection reuse is excluded.
Finite successful schedules do not prove eventual delivery under arbitrary loss.
The implemented bounded theorem requires the selected whole action and persistent-service checks, fixed raw paths, and sufficient report length.
Its complete startup-to-transfer profile requires at most two physical drops and positive clock and service bounds.
It derives current session geometry and inherited timer bounds from the actual history.
It assumes no supplied future readiness or timer cap.

Stop with an unsupported result before any omitted response affects later state.
Exclude simultaneous open, SYN data, new in-window SYNs, RST, ICMP errors, user abort, close, retry exhaustion, and option features outside the selected MSS profile.
Do not continue with unchanged state when those events require omitted processing.
Do not label these scope exclusions as requirements for a conforming TCP implementation.

The [end-to-end test](../../NetlibTest/CampusTCPStartupEndToEnd.lean) has two startup expiries and one data expiry with two physical drops.
Startup expiry counts are not bounded by the physical drop count.
The completed theorem result identifies an actual prefix and permits read-created window ACK work.
It does not establish support for an arbitrary later tail.
All seven research programs and the full campus landmark remain OPEN.
