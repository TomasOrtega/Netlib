# Bounded TCP progress through a held gap

Netlib proves completion from the two actual held-gap cuts in the campus trace.
The first cut retains two 400-byte sender records and the upper 400 bytes at the server.
The second cut retains two 600-byte sender records and the upper 600 bytes at the client.
Neither proof resets an endpoint or replaces its prior history.

All seven programs and the full campus objective remain OPEN.

## Guarantee

The task starts with the selected lower packet on its actual live link.
One shared allowance permits at most two additional drops across the whole task.
It covers the original lower packet, retry data, and their ACK paths.
Each selected drop consumes its actual pending custody identity.
The suffix has no additional copy actions.

The receiver releases `lower ++ upper` once and reads those bytes once.
A later lower retry is wholly behind the receiver cursor.
It releases no new bytes and creates new immediate ACK work.
The actual covering ACK retires both sender records.
The final sender buffer and outstanding ledger are empty, its deadline is absent, and its timeout count is zero.

Only the lower record is retransmitted.
The upper record retains its identity, byte count, send time, and retry status until retirement.
Actual retries retain Karn suppression and the stored backoff history.
A lossless ACK can take a valid RTT sample.

## Service and bound

Every persistent next demand needs service within `B` evaluated slots.
Service includes assignment, gateway processing, delivery, ACK output, timer progress, timeout output, and read.
A packet demand can also resolve by a drop of that same pending packet.
An omitted action does not count as loss.

Let `q > 0` be the maximum logical endpoint clock increase per slot.
During a retry wait, the selected sender tick reaches `min (now + q) deadline`.
Other permitted waiting operations retain that demand.

With a two-drop allowance, the bound is:

```text
rank = 22 + ceil(initialRemaining / q) + ceil(2000 / q)
slots = rank * B

forward: initialRemaining = 1000, q = 10, B = 2, slots = 644
reverse: initialRemaining =  900, q = 10, B = 2, slots = 624
```

The first wait uses the actual initial deadline and current sender time.
The reverse cut has already used 100 logical milliseconds of its first timer.
The next retry wait uses the actual 2000-millisecond RTO.
The final retry has a 4000-millisecond RTO and no remaining selected drop credit.
Smaller allowances remove the unused wait reserves.

The read witness belongs to `steps.take slots` of the supplied actual trace.
The action and service checks read stored prior states and results.
They do not evaluate the endpoint or gateway again.
Unread input after an unsupported stop supplies no slots.

## Current state and prior sources

Both cuts retain actual startup, the selected write, both original sends, and the upper receipt.
The receiver retains that receipt's header and local receive time.
The sender retains both original records, its current clock, and its earlier recovery state.

The current standby gateway owns the fixed path after the earlier actual transfer.
Its checkpoint retains observation coverage and the actual prior sources in both directions.
The selected old lower packet can still come from an earlier primary service.
Repeated admission uses the current retained observation source.
It remains possible after an actual zero-window ACK.

Actual source records identify the selected original send or a later head retry.
Typed read origins connect each byte to its release, receipt, gateway service, peer output, and application write.
Equal payload bytes alone do not identify an application write.
Permission results require compliance of the prepared report and extend it through the passed suffix.

Old copies, tickets, receipts, and drops remain in the report.
The allowance counts only drops after the selected cut.
The proof does not require global work or custody to become empty.

## Clock and path assumptions

Clock operations are monotone and increase one selected endpoint clock by at most `q`.
Current ACK causes must permit the new time.
An immediate ACK cause can block a positive receiver tick until ACK output has service.
Initial native preflight comparisons, route and filter permits, and budget `100000` remain explicit assumptions.
Ownership, policy, authentication, attachment lifetimes, and configuration stay fixed during the suffix.

The initial link path needs at most `5 * B` slots to reach a selected drop or covering ACK receipt.
A retry output needs at most `7 * B` slots for the same resolution.
The corresponding clock margins use the actual initial remaining time and current retry RTO.
These margins exclude a timeout before live path resolution.
Timer waiting after a drop belongs to the full completion bound.

Logical local time does not establish physical timing, scheduler behavior, or native delivery.

## Proof interface

| Module | Result |
| --- | --- |
| `EndpointHeadTimeoutEnabled` | Actual head retry with the literal upper tail retained. |
| `EndpointGapReceiveEnabled` | Gap fill with both actual retained headers and ordered release. |
| `EndpointOldSpanEnabled` | Whole-old lower retry behind the combined cursor. |
| `CampusTCPGapProgressStart` | Actual startup, write, held receipt, current ledger, and selected old link. |
| `CampusTCPGapProgressEvidence` | Current phases, stored references, first receipt, and suffix drop log. |
| `CampusTCPGapProgressProgress` | Enabled demand, retained evidence, and rank decrease for permitted transitions. |
| `CampusTCPGapProgressBounded` | Read and sender retirement within the supplied evaluated prefix. |
| `CampusTCPGapProgressOrigins` | Actual selected write and typed per-byte read origins. |
| `CampusTCPGapProgressBookkeeping` | Exact additional drop count and exclusion of new copies. |
| `CampusTCPGapProgressTiming` | Live path resolution and actual timer margins. |

`Basis` contains the initial geometry, positive clock quantum, and allowance bound.
`read_by` accepts the action and service predicates.
`read_by_checked` accepts their verified Boolean checks.
`read_and_retirement_by` also exposes the actual sender state at the bound.
`completed_read_origins` supplies each byte's typed origin with the exact selected writer and an actual producer in the same report.
`completed_read_permissions` also supplies current service permission when the prepared report is compliant.

## Tests and open scope

Generated tests apply the bounded theorem to the same retained traces.
They cover all 16 permitted zero-, one-, and two-loss words at each cut.
Four further cases cover zero-window retries and wrapped sequence values in both directions.
Guard cases reject omitted service, early or denied timeouts, overdue ACK clocks, a third selected drop, and exhausted retry credit.

The two cut results are independent applications.
They do not establish one shared drop allowance across a sequential exchange in both directions.
That result needs a new reverse setup from the changed forward state and a shared remaining allowance.

Progress through sparse holes, more flights, additional copies, competing applications, gateway transfer, persist, and fast recovery remains open.
See the [fresh-range result](TCP_RECOVERY_PROGRESS.md), [receive gaps](TCP_RECEIVE_GAPS.md), and [progress design](research/CAMPUS_PROGRESS.md).
