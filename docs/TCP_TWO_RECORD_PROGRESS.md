# Bounded TCP progress for two original records

Netlib proves completion from an actual accepted write of `lower ++ upper`, before either original send.
Both ranges are nonempty and fit the stated MSS, window, storage, and sequence bounds.
The theorem covers every actual schedule that meets the action and persistent-service contract.
It retains the earlier endpoint and gateway histories.

All seven programs and the full campus objective remain OPEN.

## Guarantee

The sender emits the lower and upper originals from the selected write.
After both sends, the selector offers both current actions when both original paths have pending work.
Assignment, gateway service, and delivery can alternate between those paths.
The proof permits either delivery order.

| First arrival | Receiver behavior | Sender ACK effect |
| --- | --- | --- |
| Lower | Release `lower`; later upper arrival releases `upper`. | A partial ACK can retire only the lower record. |
| Upper | Hold the upper run; lower arrival releases `lower ++ upper`. | The gap ACK leaves the head outstanding; a covering ACK retires both records. |

Held data retains its actual allocation identity, packet header, and receipt time.
Gap closure processes the retained headers in sequence order.
Later whole-old receipts release no new bytes and create new ACK work.
This includes a lower retry strictly behind the cursor after both ranges were released.

One shared allowance `D ≤ 2` covers additional drops on the selected suffix.
It includes ingress and link drops of either original, either head retry, and gap, partial, or full ACK packets.
Each drop consumes its actual pending custody identity.
An omitted operation does not count as loss.
The selected suffix permits no new copy actions or competing application writes.

The receiver reads exactly `lower ++ upper`.
The selected release stream contains those bytes once, as one combined chunk or two ordered chunks.
The final sender sent buffer and outstanding ledger are empty.
Its deadline and last timed-out identity are absent, and its timeout count is zero.
Old unrelated work and custody can remain pending.

## Actual recovery

Every timeout uses an actual recorded loss cause for the current head.
The stored timer target is

```text
max(stored deadline, head.lastAt + current RTO).
```

During a wait, the selected sender tick reaches `min(now + q, target)`.
A due timeout emits only the current head bytes and retains the literal tail record.
Each retry creates a fresh output and custody identity with the original stream coordinates and selected write source.
The shared allowance bounds global timeout outputs separately from each head's timeout count.

A partial ACK retains `lastTimedOut` and `timeoutCount` while another record remains.
A later timeout of the different tail identity starts that head's count at one.
Only full retirement clears both fields.
Karn suppression prevents a new RTT sample for a retried head.
It retains an earlier sample rather than forcing `lastSample` to be absent.
A fresh partial ACK can update the RTO used by the remaining tail.
The final covering ACK can also update the estimator when its retired records permit a sample.

## Service and bound

Let `B` bound service of each persistent next demand in evaluated joint slots.
The demands include sends, assignment, gateway service, delivery, ACK output, timer ticks, timeout output, and read.
A packet demand can resolve through its selected operation or a drop of that same exposed packet.

Let `q > 0` bound each logical endpoint clock increase.
Clock operations must also satisfy current ACK issued-time and deadline guards.
The endpoints retain separate clocks.
An immediate ACK cause can block a positive receiver tick until its output has service.

The sufficient bound is:

```text
H = 16 * B
C = max(initial RTO, sampleCap(initial estimator, H * q))
T = ceil((2^D * C) / q)
N = H + B * ((D + 1) * T + 8 * D + 7)
```

The first stage reaches an actual non-original phase by slot `H`.
`sampleCap` bounds one fresh RTT update over sample ages from zero through `H * q`.
The proof derives this age bound from the actual stored clock operations.
The recovery stage keeps this same `C` after the handoff.
It does not substitute a larger cap from later clock ages.
Retries at slot `H` can already be positive.

The RTO cap applies while a sender record remains outstanding.
It does not bound the final retired estimator or RTO.
The second stage uses remaining timeout credit, current timer slots, and current packet work as a decreasing rank.

The supplied actual trace must contain at least `N` evaluated slots.
Its stored actions must satisfy the raw action and service checks.
Unread input after an unsupported stop supplies no slots.
The completion and read witnesses refer to that same supplied prefix.
The proof does not evaluate a second endpoint or gateway run to obtain them.

## Current state and source evidence

The initial cut retains actual startup and the selected accepted write.
Its sender has no earlier outstanding data, and its receiver is ready for the selected bytes.
Earlier writes, reads, receipts, allocation counters, recovery estimates, and gateway observations remain in the history.
No endpoint is replaced with a new seed.

Both endpoint routes keep the selected gateway owner during the suffix.
The owner can be the primary or an installed standby under the corresponding current guards.
Existing checkpoint and observation sources remain actual earlier records.
Configuration, policy, authentication, attachments, and route ownership stay fixed during this task.

Current typed native preflight comparisons, route and filter permits, and budget `100000` remain explicit initial premises.
They connect the declared model to its supplied native observations.
The result does not prove a native kernel implementation or physical delivery and timing.

Typed source evidence connects each read byte to its actual release, receipt, gateway service, peer output, and selected application write.
The output can be an original send or a head retry.
Equal payload bytes alone do not identify that write.
Current service permission results additionally require compliance of the initial report.
The proof extends that compliance through the actual passed suffix.

## Proof interface

| Module | Result |
| --- | --- |
| `RecoveryHeadAckEnabled` and `EndpointPartialAckEnabled` | Actual partial head retirement with the literal tail and recovery metadata retained. |
| `EndpointFutureReceiveEnabled` and `EndpointGapReceiveEnabled` | Actual upper holding and ordered gap release. |
| `CampusTCPTwoProgressStart` | Actual accepted-write cut, endpoint guards, gateway state, and current native environment. |
| `CampusTCPTwoProgressEvidenceStep` | Actual next evidence for every allowed stored step. |
| `CampusTCPTwoProgressOriginalBounded` | Original-stage handoff by `16 * B`. |
| `CampusTCPTwoProgressHandoffRTO` and `CampusTCPTwoProgressRecoveryCapped` | Derived initial timer cap and its preservation on every later actual prefix. |
| `CampusTCPTwoProgressRecoveryBounded` | Actual completion within `N` supplied slots. |
| `CampusTCPTwoProgressRecorded` and `CampusTCPTwoProgressBounded` | Exact recorded prefix, actual reader, and read slot before `N`. |
| `CampusTCPTwoProgressReadWriter` and `CampusTCPTwoProgressEvidenceTrace` | Selected write ancestry and current service permissions for the exact read. |

`CampusTCPTwoProgressBounded.complete_by_checked` accepts verified Boolean action and service checks.
Its `Result` retains the exact recorded prefix, actual read, retired sender state, and source histories.
`Result.reader_slot` identifies that same read before `N`.
`Result.read_permissions` connects each byte to its selected writer and actual permitted service.

## Tests and open scope

The 68 generated cases use `q = 10` and `B = 3`.
They complete in 15 through 329 actual slots.
They cover both directions, both delivery orders, selected drop edges, partial retirement, head retries, and retained old histories.
These runs test selected behaviors; they do not enumerate every allowed schedule or replace the universal proof.
Two further cases extend their actual completed traces with allowed clocks at the current sender time until `N`.
They apply the public bounded theorem with verified action and service checks in both directions.
Each retains one result's read slot, exact bytes, timeout bound, selected writers, and service permissions.
The milestone changes no fixture schema or runtime protocol behavior.

The forward and reverse results use separate selected cuts and allowances.
One sequential exchange with a single shared allowance across both directions remains open.
More than two original records, sparse holes, extra copies, concurrent applications, gateway transfer during progress, persist, and fast recovery also remain open.

See the [held-gap result](TCP_GAP_PROGRESS.md), [fresh-range recovery](TCP_RECOVERY_PROGRESS.md), and [campus progress design](research/CAMPUS_PROGRESS.md).
