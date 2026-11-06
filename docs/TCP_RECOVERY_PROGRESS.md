# Bounded TCP recovery progress

Netlib proves completion of one fresh client-to-server range with advancing logical clocks and at most two additional packet drops.
The proof uses the actual startup, application write, gateway services, receipts, retries, and read.
It covers every schedule that meets the stated action and service contract.

All seven programs and the full campus objective remain OPEN.

## Guarantee

The selected range has at most three transmissions: its original output and two actual timeout outputs.
One shared drop allowance covers data ingress, data links, ACK ingress, and ACK links.
Each failed attempt consumes an actual selected custody identity.

The server releases the range once and reads exactly the selected write.
Later whole-old receipts release no new bytes and create fresh immediate ACK work.
The sender's final sent buffer and recovery ledger are empty, its deadline is absent, and its timeout count is zero.

The theorem identifies the actual read in the supplied evaluated prefix.
Unread input after an unsupported stop supplies no slots.
The bound starts after the actual five setup actions.

## Service and bound

Every persistent next demand has service within `B` evaluated slots.
Packet resolution means assignment or delivery, or an explicit drop of that same pending packet.
Gateway service, ACK output, timer ticks, timeout output, and the final read also need service.

Let `q > 0` be the maximum logical clock increase per slot.
During a retry wait, the selected sender tick reaches `min (now + q) deadline`.
Other admitted waiting operations keep that tick demand live.

The first sender RTO is `1000` logical milliseconds.
Two actual timeout operations increase it to `2000` and `4000`.
The completion bound is:

```text
rank(q) = 25 + ceil(1000 / q) + ceil(2000 / q)
slots(q, B) = rank(q) * B
slots(10, 2) = 650
```

The constant `25` covers one send, three seven-action packet paths, two timeouts, and one read.
The two wait terms cover the first and second retry deadlines.
A finite supplied suffix must contain at least the declared number of evaluated slots.

The service check reads prior-state demands and actual stored events.
Omitted assignment, gateway service, delivery, ACK output, clock progress, timeout output, or read violates the contract.
An omitted operation does not count as packet loss.

## Clock and action profile

The selected suffix has one active range, fixed primary ownership, and no additional copy actions.
It admits its current packet or application demand and guarded endpoint clock operations.
A timeout follows an actual selected drop.

Each clock operation is monotone and increases the selected endpoint clock by at most `q`.
Old ACK causes must permit the new time under their issued-time and deadline guards.
An immediate ACK cause can block a positive receiver tick until ACK output has service.

The theorem uses logical local clocks.
Physical clock correspondence, scheduler behavior, and native delivery remain external obligations.

Each live attempt reaches an actual selected drop or client ACK receipt within `7 * B` slots after output.
If `q * (7 * B) < 1000`, the sender clock stays before that attempt's actual stored deadline through resolution.
No client timeout occurs before that resolution.
The proof derives this result for the actual original send and every actual retry.
At `q = 10` and `B = 2`, each path has at most `14` slots and `140` logical milliseconds.
Timer waiting after a drop belongs to the main completion bound.

## Actual retry paths

Gateway observation and receiver release are separate state facts.
After a data-link drop, the next packet repeats gateway admission but can supply the receiver's first release.
After an ACK drop, the next data receipt is whole-old and creates a new covering ACK cause.

A known repeat remains admissible after a real ACK advertises zero window space.
Its source is the actual first indexed admission observation.
A retry preserves the original stream range and write ancestry while creating a fresh output and custody identity.

Karn suppression excludes an RTT sample from a retried range.
The retired range retains its actual backed-off RTO.
A read can leave new window ACK work pending.

## Initial state and evidence

The proof reuses `CampusTCPRoundStart.Initial` and `NativeEnv` from the [first bounded round](TCP_ROUND_PROGRESS.md).
Actual startup derives the NAT entry, both zones, endpoint cursors, negotiated MSS, and admission lanes.
Actual setup enables recovery and ACK reactions at both endpoints and writes the selected bytes.

The nonempty range fits the pending limit, effective MSS, and peer receive capacity.
Initial typed preflight comparisons, budget `100000`, and native route and filter permits remain explicit assumptions.
Configuration, authentication, attachment lifetimes, policy, and route ownership remain fixed during this suffix.

Old pending startup copies, tickets, and drops can remain in the initial report.
Only the selected suffix uses the two-drop allowance.
The proof does not require global work or custody to become empty.

The origin bridge constructs existing typed delivery, receive, and per-byte read-origin witnesses from actual records.
Permission corollaries require compliance of the prepared report and extend it through the actual passed suffix.
No successful assurance search supplies these witnesses.

## Proof interface

| Module | Result |
| --- | --- |
| `CampusTCPTimedClock` | Actual clock steps, current runtime frames, and retained packet work. |
| `CampusTCPRecoveryRoundSender` | One actual sender range through ticks, backoff, and retirement. |
| `CampusTCPRecoveryRoundReceiver` | First release, whole-old rejection, and real ACK work. |
| `CampusTCPRecoveryRoundAdmission` | First actual source and fresh or repeated current admission. |
| `CampusTCPRecoveryRoundEvidence` | Actual current phase, packet references, and suffix drop log. |
| `CampusTCPRecoveryRoundProgress` | Concrete invariant, enabled demand, persistence, and rank descent. |
| `CampusTCPRecoveryRoundBounded` | Actual prefix read and completion within the declared bound. |
| `CampusTCPRecoveryRoundHistory` | One nonempty release, one nonempty read, and exact byte streams. |
| `CampusTCPRecoveryRoundOrigins` | Existing typed delivery and write-origin evidence. |
| `CampusTCPRecoveryRoundBookkeeping` | Exact additional drop count and copy exclusion. |
| `CampusTCPRecoveryRoundTiming` | Actual path resolution, clock growth, and exclusion of early timeouts. |

`read_by` accepts the action and service predicates.
`read_by_checked` accepts their verified Boolean checks.
`read_and_retirement_by` also exposes the actual sender state at the bound.

## Tests and open scope

Generated tests retain the same actual startup, setup, and indexed suffix traces.
They cover all 21 zero-, one-, and two-loss patterns, zero-window ACK loss, and old pending work with earlier drops.
Separate cases reject service omissions, early or denied timeouts, overdue ACK clocks, a third selected drop, and a third timeout.

The [held-gap result](TCP_GAP_PROGRESS.md) starts at the actual two-record 400-byte and 600-byte cuts.
Planned gateway transfer, additional copies, multiple flights, competing applications, persist, and fast recovery remain open.
The fresh-range theorem does not reset or replace that held-gap prefix.

See the [progress design](research/CAMPUS_PROGRESS.md), [recovery model](TCP_RECOVERY.md), and [custody guide](PACKET_CUSTODY.md).
