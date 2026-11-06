# Packet custody and bounded service

The campus checker retains each packet until an explicit action consumes it.
Each actual endpoint output creates an ingress packet.
Each actual gateway emission creates a receiver-link packet.
The input cannot supply a replacement packet source, identity, payload, or custody state.

This includes startup packets, application data, pure ACKs, and timer retries.
A local send denial creates no output packet.
An accepted gateway service with no emission creates no receiver-link packet.
Those outcomes do not count as link loss.

## Packet actions

Each packet has an internal identity, exact bytes, an actual output or service reference, and an optional copy parent.
The `packets` array lists these records in identity order.
Each state has `custody.nextID`, pending identities, resolution records, and a copy count.
The `custodyAssurance` field reports the proved source and identity scope.
It does not state that pending work will receive service.

| Action | Custody effect |
| --- | --- |
| `assign` | Consume the first pending ingress packet for the selected output and create the existing immutable ticket. |
| `serve` | Consume the selected ticket through the current gateway computation. Create a link packet only for an actual emission. |
| `deliver` | Consume the first pending link packet for the selected service. Its stored bytes must equal `rawIPv4Hex`. |
| `copyPacket` | Cite a live or retired packet identity. Create a fresh identity with the same source and bytes and retain its parent. |
| `dropPacket` | Consume the selected pending packet identity and record one explicit link drop. |

Copy and drop events have the form:

```json
{"kind": "copyPacket", "packet": 6}
```

```json
{"kind": "dropPacket", "packet": 8}
```

A repeated assignment or delivery needs a pending explicit copy.
A consumed identity cannot be assigned, delivered, or dropped again.
A copy can cite a retired source because the immutable source remains stored.
It cannot change the source or bytes.
An unknown parent or absent pending identity is an input error.

An omitted operation leaves its packet pending.
The end of a finite trace does not establish loss.
An unsupported delivery still consumes its actual link packet when the endpoint recorded that receipt.
An unsupported gateway service that returns no service result leaves its ticket pending.
Input errors commit no state changes.

## Checked source and identity laws

`Theory.PacketCustody` uses fresh internal identities and retains copy lineage.
Its actual-operation history proves identity uniqueness, earlier copy parents, exact payload retention, and one-use resolution.
Every packet has an actual original source in the same history.
Pending and resolved packet counts sum to the number of allocated identities.
Only a resolution with disposition `dropped` increases the loss count.

`Check.CampusTCPCustodyFacts` lifts those laws through the actual campus step and trace.
It binds each stored packet to the exact endpoint output or gateway service at its stored index.
The checker evaluates the endpoint and gateway functions once per joint operation.
The custody transaction uses their actual results and the preceding custody state.
Existing authentication, current-policy, assignment, receipt, application-byte, and checkpoint proofs use those same results.
No second endpoint or gateway execution supplies the proof.

These laws apply even when a report fails a policy comparison.
A stale installed allow rule can still emit a real modeled packet.
That output receives custody and retains the failed comparison.
The model does not replace the installed rule with an intended deny rule.

## General bounded progress theorem

`Theory.BoundedProgress` provides an adapter over an actual checked transition relation.
Each concrete adapter must prove invariant preservation, nonincreasing rank, and a demand when rank is positive.
A pending demand must be enabled in the preceding state.
It persists while the rank stays unchanged.
An actual action that serves that demand must decrease rank.
Rank zero must imply the selected completion property.

The scheduling condition supplies service within `B` operation slots for each persistent demand.
The theorem proves completion for every execution that satisfies these laws and this service bound.
The derived bound is the initial rank multiplied by `B`.
A finite-prefix theorem requires that this bound fit inside the actual checked prefix.
It needs no hypothetical infinite continuation.
Sequential tasks add their local bounds.
A cut-state result reads the downstream rank from the actual state after the first task bound.
It permits creation of a downstream obligation before that task becomes active.
Concurrent tasks use the maximum of their local bounds, with a service condition for each task on the same execution.
A proved transition projection can transfer an adapter to a concrete system.

The service condition is an explicit assumption about actions.
It does not assume a successful final receipt or an empty final queue.
A scheduler that never services a positive pending demand fails that condition.
The tests include all 64 six-slot service/idle schedules for a small counter, plus finite-prefix and composition cases.

## Connected evidence

`examples/packet-custody/trace.json` contains 175 checked operations.
It records two data drops and two pure-ACK drops by their actual link identities.
The same endpoint histories retain reads of 2400 bytes at the server and 3600 bytes at the client.
One final packet remains pending.
Current gateway denial and local retry denial create no additional loss.

The corpus compares eight traces and thirteen input-error cases against an independent Python model.
It covers omitted actions, historical copies, link drops, missing sources, consumed identities, and exact byte checks.
Existing campus inputs now use explicit copy events where they previously reused a historical source.
No parser or replay inserts those copy events on behalf of an input.

## Remaining campus progress work

The [bounded round](TCP_ROUND_PROGRESS.md) now connects packet custody to a concrete TCP adapter.
It derives actual receive release, covering ACK output, sender retirement, and a read by `9 * B` evaluated slots.
This first suffix fixes local clocks and primary ownership and permits no additional copy or drop.
It retains the actual current-policy and byte-origin evidence.
The [recovery round](TCP_RECOVERY_PROGRESS.md) extends this result to advancing logical clocks and at most two combined data or ACK drops.
Its selected suffix has no additional copy operations.
The proof identifies each actual dropped packet and the exact increase from the initial custody count.
Old pending packets and earlier drops can remain in the initial report.
At quantum `10` and service bound `2`, the actual read occurs within `650` evaluated slots.
It also proves one nonempty release and read, actual sender retirement, and existing typed byte origins.

The [held-gap result](TCP_GAP_PROGRESS.md) retains both actual 400-byte and 600-byte cuts and their old pending packets.
It permits two shared data and ACK drops per selected task and retires both sender records.
Additional copies, more flights, and planned gateway transfer need broader progress profiles.
Clock guards, receive space, read service, current policy, and route ownership remain explicit conditions.
Native time and physical delivery remain external.
See the [campus progress design](research/CAMPUS_PROGRESS.md) for these proof obligations.
All seven programs and the full campus objective remain OPEN.
