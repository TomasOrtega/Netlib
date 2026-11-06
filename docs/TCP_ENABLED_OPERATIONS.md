# Enabled TCP operations

These proofs derive supported operations from the preceding state.
They use the existing endpoint, gateway, and campus computations.
The scheduling condition must still supply those operations.
A complete bounded TCP transfer theorem remains OPEN.

## Endpoint guards

`Endpoint.AckPrepared` strengthens ACK coherence with two conditions:

- Every pending cause satisfies its actual issue time and deadline at the current local clock.
- The actual candidate output window covers every pending position and minimum window edge.

`AckCoherent` alone does not establish the second condition.
A pending read request can require a larger right edge.
The tests include a coherent state whose uncovered edge prevents output.

`ResponseAvailable` requires actual pending ACK credit.
For deadline-only dispatch, its actual stored deadline must also be due.
The proofs derive ACK output and encoding from these guards and endpoint validity.
They do not take an accepted output as a readiness premise.
Writes, reads, sends, and output preserve preparation under their stated bounds.
The ACK initialization theorem derives preparation from the existing startup conditions.

`RecoveryEnabled` derives clock advance, acknowledgment, and timeout operations from old ledger bounds.
The clock invariant relates actual send times, retry times, and the current local clock.
Timeout readiness includes a real outstanding head, a due stored timer, elapsed head interval, and the remaining retry allowance.
An expired timer or a qualifying duplicate ACK retains the existing profile limits.
Full ACK retirement also requires positive outstanding timing ranges.
Initialization, new sends, and ACK retirement preserve this actual ledger condition.

The active receive theorem covers a nonempty in-order range with an empty held store at its actual current frontier.
It retains both enabled runtime ledgers.
Its conditions concern the old endpoint invariants, checked input tuple and controls, sequence, offered space, forward ACK distance, and stored send times.
It derives the recovery update, actual ordered release, and new endpoint invariants.
With prior ACK preparation, it also preserves the time and edge conditions needed for output.
The store need not be a replacement initial state.

The reverse ACK theorem derives complete sender-buffer retirement and clears the actual timer ledger from a full covering ACK.
A wholly old data range instead creates a fresh immediate sequence-response cause.
The following enabled dispatch covers the unchanged receive cursor and releases no additional payload.

## Gateway guards

`ConntrackLifecycleEnabled` selects an actual existing record through the old lookup.
Zone, transport, table validity, route, and native filter conditions derive preparation and forwarding.
`WireForwardingEnabled` adds the actual packet and TTL conditions to derive checked transformed bytes.

`AdmissionEnabled` derives admission for fresh data and pure ACKs from old lane validity and input geometry.
The fresh-data proof uses the whole sequence span, peer window, ACK prefix, epoch, and disjoint coverage.
The pure-ACK proof uses its actual sequence, ACK, and window-history bounds.
Neither theorem requires a caller-supplied placement or post-state validity proof.

`CampusTCPServiceEnabled` retains typed evidence for the actual policy and ingress comparisons.
That evidence is bound to the current authentication prefix, imported configuration, live interfaces, namespace, and selected budget.
Successful construction of this preflight evidence is an explicit boundary.
The new theorem derives packet processing and emission from the old tracker, lane, route, filter, and TTL conditions.
It also derives the actual route result and current comparison status.
Repeated-payload admission needs a later readiness extension.

## Actual campus steps

`CampusTCPEnabled` lifts local guards through the current stored endpoint cursors.
It derives actual send, ACK, dispatch, write, read, and assignment steps.
`CampusTCPGatewayEnabled` derives actual service and fresh receiver-link custody from a pending ticket.
`CampusTCPDeliveryEnabled` derives actual data and full-ACK deliveries from live stored emissions.
Its frame identifies the updated receiver, retained peer, actual receipt, and appended endpoint operation.
The existing source proofs retain the actual packet bytes, NAT entry, policy, route, and lifetime evidence.

`CampusTCPOrigins.Report.work_valid` derives ticket identity validity from the checked history.
`CampusTCPChronology` derives each stored endpoint operation's strict order before the next joint slot.
These facts supply old-state guards from actual reports.
The caller supplies no replacement established endpoint or cursor history.

The application frame law identifies the selected endpoint's actual result, retained peer state, appended local step, and new global time bound.
The tests apply local laws to real ACK-enabled campus prefixes.
They also connect a newly generated packet to assignment on the current route owner.

## Finite schedules

`CampusTCPSchedule` projects the stored campus results to `BoundedProgress.Prefix`.
It does not execute another endpoint or gateway model.
Every checked slot retains its actual state, event, and result.
The prefix length is the number of evaluated operations.
An unsupported operation retains its unprocessed input suffix, which supplies no service slots.

`Report.cut` extracts an actual checked prefix from the same stored results.
A strict cut before the evaluated end is supported, including when a later operation stops the original input.
A supported complete prefix can append an actual computed step through `Report.appendStep`.
The constructor retains one joint checked history.
An abstract adapter over that actual transition relation can use the finite bounded-service theorem.
A concrete TCP adapter must still prove its own invariant, demand, persistence, and descent laws.

## Remaining transfer proof

The next result must compose these laws through one actual complete range:

```text
original send → ingress assignment → current gateway service
  → ordered receive release → actual covering ACK
  → reverse assignment and service → sender retirement
  → actual application read
```

It must derive each new phase's readiness from the initial checked state and the stated environment.
A list of successful operations or a final empty buffer does not supply that proof.
The broader result must charge failed rounds to actual custody drops.
It must retain a combined data-and-ACK loss bound and exclude spurious retries through clock and service conditions.
It must then cover the existing 400-byte and 600-byte held gaps and bounded planned transfer.
See the [progress design](research/CAMPUS_PROGRESS.md) and [custody guide](PACKET_CUSTODY.md).
All seven programs and the full campus objective remain OPEN.
