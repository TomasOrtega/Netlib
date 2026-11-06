# Sparse TCP gateway observations

A gateway can observe a later data range before a lower range.
It records the actual covered bytes and passes each admitted packet to the current forwarding pipeline immediately.
The observation ledger does not wait for a hole to close.
Host [receive storage](TCP_RECEIVE_GAPS.md) remains a separate operation.

```sh
lake exe netlib campus-tcp examples/tcp-sparse-admission/trace.json --json
```

## Coverage and sources

Each lane keeps sorted, disjoint original runs.
Every run has an internally allocated first-source ID and the index of its actual committed packet observation.
Input cannot supply coverage, source IDs, or a successful post-state.

The lane separates these values:

| Value | Meaning |
| --- | --- |
| `observed` | End of the contiguous covered prefix, starting at the data sequence base. |
| `highEnd` | Greatest observed end position. |
| `uniqueBytes` | Number of different observed bytes. |
| `acknowledged` | Cumulative acknowledged position. |
| `outstanding` | Sequence span from the acknowledged position to `highEnd`, including holes. |

Observing `[600,800)` gives prefix 0, high end 800, and 200 unique bytes.
Observing `[200,400)` next gives prefix 0, high end 800, and 400 unique bytes.
A cumulative ACK cannot pass either hole.
After `[0,200)` arrives, the prefix becomes 400 while the high end stays 800.

An exact contained repeat must match bytes from one actual earlier original range.
It keeps that range's first-source record and adds no unique bytes or source ID.
The new packet still adds an actual observation and advances the checkpoint cut.
Mixed overlap and conflicting copies have explicit scope stops.

`Theory.SparseCoverage` proves insertion existence, valid coverage, exact sources, byte indices, and hole bounds.
`Admission.fresh_data_allowed` derives gateway acceptance from old valid lanes and input range, ACK, window, and epoch bounds.
It needs no successful-placement or post-state premise.
`AdmissionCoverageFacts` binds every source index to the actual observation ledger.
`CheckpointObservationHistory` locates that observation in the same reachable gateway history.
`CheckpointCoverageFacts` supplies its earlier operation, bytes, entry, direction, and payload index.
The source is not a caller-supplied certificate or a second replay.

## Sequence and window rules

New data must fit the current advertised right edge at its actual sequence end.
A unique-byte count cannot replace this sequence-space check.
The window rule uses [RFC 9293, section 3.8.6](https://www.rfc-editor.org/rfc/rfc9293.html#section-3.8.6).
These gateway evidence rules do not claim that RFC 9293 defines firewall admission.

Known repeats can remain valid after the peer window shrinks.
ACK and window freshness still use the current packet.
The cumulative ACK bound uses the peer's contiguous prefix, not its greatest end.
The selected byte epoch and outstanding sequence span retain their existing limits.

An empty ACK can use a sequence position from the lane base through its greatest observed end, inclusive.
It adds no coverage and needs no data-window space.
An empty ACK beyond that end remains outside this selected profile.
The rule does not infer missing payload from an ACK sequence.

## Exact transfer

The checkpoint image contains both complete lanes and their original source records.
Exact installation preserves covered runs, holes, IDs, and observation indices.
Changed coverage makes a source image stale even when its greatest end is unchanged.
The current transition cut also remains part of the installation check.

The example sends four actual 200-byte ranges within an 800-byte flight bound.
Primary service first observes `[600,800)` and then `[200,400)`.
The original lower packets are not served before their retries.
The model does not infer an explicit loss disposition from those omissions.

Two holes cross the planned gateway transfer.
A real timer retry supplies `[0,200)` to the standby for the first time.
It creates new observation coverage and releases 400 ordered bytes at the host.
An actual ACK retires 400 sender bytes.
A later retry fills `[400,600)`.
The application reads all 800 bytes once, in write order.
Reverse and wrapped traces use the same source and read-origin checks.

Every service still uses current ingress and forwarding permission.
A known range grants no cached permission after Logoff.
Denied service emits no packet and cannot fill the receiver's missing prefix.

## Reports and raw checks

After actual sparse observation, a lane reports `coverage` with `highEnd`, `uniqueBytes`, `nextID`, and original `runs`.
Each run reports its position, end, source ID, observation index, and payload.
Source allocation order retains evidence of earlier reordering after all holes close.
Ordinary in-order reports omit this additional object.

Campus `sparseAssurance` has scope `gateway-observation-sources`.
`checked` proves the actual source bindings and retains the existing campus application assurance.
It permits holes, including holes in a fenced primary's archived state.
Each lane summary separately reports `prefixComplete`.
That field concerns coverage through the greatest observed end.
It does not establish that every sender byte arrived or that future work will progress.

The raw checker starts from empty tracking and admission state:

```sh
lake exe netlib tcp-admission TRACE.json --json
```

Schema 1 accepts `zone`, `original`, `translated`, and `packetsHex`.
Checked raw SYN, SYN/ACK, and ACK packets build the selected startup history.
The declared mapping uses fixed permit routes to its two data endpoints.
There is no supplied coverage state or source identity.
This primitive checks gateway mechanics; it does not prove endpoint writes or campus authentication.
After a selected stop, later transport bytes remain unprocessed.
All hex syntax is checked before replay.

The [research and independent evidence](research/TCP_SPARSE_ADMISSION.md) states the source rules and corpus.
The [bounded-progress design](research/CAMPUS_PROGRESS.md) identifies the next architecture proof boundary.
The [custody extension](PACKET_CUSTODY.md) records pending packets, explicit loss, and copies.
It also supplies general bounded-service theorems.
The [recovery progress proof](TCP_RECOVERY_PROGRESS.md) covers one fresh range with two combined data or ACK drops.
Progress through held gaps and physical correspondence remain open.
General overlap handling, broader congestion control, close, and native TCP tracking refinement also remain open.
All seven programs and the full campus objective remain OPEN.
