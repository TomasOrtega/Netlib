# Buffered cutovers and old packets

A late barrier controls new admissions to the output queue.
A packet that passed the hook earlier can remain queued and arrive after installation.
Netlib connects the barrier to a FIFO model and separates those two boundaries.

## Run the retained example

```sh
lake exe netlib buffered-lifecycle examples/drain/replay.json examples/drain/forbidden.json --from 1 --drained-at 3 --json
```

| Position | Modeled event | Pending queue afterward |
| --- | --- | --- |
| 0 | The old packet passes the open filter. | One old packet. |
| 1 | The installed barrier drops a later packet. | The same old packet. |
| 2 | One service slot delivers the old packet. | Empty. |
| 3 | The declared delivery boundary, at the end of the schedule. | Empty. |

The old delivered header belongs to the forbidden class.
It was admitted before the first boundary and served before the second boundary.
The successful report preserves that delivery in its history.
It establishes a clean pending queue at position 3 and excludes selected service outputs afterward under retained barriers.

The native experiment records two UDP packet traces, eight chain visits, and four raw conntrack snapshots.
A configured netem delay keeps the first packet pending across barrier installation.
Its distinct payload reaches the server afterward.
The later same-tuple packet reaches the installed barrier and drops.
Physical queue counts are 0, 1, 1, and 0 at the recorded checkpoints.

The [capture guide](../examples/drain/README.md), [original trace](../examples/drain/native/trace.txt),
[timestamps and socket observations](../examples/drain/native/observations.json), and
[checked evidence](../examples/drain/checked-evidence.json) preserve the experiment.
The [source research note](research/POSTROUTING_QUEUES.md) explains hook placement and the limits of queue counters.
The independent verifier checks the original artifacts without Lean outputs.
The [builder](../scripts/build_drain_example.py) projects that evidence into the buffered input.

The native queue has a finite configured limit.
The experiment reports no queue drop and stays below that limit.
The formal model uses an unbounded FIFO.
The capture does not prove general FIFO correspondence, a physical service rate, or a drain deadline.

## Two boundaries

`--from N` selects the admission cutover by zero-based schedule position.
Every later packet operation must select a certified late-filter barrier.
`--drained-at M` selects the delivery boundary.
Positions satisfy `N ≤ M ≤ schedule.length`.
The first boundary must select a nonempty suffix with at least one packet operation.
The second boundary can be the end of the schedule.

The checker replays the complete prefix to compute the actual model state at each boundary.
It never resets tracking or the queue at cutover.
It computes the backlog at position N and sums declared service capacities in `[N, M)`.
That sum must cover the backlog.
The service event that consumes the last old packet belongs to the draining segment.
Its served batch can still contain forbidden headers.
The delivery guarantee begins with events at position M.

This capacity condition is sufficient.
It charges every packet pending at cutover, including packets already outside the forbidden class.
A smaller budget can fail this certificate even when the actual pending headers are clean.
The certificate does not claim a minimal drain boundary.

The report separates `barrierCertified`, `drainBudgetSufficient`, `ready`, and `observationsAgree`.
`ready` covers the model's barrier and drain conditions.
`compliant` also requires agreement with all supplied lifecycle, pending-queue, and service observations.
Prefix mismatches prevent success and never replace the modeled state.

Exit code 0 means the certificate and observations agree.
Exit code 1 means a certificate condition or observation fails.
Exit code 2 means invalid input, unsupported processing, or resource exhaustion.

## Buffered input schema 1

The root fields are `schema`, `lifecycle`, `initialPending`, and `schedule`.
`schema` is the integer 1.
`lifecycle` embeds a complete [lifecycle schema 1](LIFECYCLE.md) input.
`initialPending` lists declared initial queued headers.
Their format uses dotted IPv4 addresses and bounded numeric protocol and port fields.
The delivered history starts empty.

Each schedule entry has one of these forms:

```json
{"type": "operation", "pending": null}
{"type": "serve", "capacity": 1, "served": [], "pending": []}
```

An operation consumes the next lifecycle event in its original order.
The complete schedule must consume every lifecycle event exactly once.
Packet processing and explicit deletion remain the supported lifecycle operations.
Only the operation's computed output enters the FIFO tail.
A drop or deletion adds no packet.
Neither a claimed output nor an observed queue value can enqueue a packet.

A service entry declares a natural-number capacity and no arrivals.
It removes exactly `min(capacity, pending.length)` packets from the FIFO head.
An idle interval with queued packets must declare zero service capacity.
Its required `served` list observes that batch, including order and repeated values.
Service leaves the tracking table unchanged in the model.

Every entry has `pending` as a complete observed header list or null when unobserved.
Null is distinct from a declared empty queue.
The native builder associates pending headers with its isolated recipe and socket payloads.
A physical qdisc count alone does not identify those headers.

Use the [traffic selection format](TRAFFIC.md) for the forbidden output class.
The default policy budget covers 100,000 partition cells across all post-cutover packet operations and all five state labels.
Repeated configurations are charged for every use.
Use `--budget N` after the boundary options to change it.
The budget does not bound schedule length, queue size, or total execution time.

## Drain theorem

The queue result applies to arbitrary packet types and a property of newly arriving packets.
If every post-cutover arrival has that property, the older prefix needs at most its initial length in service capacity.
New arrivals enter the tail and cannot overtake that prefix.
The total queue can keep growing under overload while the older prefix clears.
No bound on the new arrival rate is required for that finite-prefix result.

The buffered lifecycle supplies the arrival property from the certified late filters.
Its exact projection connects computed admissions and declared service events to the queue theory.
Sufficient service establishes a clean pending queue at the delivery boundary.
Every later modeled service batch is clean when the barrier remains in each selected configuration.
A compliant report transfers this result to supplied service observations.
The continuation theorem also covers arbitrary later modeled executions under those barriers.

The capacity counts service opportunities, not elapsed seconds.
A wall-clock deadline requires an external lower service bound and a correspondence argument.
The proofs do not assert native installation completion, complete queue visibility, absence of bypass, or full kernel behavior.
The [late-filter assumptions](REVOCATION.md) and ordinary lifecycle assumptions still apply.
