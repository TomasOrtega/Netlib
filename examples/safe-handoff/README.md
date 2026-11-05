# Queued gateway handoff

This example separates route admission from gateway service for a replicated IPv4 UDP binding.
It uses the [replication capture](../replication/README.md) as its pinned parent.
The earlier producer and its saved observations remain unchanged.

The selected runtime uses Ubuntu kernel `6.8.0-117-generic`, conntrack-tools 1.4.9, and iproute2 6.19.0.
The new image builds `tc` from the retained iproute2 source and invokes `/opt/netlib/sbin/tc` explicitly.
The parent also contains a separate system `tc`; that binary does not configure the selected queues.

## Admission and service

The topology retains the same client, two gateways, server, fixed tuples, and dedicated synchronization link.
Both host routes initially select the primary.
Permanent neighbor bindings on all ten directed links avoid neighbor-resolution queues during the selected execution.

The capture follows these operations:

1. A real primary request establishes the source binding.
2. FTFW replication and explicit standby commit prepare the destination before route changes.
3. A client netem queue holds a primary-bound request for 2.5 seconds.
4. Both host routes change to the standby while that request remains queued.
5. A standby request and reply complete before the older primary request.
6. The primary serves its earlier request under its current policy.
7. Its actual completion and empty selected queue precede the primary fence.
8. Another client queue holds a standby-bound request for 1.5 seconds.
9. Standby deny policy is installed while that request remains queued.
10. The standby drops it under the new policy.
11. Permit is restored, and both directions continue through the standby.

Protected tickets use identifiers zero through five.
Their service order is one, two, zero, three, four, five.
The bootstrap packet creates the selected binding before protected admission begins.
It has no ticket identifier.

## Raw observations

The retained run contains 20 events, seven datagrams, 84 kernel dumps, and 27 NFLOG observations.

Endpoint postrouting NFLOG retains each admitted IPv4 datagram and its selected output interface.
The producer waits until each unique admission record is present before continuing its control sequence.
The saved poll records retain the original file, line, record, and read interval.
The checker requires complete valid IPv4 and UDP checksums at admission.
It does not repair partial checksums or invent Ethernet headers.

Outgoing packet-socket observations occur after qdisc service.
They therefore show release, rather than the earlier route decision.
Separate gateway ingress, tracked, egress, trace, socket, and kernel-table observations establish each selected outcome.

Every boundary retains both gateway tables, all rulesets, network readbacks, and both controlled qdisc states.
The qdisc records include configuration, packet and byte counters, backlog, queue length, drops, and requeues.
Each held frame has a 67-byte backlog while pending and one completed packet when its queue empties.
The capture retains the actual raw values without normalization.

A zero qdisc backlog alone does not establish physical drain.
The selected barrier also joins the admitted ticket to its gateway outcome and endpoint observation.
The primary fence follows completion of every modeled primary ticket and both route changes.

## Reproduce

Build the [pinned parent](../replication/README.md), then run:

```sh
examples/safe-handoff/recapture.sh /tmp/netlib-safe-handoff-recapture
```

The recipe builds offline from the existing parent and runs without external networking or host mounts.
The checker requires the selected kernel and tool profile.
The fresh run has its own packet identifiers, queue seeds, timing, and hashes.

## Scope

The formal model permits service by ticket identifier without imposing a global FIFO order.
A ticket retains its admitted gateway through route changes.
Gateway service uses current installed policy.
The finite capture supplies observations for that selected implementation profile.

It does not prove a universal physical drain bound or bounded scheduler delay.
Queue capacity, uncontrolled traffic, loss, expiry, split brain, automatic failure detection, and broader protocols need additional models.
