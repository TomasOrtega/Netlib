# Postrouting barriers and output queues

This note records source reads for the private [drain capture](../../examples/drain/README.md).
The reads use upstream Linux `v6.8` and iproute2 `v6.17.0`.
The captured kernel reports `6.8.0-117-generic`.
These source reads do not establish equivalence with that distribution kernel.

## Ordinary IPv4 output order

`ip_forward` runs `NF_INET_FORWARD` with `ip_forward_finish` as its continuation.
That continuation calls `dst_output`.
This describes the ordinary software path, subject to the source's earlier checks and offload branch.
[Linux `ip_forward.c`](https://github.com/torvalds/linux/blob/v6.8/net/ipv4/ip_forward.c#L61-L76).
[Forward hook call](https://github.com/torvalds/linux/blob/v6.8/net/ipv4/ip_forward.c#L153-L155).

`ip_output` runs `NF_INET_POST_ROUTING` before its `ip_finish_output` continuation.
For a normal small packet, this continuation reaches `ip_finish_output2`, which calls neighbor output.
[Linux `ip_output.c`](https://github.com/torvalds/linux/blob/v6.8/net/ipv4/ip_output.c#L402-L412).
[Finish output](https://github.com/torvalds/linux/blob/v6.8/net/ipv4/ip_output.c#L280-L312).
[Neighbor output call](https://github.com/torvalds/linux/blob/v6.8/net/ipv4/ip_output.c#L216-L225).

The cached neighbor output path calls `dev_queue_xmit` after adding the link header.
The transmit path selects the device qdisc and calls `__dev_xmit_skb` when that qdisc has an enqueue function.
[Linux `neighbour.h`](https://github.com/torvalds/linux/blob/v6.8/include/net/neighbour.h#L489-L505).
[Linux `dev.c`](https://github.com/torvalds/linux/blob/v6.8/net/core/dev.c#L4051-L4059).

Netfilter orders registered hooks by increasing priority.
The IPv4 constants place source NAT at `100` and conntrack confirmation at `INT_MAX`.
The IPv4 conntrack hooks register `nf_confirm` at postrouting with that confirmation priority.
[Hook insertion](https://github.com/torvalds/linux/blob/v6.8/net/netfilter/core.c#L137-L181).
[Priority constants](https://github.com/torvalds/linux/blob/v6.8/include/uapi/linux/netfilter_ipv4.h#L28-L50).
[Confirmation hook](https://github.com/torvalds/linux/blob/v6.8/net/netfilter/nf_conntrack_proto.c).

Inference from these calls: a postrouting filter at `110` precedes confirmation and the ordinary egress qdisc.
A packet can complete that filter and confirmation, then wait in the output queue.
Installing a later filter does not imply that this queued packet is absent.
This is a path interpretation, not a kernel refinement proof.
[Postrouting continuation](https://github.com/torvalds/linux/blob/v6.8/net/ipv4/ip_output.c#L402-L412).
[Qdisc handoff](https://github.com/torvalds/linux/blob/v6.8/net/core/dev.c#L4051-L4059).

## What netem delays

`netem_enqueue` computes a release time from the current kernel time and configured delay.
`netem_dequeue` checks that time before removal and otherwise schedules its watchdog.
Its internal queue orders packets by release time.
This is not a general FIFO guarantee when delay varies.
[Linux `sch_netem.c`](https://github.com/torvalds/linux/blob/v6.8/net/sched/sch_netem.c#L362-L389).
[Release time](https://github.com/torvalds/linux/blob/v6.8/net/sched/sch_netem.c#L501-L551).
[Dequeue and watchdog](https://github.com/torvalds/linux/blob/v6.8/net/sched/sch_netem.c#L642-L714).

The iproute2 manual documents timer granularity limits and possible reordering from jitter.
Thus, a configured four-second delay does not prove an exact delivery time or a universal deadline.
[iproute2 netem manual](https://github.com/iproute2/iproute2/blob/v6.17.0/man/man8/tc-netem.8#L237-L250).
[Jitter example](https://github.com/iproute2/iproute2/blob/v6.17.0/man/man8/tc-netem.8#L320-L336).

The capture uses delay only, without jitter, loss, duplication, rate limits, or a child qdisc.
The retained command and four JSON exports show that configuration.
The `tc` binary is version `6.17.0`; the separate `ip` binary is version `6.19.0`.
[Queue command](../../examples/drain/native/queue-command.json).
[Pending queue export](../../examples/drain/native/qdisc-pending.json).
[tc version](../../examples/drain/native/tc-version.txt).
[ip version](../../examples/drain/native/iproute2-version.txt).

## Counter meaning and evidence limits

The kernel statistics structure defines `qlen` as queue length and `backlog` as queue backlog size.
It also reports drop, requeue, and overlimit counters.
The iproute2 printer copies these fields to their JSON names.
Its netem JSON delay printer uses seconds.
[Linux queue statistics](https://github.com/torvalds/linux/blob/v6.8/include/uapi/linux/gen_stats.h#L48-L61).
[iproute2 statistics printer](https://github.com/iproute2/iproute2/blob/v6.17.0/tc/tc_util.c#L694-L757).
[iproute2 netem time printer](https://github.com/iproute2/iproute2/blob/v6.17.0/tc/q_netem.c#L58-L70).

These counters contain no socket payload identity or pre-barrier packet label.
Inference: total queue length cannot establish the size of an old packet prefix when unrelated traffic shares that queue.
An empty qdisc also does not report downstream driver, link, receiver, or application buffers.
Those objects are outside this statistics structure.
[Queue statistics fields](https://github.com/torvalds/linux/blob/v6.8/include/uapi/linux/gen_stats.h#L48-L61).

Neighbor resolution can hold packets in a separate queue before device transmission.
The capture therefore uses permanent neighbor entries and disables IPv6 before creating links.
The recipe, neighbor export, and namespace readbacks retain that isolation evidence.
[Linux neighbor queue](https://github.com/torvalds/linux/blob/v6.8/net/core/neighbour.c#L1145-L1161).
[Capture recipe](../../examples/drain/capture.sh).
[Router neighbors](../../examples/drain/native/neighbors.json).
[Router settings](../../examples/drain/native/router-settings.txt).

## Connection to the finite model

The experiment records one old UDP payload in the queue before the barrier and receives that payload after installation.
A distinct later payload reuses the same original tuple and receives a traced late drop.
The verifier joins those traces to active rule exports and raw conntrack bytes.
It also checks queue counters and monotonic socket times.
[Socket observations](../../examples/drain/native/observations.json).
[Offline verifier](../../scripts/check_drain_capture.py).

The model's queue identity, FIFO service, and loss assumptions remain explicit interpretation conditions.
Finite native agreement does not prove those conditions for every execution.
A drain theorem must state its service assumptions and the finite old prefix separately.
No source read or retained observation here establishes universal liveness, complete buffering visibility, or a physical drain-time bound.
