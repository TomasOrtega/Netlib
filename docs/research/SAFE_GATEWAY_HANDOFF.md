# Safe gateway handoff with selected packets pending

This note separates endpoint route selection, queued packet service, and gateway fencing.
The selected profile uses whole IPv4 UDP datagrams, fixed NAT, zone zero, and explicit gateway policies.
It does not establish automatic failover, universal packet draining, kernel refinement, or every concurrent route-lookup outcome.

## Pinned sources

Kernel reads use official Ubuntu source tagged `Ubuntu-6.8.0-117.117`.
The native environment reports `6.8.0-117-generic`.
These names do not establish source-to-binary equivalence.
[Ubuntu source](https://git.launchpad.net/~ubuntu-kernel/ubuntu/+source/linux/+git/noble/tree/net/core/dev.c?h=Ubuntu-6.8.0-117.117).

Userspace reads use iproute2 `v6.19.0`, commit `dac1bc6021693902b25a961227e289791e429b91`.
The native build uses the retained gzip archive from the earlier pinned recipe.
Its SHA-256 is `b39ac6a76f8299968408d3f2948ea59d9502b299d3e0c78c93658b65df3be5be`.
The separately downloaded xz archive has a different compression format and digest.
The inspected `q_netem.c` bytes agree across those two archives.
[Official release directory](https://www.kernel.org/pub/linux/utils/net/iproute2/).
[Official release tag](https://git.kernel.org/pub/scm/network/iproute2/iproute2.git/tag/?h=v6.19.0).
[Earlier build recipe](../../examples/lifecycle/Dockerfile).

## A route acknowledgment is not a drain observation

`ip route replace` builds a route request and calls `rtnl_talk`.
Without an answer object, that function requests an acknowledgment.
It checks the sender, sequence, and reply envelope before accepting a zero-error `NLMSG_ERROR` acknowledgment.
[Route request](https://git.kernel.org/pub/scm/network/iproute2/iproute2.git/tree/ip/iproute.c?id=dac1bc6021693902b25a961227e289791e429b91#n1637).
[Acknowledgment handling](https://git.kernel.org/pub/scm/network/iproute2/iproute2.git/tree/lib/libnetlink.c?id=dac1bc6021693902b25a961227e289791e429b91#n1003).

The kernel route handler calls `fib_table_insert`.
Its replacement path publishes a new alias with `hlist_replace_rcu`, retires the old alias, and can invalidate cached routes.
The Netlink receive path sends its acknowledgment after the request callback returns.
These calls do not provide an endpoint queue, link, gateway, or application completion observation.
[Route handler](https://git.launchpad.net/~ubuntu-kernel/ubuntu/+source/linux/+git/noble/tree/net/ipv4/fib_frontend.c?h=Ubuntu-6.8.0-117.117#n899).
[Replacement publication](https://git.launchpad.net/~ubuntu-kernel/ubuntu/+source/linux/+git/noble/tree/net/ipv4/fib_trie.c?h=Ubuntu-6.8.0-117.117#n1269).
[Netlink acknowledgment](https://git.launchpad.net/~ubuntu-kernel/ubuntu/+source/linux/+git/noble/tree/net/netlink/af_netlink.c?h=Ubuntu-6.8.0-117.117#n2517).

The ordinary unconnected UDP send path constructs its flow and calls `ip_route_output_flow`.
The connected-socket fast path can instead check a cached destination.
The selected producer uses explicit destination addresses with ordinary unconnected UDP sends.
This restricts the native profile; it does not prove atomic route selection for arbitrary concurrent kernel executions.
[UDP destination selection](https://git.launchpad.net/~ubuntu-kernel/ubuntu/+source/linux/+git/noble/tree/net/ipv4/udp.c?h=Ubuntu-6.8.0-117.117#n1172).
[Route lookup](https://git.launchpad.net/~ubuntu-kernel/ubuntu/+source/linux/+git/noble/tree/net/ipv4/udp.c?h=Ubuntu-6.8.0-117.117#n1282).

## Route selection precedes the endpoint queue

`ip_output` obtains the selected output device from the packet destination and supplies that device to the postrouting hook.
The ordinary continuation then reaches neighbor output and device transmission.
The device transmit path selects the interface qdisc before enqueueing the packet.
Thus, a postrouting NFLOG observation can expose the selected output ifindex before the packet waits in that qdisc.
[Postrouting device](https://git.launchpad.net/~ubuntu-kernel/ubuntu/+source/linux/+git/noble/tree/net/ipv4/ip_output.c?h=Ubuntu-6.8.0-117.117#n426).
[Neighbor output](https://git.launchpad.net/~ubuntu-kernel/ubuntu/+source/linux/+git/noble/tree/net/ipv4/ip_output.c?h=Ubuntu-6.8.0-117.117#n198).
[Qdisc selection](https://git.launchpad.net/~ubuntu-kernel/ubuntu/+source/linux/+git/noble/tree/net/core/dev.c?h=Ubuntu-6.8.0-117.117#n4412).

This observation occurs after route selection; it is not a direct trace of the FIB lookup instruction.
The interpretation requires stable endpoint hooks, default policy routing, the observed address binding, and no later redirect or encapsulation path.
Permanent neighbor entries prevent an unresolved-neighbor queue from introducing another selected waiting location.
These conditions belong to the finite profile.
[Earlier output-path analysis](POSTROUTING_QUEUES.md).

## Netem retains the selected interface

For its ordinary delay path, `netem_enqueue` computes a release time from kernel time and the configured delay.
It stores the packet in a queue ordered by release time.
`netem_dequeue` releases an eligible packet or schedules its watchdog.
Before returning a queued packet, it restores `skb->dev` from the qdisc's device.
[Queue insertion](https://git.launchpad.net/~ubuntu-kernel/ubuntu/+source/linux/+git/noble/tree/net/sched/sch_netem.c?h=Ubuntu-6.8.0-117.117#n390).
[Release time](https://git.launchpad.net/~ubuntu-kernel/ubuntu/+source/linux/+git/noble/tree/net/sched/sch_netem.c?h=Ubuntu-6.8.0-117.117#n548).
[Dequeue and device restoration](https://git.launchpad.net/~ubuntu-kernel/ubuntu/+source/linux/+git/noble/tree/net/sched/sch_netem.c?h=Ubuntu-6.8.0-117.117#n700).

The qdisc service path takes that qdisc's device and calls the device transmit function.
These calls do not repeat the endpoint's IPv4 route lookup.
Inference for this ordinary path: changing the endpoint route does not retarget a packet already queued on its earlier interface.
A packet selected for A can therefore reach A after later sends select B.
[Qdisc service](https://git.launchpad.net/~ubuntu-kernel/ubuntu/+source/linux/+git/noble/tree/net/sched/sch_generic.c?h=Ubuntu-6.8.0-117.117#n391).
[Device transmission](https://git.launchpad.net/~ubuntu-kernel/ubuntu/+source/linux/+git/noble/tree/net/sched/sch_generic.c?h=Ubuntu-6.8.0-117.117#n317).

The profile uses delay only, without jitter, loss, duplication, corruption, rate limits, slots, reordering, or a child qdisc.
The manual documents timer granularity limits.
Configured delay does not establish exact delivery time, global FIFO ordering, or a universal service deadline.
[Netem limitations](https://git.kernel.org/pub/scm/network/iproute2/iproute2.git/tree/man/man8/tc-netem.8?id=dac1bc6021693902b25a961227e289791e429b91#n252).

## Outgoing packet taps occur after queue service

`qdisc_restart` dequeues a packet before calling `sch_direct_xmit`.
That function reaches `dev_hard_start_xmit` and `xmit_one`.
`xmit_one` calls `dev_queue_xmit_nit` before invoking the device driver.
The tap clones the packet and labels the copy `PACKET_OUTGOING`.
[Service order](https://git.launchpad.net/~ubuntu-kernel/ubuntu/+source/linux/+git/noble/tree/net/sched/sch_generic.c?h=Ubuntu-6.8.0-117.117#n391).
[Transmit tap](https://git.launchpad.net/~ubuntu-kernel/ubuntu/+source/linux/+git/noble/tree/net/core/dev.c?h=Ubuntu-6.8.0-117.117#n3622).
[Outgoing clone](https://git.launchpad.net/~ubuntu-kernel/ubuntu/+source/linux/+git/noble/tree/net/core/dev.c?h=Ubuntu-6.8.0-117.117#n2328).

Consequently, the endpoint's outgoing AF_PACKET observation follows netem service on this path.
It cannot establish that the selected packet entered the queue before the route update.
The earlier endpoint postrouting observation and pending queue readback supply different evidence.
Later endpoint AF_PACKET and gateway ingress observations bind the delayed bytes to their selected interface.

## Early UDP checksum state

Passive NFLOG exports opaque packet bytes with `skb_copy_bits`.
The pinned NFLOG UAPI has no `NFULA_SKB_INFO` attribute or checksum-state flags.
`NFQA_SKB_INFO`, `NFQA_SKB_CSUMNOTREADY`, and `NFQA_SKB_CSUM_NOTVERIFIED` belong to NFQUEUE, which is a different protocol.
Their flag values are one and four respectively.
[NFLOG payload copying](https://git.launchpad.net/~ubuntu-kernel/ubuntu/+source/linux/+git/noble/tree/net/netfilter/nfnetlink_log.c?h=Ubuntu-6.8.0-117.117#n648).
[NFLOG attributes](https://git.launchpad.net/~ubuntu-kernel/ubuntu/+source/linux/+git/noble/tree/include/uapi/linux/netfilter/nfnetlink_log.h?h=Ubuntu-6.8.0-117.117#n46).
[NFQUEUE flags](https://git.launchpad.net/~ubuntu-kernel/ubuntu/+source/linux/+git/noble/tree/include/uapi/linux/netfilter/nfnetlink_queue.h?h=Ubuntu-6.8.0-117.117#n122).

An early outgoing packet can still require checksum completion.
The single-skb `udp4_hwcsum` path writes the folded UDP pseudoheader sum into the checksum field as a seed.
It also records the checksum start and offset.
`udp_send_skb` sends this partial-checksum path without first computing the final UDP checksum.
[UDP seed](https://git.launchpad.net/~ubuntu-kernel/ubuntu/+source/linux/+git/noble/tree/net/ipv4/udp.c?h=Ubuntu-6.8.0-117.117#n898).
[UDP send branch](https://git.launchpad.net/~ubuntu-kernel/ubuntu/+source/linux/+git/noble/tree/net/ipv4/udp.c?h=Ubuntu-6.8.0-117.117#n1026).

When required by device features, transmit validation calls `skb_checksum_help` later in the path.
That function sums the transport bytes, including the seed, and writes the complemented folded result.
A computed final zero becomes `CSUM_MANGLED_0`, whose transmitted value is `0xffff`.
It then sets `CHECKSUM_NONE`.
This selected completion path does not turn a computed zero into UDP checksum omission.
[Software completion](https://git.launchpad.net/~ubuntu-kernel/ubuntu/+source/linux/+git/noble/tree/net/core/dev.c?h=Ubuntu-6.8.0-117.117#n3341).
[Device validation](https://git.launchpad.net/~ubuntu-kernel/ubuntu/+source/linux/+git/noble/tree/net/core/dev.c?h=Ubuntu-6.8.0-117.117#n3732).

Therefore, disabled device offloads alone do not certify checksum completion at an earlier observation point.
The complete admission mode requires unchanged early bytes that already pass the strict IPv4 UDP codec.
The selected checker implements only this complete mode and rejects missing or invalid early UDP checksums.
A future partial-seed mode would need separate seed, kernel-path, and checksum-state premises.
NFLOG cannot supply those premises through nonexistent metadata.
Such completion would need to preserve early bytes and relate them to later wire bytes explicitly.

## What queue counters establish

The kernel defines queue length, backlog size, drops, requeues, and overlimits.
The iproute2 statistics printer exports these values.
Its netem JSON delay printer uses seconds.
These counters contain no UDP payload identity or model ticket identifier.
[Kernel queue statistics](https://git.launchpad.net/~ubuntu-kernel/ubuntu/+source/linux/+git/noble/tree/include/uapi/linux/gen_stats.h?h=Ubuntu-6.8.0-117.117#n51).
[Statistics printer](https://git.kernel.org/pub/scm/network/iproute2/iproute2.git/tree/tc/tc_util.c?id=dac1bc6021693902b25a961227e289791e429b91#n747).
[Netem JSON units](https://git.kernel.org/pub/scm/network/iproute2/iproute2.git/tree/tc/q_netem.c?id=dac1bc6021693902b25a961227e289791e429b91#n764).

An isolated queue with one selected pending input supports a narrower interpretation than a shared queue with unrelated traffic.
Even an empty qdisc does not establish empty driver, link, gateway, receiver, or application buffers.
Resetting netem clears its queues; deletion is not evidence that queued packets completed service.
The selected completion evidence must therefore join queue readbacks with the actual packet's later gateway outcome.
[Queue reset](https://git.launchpad.net/~ubuntu-kernel/ubuntu/+source/linux/+git/noble/tree/net/sched/sch_netem.c?h=Ubuntu-6.8.0-117.117#n784).

## Model interpretation and checker seam

The model ticket records the gateway selected at route admission.
Changing a later endpoint owner does not rewrite that ticket.
Serving the ticket applies its assigned gateway's current policy and connection state.
The model's safe fence requires both endpoint owners to select B and no pending ticket assigned to A.
These are explicit model conditions, not consequences of a route command's exit status.

Finite evidence must bind each ticket to an earlier endpoint admission observation and its selected output ifindex.
It must retain queue configuration, positive pending counts, complete route and policy readbacks, and later unchanged packet observations.
It must observe the selected ticket's completion or denial before declaring it absent from the model's pending set.
Current-policy denial remains observable even when the ticket was admitted under an earlier policy.

The checker separates raw evidence handling from the protocol-specific transition adapter.
The shared module owns command references, intervals, observer lifetimes, raw packet joins, and consumption accounting.
Its named adapters cover the existing replication capture and this split admission/service capture.
The existing replication verifier and pinned artifacts remain unchanged.
The compatibility adapter calls that verifier and normalizes its checked report.
The new adapter owns tickets, route ownership, readiness, current policy, and the finite drain condition.

The interface exposes opening a named profile, reading a boundary, binding a packet, and finishing the audit.
It must not expose a large caller-defined grammar of producer fields or synthesize earlier packet observations from later wire captures.
Both actual capture formats must exercise this interface and retain their contradiction regressions.
[Existing authoritative verifier](../../scripts/check_replication_capture.py).
[Existing contradiction tests](../../scripts/test_check_replication_capture.py).

## Selected native observations

The selected capture contains seven UDP inputs, six forwarded outputs, and one current-policy drop.
Its evidence includes 84 kernel dumps, 26 data AF_PACKET records, 27 NFLOG records, and 30 synchronization frame copies.
All ten directed neighbor entries are permanent before the initial boundary; the profile rejects additional ARP records.
[Native event manifest](../../examples/safe-handoff/native/capture.json).
[Evidence checker](../../scripts/check_safe_handoff_capture.py).

The first delayed packet has an earlier complete endpoint postrouting observation selecting A.
The isolated `cal` queue retains one packet with a 67-byte backlog after both route changes and the overtaking B reply.
Later unchanged AF_PACKET, gateway NFLOG, tracing, and socket observations bind that packet to successful A service.
The selected queue then reports zero pending packets, one transmitted packet, and zero drops before its deletion and A's fence.

The second delayed packet selects B while its policy permits the protected flow.
Its isolated queue remains pending while the controller installs the deny policy.
Later B observations show tracking followed by the current forward drop, without an output packet or socket delivery.
The final permit installation allows both subsequent directions through B.

Every early admission has a complete, nonzero valid UDP checksum in this capture.
The checker preserves those early bytes and compares them directly with later source and gateway ingress bytes.
It does not obtain an earlier packet by copying a future wire observation.
[Raw evidence interface](../../scripts/capture_evidence.py).
[Admission and interface tests](../../scripts/test_capture_evidence.py).

The native barriers concern these selected delayed packets, with their actual completion observations and isolated queue readbacks.
Queue length is not the model's outstanding-ticket count during arbitrary link, driver, or gateway processing.
The general model's fence condition is separate from this finite observation sequence.
The checker tests contradictory timing, interface bindings, source bytes, policy, queue state, commands, and reused artifacts.
[Protocol contradiction tests](../../scripts/test_check_safe_handoff_capture.py).
