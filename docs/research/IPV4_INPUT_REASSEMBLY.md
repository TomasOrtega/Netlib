# IPv4 input buffering and reassembly

This note separates protocol requirements, inspected Ubuntu behavior, and recommended model boundaries.
All Linux links select `Ubuntu-6.8.0-117.117`.
Source inspection does not establish equivalence with a running kernel binary.
[Pinned reassembly source][queue].

## Protocol requirements

IPv4 identifies fragment families by source, destination, protocol, and identification.
Offsets count eight-byte units; MF distinguishes the final fragment.
The reconstructed total length includes its IP header.
RFC 791's example accepts overlaps by using later bytes.
Its example also flushes a matching queue when an unfragmented packet arrives.
Those example choices do not describe the Linux path below.
[RFC 791, section 3.2](https://www.rfc-editor.org/rfc/rfc791.html#section-3.2).

RFC 815 describes a hole-list algorithm that supports arbitrary arrival order, overlap, and duplication.
It provides an algorithm, rather than a modern Linux overlap policy.
[RFC 815, sections 1–3](https://www.rfc-editor.org/rfc/rfc815.html).

RFC 5722 prohibits overlapping **IPv6** fragments.
It does not introduce an IPv4 standards requirement.
Linux shares its interval insertion implementation between IP versions and explicitly distinguishes duplicates from overlaps.
[RFC 5722, sections 1 and 4](https://www.rfc-editor.org/rfc/rfc5722.html#section-4), [shared insertion][insert].

Reassembly must preserve congestion indications.
CE with an ECT fragment must produce CE or a dropped packet.
CE must not be propagated when another contributing fragment is Not-ECT.
Identical fragment ECN codepoints must remain unchanged.
[RFC 3168, section 5.3](https://www.rfc-editor.org/rfc/rfc3168.html#section-5.3).

RFC 1122 recommends a fixed reassembly timeout between 60 and 120 seconds.
It requires incomplete-datagram disposal after timeout and generally requires an ICMP reply when fragment zero exists.
[RFC 1122, section 3.3.2](https://datatracker.ietf.org/doc/html/rfc1122#section-3.3.2).

Atomic IPv4 datagrams have DF set, MF clear, and offset zero.
Their identification field must be ignored by devices examining IPv4 headers.
Non-atomic datagrams retain identification uniqueness requirements.
[RFC 6864, sections 4.1–4.3](https://www.rfc-editor.org/rfc/rfc6864.html#section-4.1).

RFC 1812 prohibits ordinary routers from reassembling transit datagrams before forwarding.
The inspected gateway instead uses Linux's enabled conntrack defragmentation path.
Describe that selected middlebox behavior explicitly.
[RFC 1812, section 5.2.6](https://www.rfc-editor.org/rfc/rfc1812.html#section-5.2.6), [netfilter defragmentation][defrag].

## Hook order and queue identity

`ip_rcv_core` checks version, IHL, header checksum, and total-length availability before prerouting.
It trims link padding to the IP total length.
These failures occur before fragment queue lookup.
[IPv4 receive validation][input].

Enabled defragmentation runs at prerouting priority -400.
Ordinary raw processing follows at -300, conntrack at -200, and destination NAT at -100.
Pending fragments and reassembly errors return `NF_STOLEN`.
Only successful completion continues through later hooks.
Successfully reassembled packets receive `ignore_df = 1`.
[Hook registration and verdicts][defrag], [priority constants][priority].

The hook bypasses packets marked untracked and qualifying `IP_NODEFRAG` sockets.
An unfragmented packet bypasses `ip_defrag`; it does not flush a same-key pending queue.
The selected model should exclude these bypass configurations or represent them separately.
[Defragmentation hook][defrag].

The queue directory belongs to one network namespace.
Its key contains source, destination, protocol, identification, defragmentation user, and `vif`.
`vif` is the L3 master interface index, rather than the ordinary ingress interface index.
Different ordinary interfaces can therefore contribute to one queue.
[Queue key][key], [L3 master selection][domain].

Netfilter derives its user from the input, output, or bridge-input base plus the attached conntrack zone identifier.
The zone identifier respects the conntrack direction.
Without an attached template or connection, the default zone applies.
A zone assignment intended to isolate fragments must precede priority -400.
[User construction][user], [zone direction][zone], [hook priorities][priority].

Recommendation: keep namespace isolation outside the table, or include it explicitly in the model key.
Represent effective user and L3 master scope explicitly.
Do not replace either field with an ordinary ingress-port identifier.
[Queue construction][key], [user construction][user], [L3 master selection][domain].

## Exact insertion sequence

The following sequence assumes successful allocation, serialized queue operations, and `ipfrag_max_dist = 0`.
It describes IP payload intervals as `[start, end)`.
[Queue processing][queue], [distance control][sysctl].

1. Find or create the keyed queue.
   Derive `start = 8 * fragmentOffset` and `end = start + payloadLength`.
   DF does not prevent fragmented input from entering this path.
   [Queue lookup and normalization][queue].
2. For MF clear, reject `end < queue.len`.
   Also reject a different end when a final fragment was already observed.
   Otherwise set LAST and assign `queue.len = end`.
   [Final-length validation][length].
3. For MF set, round `end` down to an eight-byte boundary and trim excess payload bytes.
   If the new end exceeds `queue.len`, reject an already final queue; otherwise increase its length.
   A normalized empty payload destroys the queue.
   [MF normalization][length].
4. Insert the normalized interval using the run rules below.
   A duplicate discards only the incoming packet.
   An overlap destroys the whole pending queue.
   [Interval insertion][insert], [error handling][queue].
5. Successful insertion adds payload length to `meat` and records ECN, maximum sizes, timestamp, and ingress interface.
   Offset zero sets FIRST.
   [Accepted-fragment updates][accepted].
6. Complete only when FIRST and LAST are set and `meat = queue.len`.
   Validate combined ECN and reconstructed total length before returning a packet.
   [Completion trigger][accepted], [reconstruction validation][reasm].

Final-length changes happen **before** duplicate classification.
A duplicate can set LAST without adding payload or triggering completion.
It does not update ECN, maximum sizes, first-header selection, timestamps, or the deadline.
Different payload bytes do not prevent duplicate classification.
[Length ordering][length], [duplicate return][queue], [range-only insertion][insert].

There is no early `end <= 65535 - IHL` check in this insertion path.
An incomplete oversized family can remain buffered.
Completed reconstruction rejects total length above 65535.
Modeling every excessive offset as an immediate Linux drop would be incorrect.
[End calculation][length], [final size check][reasm].

Killing a queue removes it from the hash table.
There is no retained overlap tombstone in this path.
Later fragments with the same key can create another queue.
[Queue destruction][kill], [queue creation][allocation].

## Runs, duplicates, and overlap

The tree stores ordered runs of accepted fragments.
Each run covers one contiguous interval and retains its constituent packets.
Only an arrival adjacent to the global tail extends its final run.
An internal gap-filling insertion creates a separate run.
Linux does not merge all adjacent runs afterward.
[Run representation and construction][runs], [insertion branches][insert].

An incoming interval entirely contained in one existing run is a duplicate.
This includes intervals spanning several constituent packets within that run.
Any other intersecting interval is an overlap.
An interval spanning separate adjacent runs is therefore an overlap.
[Range classification][insert].

For example, arrivals `[0,8)`, `[8,16)`, and `[24,32)` leave the first two intervals in one run.
An incoming `[0,16)` is then a duplicate.
Instead, arrivals `[0,8)`, `[16,24)`, and `[8,16)` leave three runs.
An incoming `[0,16)` is then an overlap.
These examples assume MF set and an unfinished family.
[Run construction][runs], [range classification][insert].

Recommendation: preserve run provenance, rather than merging every contiguous payload interval.
The existing strict family assembler rejects duplicates and metadata differences, so it cannot serve as this ingress transition.
[Native insertion][insert], [existing strict module](../../Netlib/Protocol/IPv4Fragmentation.lean).

## Reconstructed metadata

The resulting IP header comes from the accepted fragment at offset zero.
The completing packet object is morphed to that stored head when necessary.
TTL and the DSCP portion of TOS therefore come from fragment zero, regardless of arrival order.
Reassembly itself does not decrement TTL.
[Head selection][head], [header reconstruction][reasm], [later forwarding decrement][forward].

Successfully inserted fragments contribute ECN codepoints to a set.
The completion table rejects any Not-ECT mixture with ECT or CE.
CE combined with ECT becomes CE.
Mixed ECT(0) and ECT(1), without CE, retain fragment zero's ECN codepoint.
Discarded duplicates contribute no ECN evidence.
[ECN aggregation][accepted], [ECN table][ecn], [TOS update][reasm].

`max_size` records the largest accepted fragment's trimmed payload length plus that fragment's header length.
`max_df_size` records the same maximum restricted to accepted DF fragments.
The reassembled packet receives `frag_max_size = max(max_size, max_df_size)`.
It receives DF and `IPSKB_FRAG_PMTU` exactly when those two maxima are equal.
MF and fragment offset become zero.
The total length and header checksum are recomputed.
[Size accumulation][accepted], [reconstructed flags][reasm].

The packet device becomes the completing fragment's device.
The queue's saved ingress interface and timestamp come from the last successful insertion.
These values do not establish per-interface queue isolation.
[Accepted metadata][accepted], [completion metadata][reasm], [timestamp reconstruction][finish].

## Deadlines and resources

Creation schedules expiry at current jiffies plus `ipfrag_time`.
Normal insertion and duplicate arrival do not refresh that timer.
The default is 30 seconds; `ipfrag_max_dist` defaults to 64.
[Timer creation][allocation], [queue processing][queue], [defaults][defaults], [timeout constant][time].

Positive `ipfrag_max_dist` enables a source-peer disorder heuristic, scoped by source address and L3 master.
Excessive distance purges the current payload and restarts its timer before processing the arriving fragment.
Setting it to zero disables this extra transition.
Use zero in initial native probes and record that setting.
[Peer creation][peer], [distance and reinitialization][distance], [control documentation][sysctl].

Expiry destroys the queue and increments reassembly-failure and timeout counters.
An ICMP reassembly timeout additionally requires fragment zero, a usable device, and successful routing.
For conntrack-input users, a nonlocal route suppresses that ICMP reply.
Transit expiry therefore normally produces no ICMP packet.
[Expiry processing][expiry].

Expiry routes the original destination before destination NAT.
A locally assigned VIP can therefore permit an ICMP timeout, even when destination NAT would forward completed traffic.
Record that control output separately from the selected UDP transit output.
[Expiry route lookup][expiry], [destination NAT priority][priority].

Unqualified nftables zone assignment attaches a conntrack template covering both directions.
Queued fragment handling retains that template.
`skb_orphan` releases socket ownership without clearing conntrack.
[Zone template assignment][nft-zone], [queued packet handling][queue], [socket ownership release][orphan].

ICMP quotation construction calls `nf_ct_attach` on the stored fragment.
Its wrapper accepts any nonzero attachment, and the conntrack hook copies templates without excluding them.
LOCAL_OUT tracking removes the packet's template attachment, then passes that template into ICMP error association.
`nf_ct_zone_tmpl` selects its inherited zone for reverse-quote lookup.
[ICMP attachment][icmp-glue], [attachment wrapper][attach-wrapper], [attachment hook][attach], [tracking entry][ct-in], [error lookup][icmp-lookup], [template zone][template-zone].

The selected BOTH-direction template profile therefore uses the original queue zone for timeout association.
Directional templates, mark-derived zones, and output-zone changes require separate semantics.
[Zone assignment][nft-zone], [template zone selection][template-zone].

A deterministic model can process deadlines at `now >= deadline` before an arrival.
This is a selected scheduling abstraction.
Kernel callbacks run through asynchronous timers, so exact boundary behavior requires an explicit event-order assumption.
[Kernel timer and queue locking][allocation], [expiry callback][expiry].

All event times and queue timeouts must use the same abstract monotonic unit.
Use nanoseconds in native replay and convert the sysctl's seconds accordingly.
[Kernel timeout control][sysctl], [timer scheduling][allocation].

Memory accounting includes queue storage and packet `truesize`, rather than payload length alone.
`inet_frag_find` refuses lookup when memory exceeds `ipfrag_high_thresh`, including lookups for already existing queues.
The inspected path does not perform an LRU eviction down to `ipfrag_low_thresh`.
That low threshold is documented as obsolete since Linux 4.17.
[Accounting and admission][allocation], [packet accounting][accepted], [obsolete control][sysctl].

Recommendation: explicitly exclude allocation failures and memory pressure from the first selected transition.
A synthetic payload-byte limit is an application policy, rather than Linux memory-accounting equivalence.
[Native accounting][allocation], [native packet charge][accepted].

## Forwarding and re-fragmentation

The completed packet reaches conntrack and NAT before route selection and forwarding.
Forwarding checks TTL expiry before its MTU guard, then decrements surviving TTL before the forward hook.
[Prerouting priorities][priority], [receive continuation][input], [forward path][forward].

For oversized DF packets, `ip_exceeds_mtu` first rejects an original maximum fragment size above the outgoing MTU.
Otherwise `ignore_df` permits forwarding the larger reconstructed packet.
DF-clear packets pass this guard regardless of reconstructed size.
[Forwarding MTU guard][mtu].

Output calls `ip_fragment` whenever `frag_max_size` is nonzero, even when the reconstructed packet fits the route MTU.
`ip_do_fragment` caps its working MTU at that retained maximum.
A 600-byte ingress MTU and 1500-byte egress MTU therefore still produce output fragments.
For ordinary IHL-five fragmentation, the retained maximum can be 596 bytes because payload boundaries require alignment.
[Output trigger][output], [output size cap][refragment].

`ip_fragment` permits DF fragmentation only with `ignore_df` and an original maximum no larger than the route MTU.
Otherwise it attempts Fragmentation Needed and drops the packet.
The fragment budget uses the retained size directly; it does not enforce a new 68-byte minimum.
[Output DF guard][output-df], [size cap and header subtraction][refragment].

The valid fragment-list fast path can preserve accepted fragment boundaries.
The copying slow path can regroup payload according to the capped MTU.
Both paths preserve payload order, but arbitrary ingress fragment boundaries do not uniquely determine output boundaries.
[Fragment-list validation and reuse][refragment], [copying fragmentation][copy].

DF output also depends on that internal path.
The fragment-list helpers assign offset and MF fields without retaining DF.
The copying path sets output DF from `IPSKB_FRAG_PMTU`.
A model must select a path or expose this distinction before claiming exact DF-fragment wire equality.
[Fragment-list header construction][fraglist], [copying DF construction][copy].

## Transport and unsupported cases

Reassembly does not validate UDP length or checksum.
UDP conntrack subsequently rejects lengths below eight or above available payload, while permitting shorter declared lengths than available payload.
Checksum zero bypasses UDP checksum validation.
With prerouting checksum validation enabled, an invalid nonzero checksum causes an invalid conntrack result.
[UDP validation][udp].

That invalid result detaches conntrack and returns `NF_ACCEPT`; it does not itself drop the packet.
Later firewall policy determines forwarding.
A strict UDP decoder can therefore reject input that Linux would forward without NAT under a permissive policy.
Treat that case as unsupported unless the model explicitly implements invalid-transport policy.
[Invalid result handling][ct-invalid], [UDP error return][udp].

Recommendation: distinguish buffered, completed, duplicate, native queue drop, malformed IP, and unsupported input.
IP options, reserved flag handling, bypass hooks, bridges, offload geometry, memory pressure, and positive disorder heuristics require separate selected semantics.
Unsupported means that the selected model makes no native acceptance claim.
It must not silently assert a Linux drop.
[Receive checks][input], [bypass cases][defrag], [insertion][queue], [resources][allocation], [output geometry][refragment].

## Native evidence and proof obligations

The following probes are recommendations derived from the inspected transitions.
Each capture should record kernel release, queue controls, routes, MTUs, zone assignments, hook priorities, and packet bytes.
[Relevant controls][sysctl], [hook priorities][priority], [queue behavior][queue].

| Probe | Required observation |
| --- | --- |
| In-order and out-of-order completion | Pre-defragmentation sees every fragment; priority -300 sees one complete packet. |
| A missing fragment | No later-hook packet and no conntrack or NAT mutation. |
| Duplicate with changed payload | Existing bytes survive; no extra completion or ECN contribution. |
| Contained interval spanning one run | Incoming interval is discarded as a duplicate. |
| Same interval spanning separate runs | Queue dies, despite identical aggregate byte coverage. |
| Partial overlap or conflicting final end | Queue dies; later same-key fragments can start another queue. |
| MF payload with trailing odd bytes | Native completion uses only the aligned prefix. |
| Empty normalized fragment | Existing queue dies. |
| Different fragment-zero TTL or DSCP | Completed packet takes those fields from fragment zero. |
| Mixed Not-ECT and ECT, or CE and ECT | First family fails; second completes with CE. |
| Deadline with an intermediate duplicate | Duplicate does not prolong queue survival. |
| Same key after expiry | New family can complete without old payload. |
| 600-byte ingress and 1500-byte egress | NAT follows completion; output remains fragmented below the retained cap. |

These observations follow the hook, insertion, metadata, expiry, and output branches described above.
[Hooks][defrag], [run classification][insert], [metadata][reasm], [expiry][expiry], [output][output].

Recommendation: retain a passive full-packet capture at priority -300 for completed bytes before conntrack and NAT.
An ingress packet-socket capture alone sees arriving fragments, while an egress capture sees translated, re-fragmented output.
The intermediate capture separates reassembly correctness from later forwarding correctness.
[Hook positions][priority], [defragmentation verdict][defrag], [output fragmentation][output].

Recommended durable proofs preserve key isolation, sorted nonoverlapping stored intervals, positive normalized lengths, and exact `meat` accounting.
Completion should imply coverage from zero through the declared final end.
Completed payload should equal the ordered accepted bytes, excluding duplicates and trimmed suffixes.
Buffered and rejected arrivals should leave conntrack, NAT mappings, and forwarding effects unchanged.
[Insertion and completion][queue], [ordered reconstruction][finish], [hook isolation][defrag].

Also prove first-header selection, ECN merging, maximum-size accumulation, fixed deadlines, queue removal, and certified output-family payload preservation.
These prove the selected state machine's properties.
They do not prove refinement of kernel C, authenticate packet captures, or establish universal Linux behavior.
[Header and metadata][reasm], [timer construction][allocation], [output paths][refragment].

[queue]: https://git.launchpad.net/~ubuntu-kernel/ubuntu/+source/linux/+git/noble/tree/net/ipv4/ip_fragment.c?h=Ubuntu-6.8.0-117.117#n279
[key]: https://git.launchpad.net/~ubuntu-kernel/ubuntu/+source/linux/+git/noble/tree/net/ipv4/ip_fragment.c?h=Ubuntu-6.8.0-117.117#n210
[domain]: https://git.launchpad.net/~ubuntu-kernel/ubuntu/+source/linux/+git/noble/tree/net/ipv4/ip_fragment.c?h=Ubuntu-6.8.0-117.117#n489
[length]: https://git.launchpad.net/~ubuntu-kernel/ubuntu/+source/linux/+git/noble/tree/net/ipv4/ip_fragment.c?h=Ubuntu-6.8.0-117.117#n304
[accepted]: https://git.launchpad.net/~ubuntu-kernel/ubuntu/+source/linux/+git/noble/tree/net/ipv4/ip_fragment.c?h=Ubuntu-6.8.0-117.117#n359
[reasm]: https://git.launchpad.net/~ubuntu-kernel/ubuntu/+source/linux/+git/noble/tree/net/ipv4/ip_fragment.c?h=Ubuntu-6.8.0-117.117#n417
[expiry]: https://git.launchpad.net/~ubuntu-kernel/ubuntu/+source/linux/+git/noble/tree/net/ipv4/ip_fragment.c?h=Ubuntu-6.8.0-117.117#n126
[distance]: https://git.launchpad.net/~ubuntu-kernel/ubuntu/+source/linux/+git/noble/tree/net/ipv4/ip_fragment.c?h=Ubuntu-6.8.0-117.117#n231
[peer]: https://git.launchpad.net/~ubuntu-kernel/ubuntu/+source/linux/+git/noble/tree/net/ipv4/ip_fragment.c?h=Ubuntu-6.8.0-117.117#n85
[defaults]: https://git.launchpad.net/~ubuntu-kernel/ubuntu/+source/linux/+git/noble/tree/net/ipv4/ip_fragment.c?h=Ubuntu-6.8.0-117.117#n670
[runs]: https://git.launchpad.net/~ubuntu-kernel/ubuntu/+source/linux/+git/noble/tree/net/ipv4/inet_fragment.c?h=Ubuntu-6.8.0-117.117#n29
[insert]: https://git.launchpad.net/~ubuntu-kernel/ubuntu/+source/linux/+git/noble/tree/net/ipv4/inet_fragment.c?h=Ubuntu-6.8.0-117.117#n386
[head]: https://git.launchpad.net/~ubuntu-kernel/ubuntu/+source/linux/+git/noble/tree/net/ipv4/inet_fragment.c?h=Ubuntu-6.8.0-117.117#n450
[finish]: https://git.launchpad.net/~ubuntu-kernel/ubuntu/+source/linux/+git/noble/tree/net/ipv4/inet_fragment.c?h=Ubuntu-6.8.0-117.117#n565
[ecn]: https://git.launchpad.net/~ubuntu-kernel/ubuntu/+source/linux/+git/noble/tree/net/ipv4/inet_fragment.c?h=Ubuntu-6.8.0-117.117#n88
[kill]: https://git.launchpad.net/~ubuntu-kernel/ubuntu/+source/linux/+git/noble/tree/net/ipv4/inet_fragment.c?h=Ubuntu-6.8.0-117.117#n231
[allocation]: https://git.launchpad.net/~ubuntu-kernel/ubuntu/+source/linux/+git/noble/tree/net/ipv4/inet_fragment.c?h=Ubuntu-6.8.0-117.117#n315
[defrag]: https://git.launchpad.net/~ubuntu-kernel/ubuntu/+source/linux/+git/noble/tree/net/ipv4/netfilter/nf_defrag_ipv4.c?h=Ubuntu-6.8.0-117.117#n62
[user]: https://git.launchpad.net/~ubuntu-kernel/ubuntu/+source/linux/+git/noble/tree/net/ipv4/netfilter/nf_defrag_ipv4.c?h=Ubuntu-6.8.0-117.117#n41
[zone]: https://git.launchpad.net/~ubuntu-kernel/ubuntu/+source/linux/+git/noble/tree/include/net/netfilter/nf_conntrack_zones.h?h=Ubuntu-6.8.0-117.117#n60
[priority]: https://git.launchpad.net/~ubuntu-kernel/ubuntu/+source/linux/+git/noble/tree/include/uapi/linux/netfilter_ipv4.h?h=Ubuntu-6.8.0-117.117#n30
[input]: https://git.launchpad.net/~ubuntu-kernel/ubuntu/+source/linux/+git/noble/tree/net/ipv4/ip_input.c?h=Ubuntu-6.8.0-117.117#n462
[forward]: https://git.launchpad.net/~ubuntu-kernel/ubuntu/+source/linux/+git/noble/tree/net/ipv4/ip_forward.c?h=Ubuntu-6.8.0-117.117#n84
[mtu]: https://git.launchpad.net/~ubuntu-kernel/ubuntu/+source/linux/+git/noble/tree/net/ipv4/ip_forward.c?h=Ubuntu-6.8.0-117.117#n42
[output]: https://git.launchpad.net/~ubuntu-kernel/ubuntu/+source/linux/+git/noble/tree/net/ipv4/ip_output.c?h=Ubuntu-6.8.0-117.117#n295
[output-df]: https://git.launchpad.net/~ubuntu-kernel/ubuntu/+source/linux/+git/noble/tree/net/ipv4/ip_output.c?h=Ubuntu-6.8.0-117.117#n582
[fraglist]: https://git.launchpad.net/~ubuntu-kernel/ubuntu/+source/linux/+git/noble/tree/net/ipv4/ip_output.c?h=Ubuntu-6.8.0-117.117#n604
[copy]: https://git.launchpad.net/~ubuntu-kernel/ubuntu/+source/linux/+git/noble/tree/net/ipv4/ip_output.c?h=Ubuntu-6.8.0-117.117#n650
[refragment]: https://git.launchpad.net/~ubuntu-kernel/ubuntu/+source/linux/+git/noble/tree/net/ipv4/ip_output.c?h=Ubuntu-6.8.0-117.117#n767
[time]: https://git.launchpad.net/~ubuntu-kernel/ubuntu/+source/linux/+git/noble/tree/include/net/ip.h?h=Ubuntu-6.8.0-117.117#n144
[sysctl]: https://git.launchpad.net/~ubuntu-kernel/ubuntu/+source/linux/+git/noble/tree/Documentation/networking/ip-sysctl.rst?h=Ubuntu-6.8.0-117.117#n242
[udp]: https://git.launchpad.net/~ubuntu-kernel/ubuntu/+source/linux/+git/noble/tree/net/netfilter/nf_conntrack_proto_udp.c?h=Ubuntu-6.8.0-117.117#n44
[ct-invalid]: https://git.launchpad.net/~ubuntu-kernel/ubuntu/+source/linux/+git/noble/tree/net/netfilter/nf_conntrack_core.c?h=Ubuntu-6.8.0-117.117#n2034
[nft-zone]: https://git.launchpad.net/~ubuntu-kernel/ubuntu/+source/linux/+git/noble/tree/net/netfilter/nft_ct.c?h=Ubuntu-6.8.0-117.117#n224
[orphan]: https://git.launchpad.net/~ubuntu-kernel/ubuntu/+source/linux/+git/noble/tree/include/linux/skbuff.h?h=Ubuntu-6.8.0-117.117#n3168
[icmp-glue]: https://git.launchpad.net/~ubuntu-kernel/ubuntu/+source/linux/+git/noble/tree/net/ipv4/icmp.c?h=Ubuntu-6.8.0-117.117#n355
[attach-wrapper]: https://git.launchpad.net/~ubuntu-kernel/ubuntu/+source/linux/+git/noble/tree/net/netfilter/core.c?h=Ubuntu-6.8.0-117.117#n700
[attach]: https://git.launchpad.net/~ubuntu-kernel/ubuntu/+source/linux/+git/noble/tree/net/netfilter/nf_conntrack_core.c?h=Ubuntu-6.8.0-117.117#n2146
[ct-in]: https://git.launchpad.net/~ubuntu-kernel/ubuntu/+source/linux/+git/noble/tree/net/netfilter/nf_conntrack_core.c?h=Ubuntu-6.8.0-117.117#n1968
[icmp-lookup]: https://git.launchpad.net/~ubuntu-kernel/ubuntu/+source/linux/+git/noble/tree/net/netfilter/nf_conntrack_proto_icmp.c?h=Ubuntu-6.8.0-117.117#n105
[template-zone]: https://git.launchpad.net/~ubuntu-kernel/ubuntu/+source/linux/+git/noble/tree/include/net/netfilter/nf_conntrack_zones.h?h=Ubuntu-6.8.0-117.117#n29
