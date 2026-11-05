# IPv4 ingress reassembly

This fresh Linux `6.8.0-117-generic` run uses three private namespaces:
peer → EAP/NAT gateway → server. The peer/gateway link has MTU 600;
the gateway/server link has MTU 1500. The original UDP tuple is
`192.0.2.2:41000 → 203.0.113.2:8080`; the translated wire tuple is
`203.0.113.1:40000 → 198.51.100.2:9000`.

The four admission checkpoints retain the EAP and credential contract.
Authentication alone denies UDP. Installing the declared credential loads
the compiled permit policy; Logoff loads deny while keeping the cached flow.
The native EAP handshake temporarily uses MTU 1500, with actual write and
readback records. Both peer interfaces return to 600 before IPv4 probes.

The ordinary UDP socket fragments a 1200-byte payload before the gateway.
Only completion reaches conntrack and NAT. Linux preserves the ingress
fragment-size budget, producing IP lengths 596, 596 and 76 even though the
egress MTU is 1500. An ordinary reply returns through the cached mapping.
Separate fixed-policy probes make no additional EAP authorization claim.
One queue starts under permit and completes after Logoff under deny; another
starts under deny and completes after the fixed permit policy is loaded.

Raw synthetic sender commands retain their constructed on-wire bytes and
stdout. They exercise reversed and interleaved families, changed-byte
duplicates, contained ranges, overlapping ranges, conflicting final lengths,
odd MF payload trimming, zero normalized payload, ECN combinations and
largest-DF-fragment metadata. Zones 10 and 20 isolate identical tuple/ID
queues. `ipfrag_max_dist = 0` excludes Linux's distance heuristic; successful
allocation is an explicit selected-profile premise.

Two measured waits expire incomplete queues after a retained one-second
`ipfrag_time` write/readback. SNMP reports one timeout/failure per wait and
the fragment queue count falls. The locally assigned destination VIP makes
each expired queue eligible for ICMP type 11/code 1. The error preserves
the stored first-fragment header and normalized payload prefix. Its outer
source is the VIP, TTL 64, TOS 192 and total length 576. Passive OUTPUT
counters distinguish inherited zone 0 and zone 10 templates. Both errors
classify INVALID, leave conntrack unchanged and pass the exact type/code
control permission. No OUTPUT rule rewrites the zone.

Passive NFLOG copies at prerouting priority -450 provide authoritative
arrival IPv4 bytes; priority -300 copies expose actual completed packets
before conntrack. All 107 raw Netlink messages and their configuration ACKs
are retained. The checker joins 79 arrivals, 22 completions and both errors
to native command, socket, trace, counter and snapshot boundaries. Its 82
ordered events include two waits and one administrative erase. Only 73
actual terminal episode dumps are observed; nine socket-burst prefixes have
no invented intermediate conntrack snapshot.

All 266 AF_PACKET reads remain unchanged. Twenty-one delayed ingress reads
show shared-buffer mutation into a later Ethernet egress packet. Each is
bound to the exact whole egress bytes from the same episode. They never
supply reconstructed input bytes. All output families use actual egress
Ethernet frames and preserve capture order; their coverage contract accepts
permutations and does not assume a unique Linux skb fragmentation layout.

The checker validates complete exclusive rulesets, typed timeout guards,
every traced rule handle/action, checksum and metadata joins, per-send link
readbacks, offload state, raw Netlink conntrack dumps, socket payload/order,
SNMP deltas, queue memory/counts and every controller command since the
baseline settings readback. Native observation times use monotonic nanoseconds;
timeouts scale seconds by 1,000,000,000. These are userspace read fences,
not exact internal kernel execution or jiffy times.

```sh
UV_CACHE_DIR=/private/tmp/netlib-uv-cache uv run --locked python scripts/check_reassembly_capture.py
UV_CACHE_DIR=/private/tmp/netlib-uv-cache uv run --locked python -m unittest discover -s scripts -p test_check_reassembly_capture.py
```

Run `sh examples/reassembly/recapture.sh /tmp/netlib-reassembly-recapture`
with the pinned `netlib-received-icmp-capture:1` parent image. The recipe
uses no network or host mounts. The retained run used `docker run` directly;
`capture-invocation.json` records its actual command, image and timestamps.
Producer, artifact and verifier hashes are in `capture-provenance.json`.
Mutation tests use temporary copies only. This selected evidence does not
prove capture authenticity, Linux C refinement, TLS cryptography, memory
pressure behavior, options, arbitrary protocols or arbitrary routing scopes.
