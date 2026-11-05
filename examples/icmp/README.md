# Native generated ICMP errors

This fresh Linux `6.8.0-117-generic` experiment extends the pinned
MTU image in private peer, gateway, and server namespaces. The peer
link has MTU 4096 and the server link MTU 600. It retains the four
EAP and credential checkpoints, ordinary 1200-byte UDP socket send,
three request fragments, reverse NAT reply, targeted conntrack
erasure, and six MTU probes from the parent experiment.

Eight further TTL-one probes cover original and reply directions,
nonzero TOS including ECN bits, odd and even lengths, complete and
truncated quotes, and a quoted omitted UDP checksum. Their input
IPv4 lengths are 63, 64, 547, 548, 549, 576, 577, and 575 bytes.
The retained run contains 20 selected packet episodes, 31 UDP
Ethernet frames, and 12 generated ICMP errors.

The measured no-options quote limit is 548 bytes: the lesser of
the original IPv4 length and `min(return MTU, 576) - 28`. Thus a
548-byte input is quoted completely, while a 549-byte input is
truncated. Every quote equals the entire corresponding original
ingress prefix, including the original pre-DNAT IPv4 and UDP
headers and the unchanged UDP checksum field. A partial UDP quote
is marked partial even when its truncated checksum sum happens
to equal the checksum acceptance value. UDP checksum validation
requires the complete datagram; zero denotes omission.

The outer TOS is `(ingress TOS & 0x1e) | 0xc0`, TTL is the measured
`ip_default_ttl` of 64, and DF is clear. The return route initially
selects the gateway interface address. The attached RELATED
conntrack state admits the error at the dedicated LOCAL_OUT filter;
POSTROUTING NAT changes its source to the original ingress
destination, either the service VIP or public SNAT address. The
outer destination is the original ingress source. The outer IPv4
ID is retained as a raw-derived allocation choice, without a claim
that the model determines Linux's ID allocator.

The dedicated output hook has priority 0, a drop policy, and a
rule accepting ICMP with conntrack state RELATED. A separate
POSTROUTING filter at priority 200 accepts generated output.
Complete rulesets, their exact command stdout, RELATED counters,
LOCAL_OUT and POSTROUTING traces, raw Netlink snapshots, per-send
MTUs, offload readbacks, socket results, sysctl write/readback
commands, public certificates, and redacted EAP producer logs are
retained under [native](native/). The selected ICMP rate-limit
settings and `icmp_errors_use_inbound_ifaddr` are explicitly zero.
All selected input, output, and ICMP userspace read timestamps must
precede their post-step state snapshot.

The independent Python checker validates outer IPv4 and ICMP
checksums, ICMP type/code and reserved words, the next-hop MTU,
quoted IPv4 checksums and tuples, complete quoted UDP checksums,
the exact entire quote prefix and truncation boundary, outer
metadata, NAT changes, output admission, and cached state effects.
Every whole UDP hook checksum is recomputed from the complete
ingress payload and that hook's tuple. Dedicated late-hook visits
remain checked, and each ICMP output trace belongs to exactly one
preceding ingress episode even when outer IPv4 IDs repeat.
The checksum-valid mutation cases in its tests are synthetic and
never rewrite retained packet bytes.

Run `sh examples/icmp/recapture.sh /tmp/netlib-icmp-recapture` with
a Docker context containing the pinned parent image. The recipe
uses no network or host mounts. The retained run used Docker run
directly; [capture-invocation.json](capture-invocation.json) records
the actual command, image, and timestamps. The packaged recipe uses
create/start with the same source inputs and runtime options.

```sh
UV_CACHE_DIR=/private/tmp/netlib-uv-cache uv run --locked python scripts/check_icmp_capture.py
UV_CACHE_DIR=/private/tmp/netlib-uv-cache uv run --locked python -m unittest discover -s scripts -p test_check_icmp_capture.py
```

This finite profile covers generated Time Exceeded and Fragmentation
Needed errors for unicast, unfragmented IPv4/UDP gateway inputs.
It does not cover gateway ICMP error input, general ICMP, options,
rate-limit suppression, or gateway input reassembly. The evidence
assumes the retained configuration observations describe the active
experiment; it does not prove capture authenticity, Linux C
refinement, TLS cryptography, or internal kernel timing.
