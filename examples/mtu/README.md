# Native IPv4 MTU and fragmentation

This capture uses private peer, gateway, and server namespaces on
Linux `6.8.0-117-generic`. Peer-facing veths have MTU 4096; the server
link has MTU 600. TX checksums, TSO, GSO, and GRO are disabled with
retained readbacks. Captured Ethernet bytes are unchanged.

The ordinary UDP sender records `IP_PMTUDISC_DONT` and sends a
1200-byte payload in one unfragmented IPv4 packet. DNAT maps
`203.0.113.2:8080` to `198.51.100.2:9000`; SNAT maps the source to
`203.0.113.1:40000`. The permitted request produces three IPv4
fragments with lengths 596/596/76 and byte offsets 0/576/1152.
The server's ordinary UDP socket receives the complete 1200-byte
payload. Its small reply traverses reverse NAT.

The four admission checkpoints deny before authentication, deny
after real EAP-TLS success without the declared application
credential, permit after local credential installation, and deny
the same cached flow after captured EAPOL Logoff. A TTL-one reply
before the normal reply changes the raw conntrack seen-reply status
while no selected UDP reply exits. The post-Logoff drop preserves
that replied binding. The credential is supplied local demo input;
its integrity field is not a verified network signature.

A separate permit phase measures six boundary cases:

| Case | Native result |
| --- | --- |
| Cached oversized DF packet | ICMP 3/4, MTU 600; same replied entry |
| Fresh oversized DF packet | ICMP 3/4, MTU 600; no confirmed entry |
| TTL 1 plus oversized DF | ICMP 11/0; no confirmed entry |
| Exact 600-byte packet with DF | One forwarded packet |
| Oversized packet with DF clear | Three forwarded fragments |
| Omitted UDP checksum | Three fragments; checksum remains zero |

A targeted zone-zero conntrack deletion separates the cached and
fresh probes. The initial and post-step states are raw Netlink
dumps. Complete rulesets, NAT and filter exports, per-event link
MTUs, routes, command stdout, producer versions, public certificates,
and EAP logs are retained under [native](native/).

The independent Python checker validates each IPv4 header, joins
unordered fragments with exact contiguous coverage and common
metadata, then checks UDP length and its complete pseudoheader
checksum. It compares reassembled payloads with the native socket
results. Reassembled metadata is marked as derived; the replay's
output arrays contain only original captured Ethernet frames.
Native hook traces describe the whole packet before fragmentation.
ICMP errors have valid checksums, the expected type/code and MTU,
and an exact quoted prefix of the corresponding ingress packet.

Capture timestamps come from userspace reads. The checker requires
selected frames and errors to be measured before their post-step
snapshot. These fences do not prove internal kernel timing. The
finite experiment assumes the retained namespace, hook, routing,
and authentication observations describe the active configuration.
It does not prove Linux C refinement, TLS cryptography, capture
authenticity, gateway input reassembly, full ICMP behavior,
anti-spoofing, or instantaneous policy updates.

Run `sh examples/mtu/recapture.sh /tmp/netlib-mtu-recapture` with a
Docker context that contains the pinned parent image and permits
private namespace setup. The recipe has no network or host mounts.
The retained run used Docker run directly; [capture-invocation.json](capture-invocation.json)
records that invocation. The packaged recipe uses create/start with
the same image inputs and runtime options. Build/runtime logs and
container metadata describe the actual retained run. The inherited
EAP producer removes private keys and redacts derived-key debug
lines before export. No captured packet bytes are rewritten.

From the repository, run:

```sh
UV_CACHE_DIR=/private/tmp/netlib-uv-cache uv run --locked python scripts/check_mtu_capture.py
UV_CACHE_DIR=/private/tmp/netlib-uv-cache uv run --locked python -m unittest discover -s scripts -p test_check_mtu_capture.py
```

The formal model and its explicit limits are documented in
[MTU forwarding](../../docs/MTU.md) and the
[primary-source note](../../docs/research/MTU_FRAGMENTATION.md).
