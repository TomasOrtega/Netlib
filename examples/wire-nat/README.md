# NAT and TTL forwarding evidence

This fresh private capture combines EAP-TLS admission, generated forward policy, two-sided NAT, and complete IPv4/UDP wire bytes.
The three namespaces are `peer`, `auth`, and `server`.
All four veth interfaces have TX checksum and segmentation offloads disabled, with native readbacks.
The selected packets fit the retained 1500-byte interface MTUs.

The request and reply have four measured wire views:

| View | Source | Destination |
| --- | --- | --- |
| Peer request ingress | `192.0.2.2:41000` | `203.0.113.2:8080` |
| Server request egress | `203.0.113.1:40000` | `198.51.100.2:9000` |
| Server reply ingress | `198.51.100.2:9000` | `203.0.113.1:40000` |
| Peer reply egress | `203.0.113.2:8080` | `192.0.2.2:41000` |

The compiler's forward classes apply after destination translation.
They match the private peer and server endpoints, including the reverse reply.
Normal socket traffic is denied before authentication and after EAP without the local demo credential.
After credential installation and permit load, both sockets receive their distinct payloads.
Actual EAPOL Logoff followed by deny load blocks the same cached request.
The replied NAT row remains visible with the same ID.
[Socket observations](native/observations.json).
[Checked evidence](checked-evidence.json).

The permitted exchange includes a TTL-one reply before its normal reply.
The first request has already confirmed an unreplied NAT row.
The TTL-one reply changes that same row to seen-reply, while no selected UDP reply reaches the peer.
The gateway emits a separately retained ICMP Time Exceeded message.
Only then does the server send its ordinary reply.

After the four admission stages, a separate controlled phase deletes exactly the selected zone-zero conntrack key.
Raw snapshots record the existing row and the empty state after deletion.
The phase loads permit policy to test TTL behavior independently of session authorization.

| Raw probe | Selected UDP egress | Visible state after the probe |
| --- | --- | --- |
| TTL zero | Absent; ICMP Time Exceeded observed | Empty |
| TTL one | Absent; ICMP Time Exceeded observed | Empty |
| TTL two | Present with TTL one; server receives | New confirmed NAT row |
| Cached UDP checksum omitted | Present; server receives | Same new row |

The omission probe carries the legal IPv4 UDP zero-checksum marker.
NAT preserves that marker in the actual egress bytes.
All nonzero UDP checksums are validated with their IPv4 pseudoheaders.
Payload, identification, TOS, and DF are preserved through translation; TTL decreases by one on forwarded packets.
The verifier never repairs captured bytes.

The native hook trace includes before-DNAT, after-DNAT, before-SNAT, and after-SNAT checkpoints.
These provide actual five-tuple, TTL, length, and UDP checksum observations.
They are not fabricated intermediate Ethernet frames.
Trace IDs can repeat, so the verifier splits complete ingress episodes and joins their packet IDs and headers.
Raw bytes, payloads, native policy exports, command stdout, socket intervals, and Netlink snapshots are checked independently of Lean output.

The empty initial state is an actual raw Netlink dump before the first policy load and selected packet.
Classification and freshness observations remain unasserted when the native capture does not identify them directly.
ICMP is retained as an observed side effect, outside the UDP forwarding implementation model.
Its quoted packet ID, interface, and interval are checked without claiming a complete ICMP model.

Run the offline verifier and tests from the repository root:

```sh
UV_CACHE_DIR=/private/tmp/netlib-uv-cache uv run --locked python scripts/check_wire_nat_capture.py
UV_CACHE_DIR=/private/tmp/netlib-uv-cache uv run --locked python -m unittest discover -s scripts -p test_check_wire_nat_capture.py
```

The [builder](../../scripts/build_wire_nat_examples.py) projects independently checked observations into four session checkpoints and eleven wire replay events.
Input and output bytes, table snapshots, and hook observations come from the capture.
Lean report values do not create those observations.

```sh
UV_CACHE_DIR=/private/tmp/netlib-uv-cache uv run --locked python scripts/build_wire_nat_examples.py
lake exe netlib wire-forward examples/wire-nat/replay.json --json
lake exe netlib session-firewall examples/wire-nat/session.json --json
```

The [forwarding guide](../../docs/WIRE_FORWARDING.md) records the model, proof chain, schema, and remaining assumptions.
The [source note](../../docs/research/WIRE_NAT_FORWARDING.md) identifies exact native source paths and RFC requirements.

The [fresh recipe](recapture.sh) uses the pinned wire image and this directory's four immutable policy inputs.
It installs no packages and runs without an external network or host mounts.

```sh
export DOCKER_HOST=unix:///Users/to1717/.colima/default/docker.sock
export DOCKER_CONFIG=/private/tmp/netlib-docker-config
sh examples/wire-nat/recapture.sh /private/tmp/netlib-wire-nat-fresh
UV_CACHE_DIR=/private/tmp/netlib-uv-cache uv run --locked python scripts/check_wire_nat_capture.py \
  --capture-dir /private/tmp/netlib-wire-nat-fresh/native --input-dir examples/wire-nat
```

The runtime reuses earlier EAP and offload helpers inside the pinned image.
Earlier captures remain unchanged.
The demo credential is a declared local input, not a signed network credential.
Public certificates and sanitized logs are retained; private keys are deleted before export.

The results concern this finite, isolated software path.
They do not prove TLS cryptography, kernel refinement, capture authenticity, anti-spoofing, instantaneous policy updates, fragmentation, or all ICMP behavior.
