# IPv4 and UDP wire evidence

This is a fresh capture with complete UDP checksums in the retained bytes.
The seven normal datagrams come from ordinary UDP sockets.
The private gateway repeats the four admission stages: unauthenticated deny, authentication-only deny, credential permit, and Logoff deny.
The same cached flow remains visible after Logoff.

Before traffic, the wrapper disables TX checksum, TSO, GSO, and GRO on all four veth interfaces.
It uses Linux `SIOCETHTOOL` controls and retains each getter, setter, and readback result.
Every final readback is zero.
The verifier also computes the checksums from the raw bytes independently.
No captured checksum field is repaired or replaced after collection.
[Offload observations](native/offloads.json).
[Normal socket frames](native/data-frames.jsonl).
[Checked evidence](checked-evidence.json).

The older raw admission capture remains unchanged.
Its AF_PACKET records contain partial UDP checksum values and need their stated transport-validity assumption.
Those bytes fail this example's nonzero wire checksum check.
They are retained as a regression counterexample, not presented as valid wire datagrams.

After the admission episode finishes, a separate test loads the same permit policy and injects five raw Ethernet probes.
These probes test endpoint parsing rather than session authorization.

| Injected probe | Gateway service egress | UDP socket result |
| --- | --- | --- |
| Valid nonzero UDP checksum | Present | Payload received |
| Zero UDP checksum, explicitly omitted | Present | Payload received |
| Incorrect nonzero UDP checksum | Present | Timeout |
| UDP declared length seven | Present | Timeout |
| Incorrect IPv4 header checksum | Absent | Timeout |

The raw sender constructs each probe before collection and retains its exact bytes and send result.
The normal receiving UDP socket supplies an independent outcome.
The verifier joins the sender, gateway ingress, gateway egress, active policy exports, and socket intervals.
Invalid UDP can therefore reach gateway egress while failing at the final socket.
The length-seven probe has a malformed UDP length; no valid UDP checksum interpretation is claimed for that datagram.
[Probe observations](native/probe-observations.json).
[Probe frames](native/probe-frames.jsonl).

The byte checker supports Ethernet IPv4 with IHL five, no fragmentation, protocol UDP, and exact UDP payload length.
It checks the IPv4 checksum and the UDP pseudoheader, including source and destination addresses.
Zero means checksum omission for IPv4 UDP and is reported separately.
Ethernet padding lies outside the IPv4 total length.
The native positive profile requires a complete nonzero UDP checksum.

Run the offline checks from the repository root:

```sh
UV_CACHE_DIR=/private/tmp/netlib-uv-cache uv run --locked python scripts/check_wire_capture.py
UV_CACHE_DIR=/private/tmp/netlib-uv-cache uv run --locked python -m unittest discover -s scripts -p test_check_wire_capture.py
```

The [builder](../../scripts/build_wire_examples.py) reuses the shared admission projection for its four session checkpoints.
It derives the wire fixture directly from the independently checked normal capture.
The generated artifacts read no Lean report values to create their observations.

```sh
UV_CACHE_DIR=/private/tmp/netlib-uv-cache uv run --locked python scripts/build_wire_examples.py
lake exe netlib wire examples/wire/frame.json --json
lake exe netlib session-firewall examples/wire/bundle.json --json
```

The [wire guide](../../docs/WIRE.md) defines the byte profile and proof chain.
The [source note](../../docs/research/IPV4_UDP_WIRE.md) records exact RFC and native kernel references.

The [fresh recipe](recapture.sh) uses the pinned admission image and this directory's immutable policy inputs.
It installs no packages and runs without an external network or host mounts.
Configure Docker, then choose a new output directory:

```sh
export DOCKER_HOST=unix:///Users/to1717/.colima/default/docker.sock
export DOCKER_CONFIG=/private/tmp/netlib-docker-config
sh examples/wire/recapture.sh /private/tmp/netlib-wire-fresh
UV_CACHE_DIR=/private/tmp/netlib-uv-cache uv run --locked python scripts/check_wire_capture.py \
  --capture-dir /private/tmp/netlib-wire-fresh/native --input-dir examples/wire
```

The wrapper reuses the existing admission and EAP producers inside the pinned image.
Their original captured artifacts are unchanged.
Public certificates and sanitized logs are retained; private keys are deleted before export.
Fresh runs change TLS randomness, timestamps, packet IDs, and cached-flow IDs.

This is finite evidence for the selected datagrams and private gateway path.
The userspace capture timestamps can differ from packet processing order across interfaces.
The verifier does not prove TLS cryptography, capture authenticity, all kernel behavior, anti-spoofing, or global instantaneous policy updates.
