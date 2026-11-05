# Session admission at a wired gateway

This experiment combines actual EAP-TLS authentication, generated nftables policy, and measured UDP traffic.
The private Linux namespaces are `peer`, `auth`, and `server`.
The selected request is `192.0.2.2:41000` to `198.51.100.2:9000`, with its reverse reply.
There is no NAT.

The four measured stages are:

| Stage | Generated policy | Native result |
| --- | --- | --- |
| Before authentication | Deny | Server and client time out |
| After EAP-TLS, before the demo credential | Deny | Server and client time out |
| After local demo credential installation | Permit request and reply | Both sockets receive their distinct payloads |
| After actual EAPOL Logoff | Deny | The same cached UDP flow is blocked |

The credential file remains installed after Logoff.
The same confirmed, replied conntrack row remains visible with its original ID.
The forward chain still denies the final request.
It has no conntrack established-flow bypass.
[Measured observations](native/observations.json).
[Independent checked evidence](checked-evidence.json).

The capture retains seven raw IPv4 Ethernet frames and eighteen raw EAPOL frames.
It also retains public certificates, sanitized producer logs, socket intervals, active policy exports, complete rulesets, and raw Netlink conntrack dumps.
Every native policy export is joined to its exact producer stdout and measurement interval.
The verifier checks MAC roles, packet lengths, payloads, forwarding TTL changes, policy classes, cached-flow identity, and authentication checkpoints.

The controller loads the immutable [deny](deny.json) and [permit](permit.json) policies.
Each replacement uses one nftables JSON transaction that deletes and recreates the selected table.
A separate prerouting chain only counts tracked new and established packets.
It enables the conntrack observation and contains no forwarding verdict.
The full ruleset must contain exactly this counter chain and the generated forward table.

The [demo credential](demo-credential.json) is a declared local controller input.
It is not a signed network credential or part of the UDP payload.
Hostapd and wpa_supplicant perform the actual TLS 1.3 exchange.
The capture reuses the [existing EAP helper](../eap/exercise.py) without changing its earlier evidence.
Private keys stay inside the runtime container and are deleted before export.
Derived-key debug lines are redacted before writing.

Run the independent verifier and tests from the repository root:

```sh
UV_CACHE_DIR=/private/tmp/netlib-uv-cache uv run --locked python scripts/check_admission_capture.py
UV_CACHE_DIR=/private/tmp/netlib-uv-cache uv run --locked python -m unittest discover -s scripts -p test_check_admission_capture.py
```

The [projection builder](../../scripts/build_admission_examples.py) reads independently checked capture evidence.
It supplies the declared local round 2 from Begin and the single Start.
The four native stages map to consumed event counts 1, 18, 19, and 21.
The demo credential is installed once, after method evidence and before Logoff.
This projection reads no Lean report values to create its observations.

```sh
UV_CACHE_DIR=/private/tmp/netlib-uv-cache uv run --locked python scripts/build_admission_examples.py
lake exe netlib session-firewall examples/admission/bundle.json --json
lake exe netlib compile-session examples/admission/authentication.json examples/admission/requirements.json --after 19
```

The final command reconstructs the retained permit policy through the certified session compiler.
The default final-state compilation reconstructs the deny policy.
The [session firewall guide](../../docs/SESSION_FIREWALL.md) defines the proofs, schemas, and assumptions.

The [fresh recipe](recapture.sh) uses the pinned EAP capture image.
It adds no packages and runs without an external network or host mounts.
Configure Docker and choose a separate output directory:

```sh
export DOCKER_HOST=unix:///Users/to1717/.colima/default/docker.sock
export DOCKER_CONFIG=/private/tmp/netlib-docker-config
sh examples/admission/recapture.sh /private/tmp/netlib-admission-fresh
UV_CACHE_DIR=/private/tmp/netlib-uv-cache uv run --locked python scripts/check_admission_capture.py \
  --capture-dir /private/tmp/netlib-admission-fresh/native
```

The retained run used the same image inputs through explicit Docker build and run commands.
Its [invocation record](capture-invocation.json) identifies those commands and the later cached rebuild used to retain build output.
Fresh runs change certificate fingerprints, packet IDs, timestamps, and conntrack IDs.

This is finite evidence for ordinary transit traffic through this gateway.
The verifier does not verify TLS cryptography offline or authenticate the capture itself.
Certificate validation, current-round attribution, header identity, and authentic collection remain assumptions.
The demo gives no anti-spoofing, global instantaneous update, or kernel refinement proof.
