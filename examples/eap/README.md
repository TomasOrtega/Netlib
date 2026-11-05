# Wired EAP-TLS capture

This example connects actual hostapd and wpa_supplicant processes through a private Linux veth link.
Both programs are built from the official 2.12 source archives.
OpenSSL 3.5.9 runs mutual certificate authentication with TLS 1.3.
There is no wireless device, host network, host mount, or external runtime network.

The first exchange succeeds and then sends EAPOL Logoff.
The second exchange rejects the server certificate because its DNS name does not match the configured name.
The capture records 32 Ethernet EAPOL frames, including TLS fragments, Success, Failure, and Logoff.
[Checked evidence](checked-evidence.json).
[Raw frame capture](native/success-frames.jsonl).
[Rejected server capture](native/bad-server-frames.jsonl).

The public outer identity is `anonymous@campus.example.test`.
The accepted client certificate identifies `alice@campus.example.test`.
The verifier keeps those identities distinct.
It requires TLS method completion from both producer logs before reporting successful authentication.
A raw EAP-Success packet alone is insufficient.
[Research and source references](../../docs/research/EAP_AUTHENTICATION.md).

## Retained evidence

- Raw Ethernet bytes and monotonic receive times from one AF_PACKET socket on `auth/auth0`.
- Independent supplicant RX/TX EAPOL byte dumps, compared with every captured payload.
- Timestamped native logs, public certificates, CRL, OCSP response, and certificate fingerprints.
- Exact configurations, producer commands, package versions, source hashes, and binary hashes.
- Logical station authorization before Logoff and its removal after Logoff.

No private keys are exported.
The collector redacts derived-key log lines before writing them.
Other producer output is retained, including OpenSSL's own removed-key markers.
The Ethernet frame bytes are unchanged.
The timestamp on a producer line records when the collector reads it.
It does not measure the producer's internal decision instant.

`phaseId` identifies an isolated pair of producer processes and its capture interval.
It is not an EAP field or the formal model's round number.
The admission adapter derives its local round from begin and reset events.
Mapping the method decision to that round requires the stated collector and link attribution assumption.

## Offline checks

Run these commands from the repository root:

```sh
UV_CACHE_DIR=/private/tmp/netlib-uv-cache uv run --locked python scripts/check_eap_capture.py
UV_CACHE_DIR=/private/tmp/netlib-uv-cache uv run --locked python -m unittest discover -s scripts -p test_check_eap_capture.py
```

The verifier reads native evidence independently of Lean output.
It checks link roles, padding boundaries, declared lengths, request correlation, method sequencing, TLS fragment totals, and native results.
It also checks that native EAPOL byte dumps agree with all raw frame payloads.
Contradiction tests reject missing method results, wrong identifiers, stale windows, wrong MACs, malformed lengths, duplicate events, and certificate-policy failures.

## Fresh capture

The recipe requires Docker with the retained parent image and permission to create private Linux network namespaces.
Its build downloads the pinned producer sources and installs the exact OpenSSL packages.
Its runtime has no external network.
The parent image ID is checked before the build.

Configure the Docker endpoint, then run the recipe:

```sh
export DOCKER_HOST=unix:///Users/to1717/.colima/default/docker.sock
export DOCKER_CONFIG=/private/tmp/netlib-docker-config
sh examples/eap/recapture.sh /private/tmp/netlib-eap-fresh
UV_CACHE_DIR=/private/tmp/netlib-uv-cache uv run --locked python scripts/check_eap_capture.py \
  --capture-dir /private/tmp/netlib-eap-fresh/native --output /private/tmp/netlib-eap-fresh/checked-evidence.json
```

The recipe generates new certificates and keys for each run.
Keys stay in the container's temporary runtime directory and are deleted before export.
Certificate fingerprints, TLS randomness, timestamps, and later request identifiers can change.
The results reproduce the experiment, not its exact bytes.
[Container recipe](Dockerfile).
[Runtime recipe](capture.sh).
[Producer and socket capture](exercise.py).
[Retained provenance](capture-provenance.json).

## Scope

The verifier checks a finite, retained exchange.
It does not reimplement TLS or verify signatures and encrypted handshake contents offline.
Correct certificate validation, TLS processing, current-round attribution, and authentic collection remain assumptions.
The test does not claim a CNSA-approved cipher suite.

The wired driver exposes EAPOL transport without a station-authorization driver callback.
Hostapd's authorized flag is therefore a logical observation.
No application payload or physical port barrier is measured here.
The capture proves neither data-port enforcement nor a universal replay or liveness property.
