# Received ICMP and host PMTU

This fresh Linux `6.8.0-117-generic` capture uses four private namespaces:
peer → EAP/NAT gateway → downstream router → server. The peer link has
MTU 4096, the gateway/router link 1500, and the router/server link 600.
The gateway route to `198.51.100.0/24` explicitly uses `198.51.101.254`.
The original UDP tuple remains `192.0.2.2:41000 → 203.0.113.2:8080`;
the translated wire tuple is `203.0.113.1:40000 → 198.51.100.2:9000`.

The first four stages retain the EAP and credential admission contract.
Authentication alone does not permit UDP. Installing the declared credential
loads the compiled permit policy; EAPOL Logoff loads deny while retaining
the cached NAT flow. A 1200-byte request fragments at the downstream router,
and the server reassembles it and returns an ordinary UDP reply.

A separate probe phase reloads the same UDP permission and prepends an
explicit ICMP `ct state related accept` rule in the same forward base chain.
This fixed control permission makes no additional EAP authorization claim.
The complete rulesets retain deny-by-default forward and local-input filters.
The targeted old UDP association is erased before the PMTU experiment.

The peer then connects a real UDP socket with `IP_PMTUDISC_DO` and
`IP_RECVERR`. Its initial `IP_MTU` is 4096. A 1200-byte send reaches the
downstream router after NAT; that router generates ICMP type 3/code 4 with
MTU 600 and quotes the exact SNAT wire prefix. The gateway **receives** the
error on `service0`, associates it with the confirmed flow as RELATED,
reverses both quoted NAT mappings, and forwards it to the peer. The native
error queue reports network origin, `EMSGSIZE`, type/code 3/4, and MTU 600.
The socket reads `IP_MTU = 600`. Its next 1200-byte send returns `EMSGSIZE`
with local origin and emits no packet. After draining that error, a 500-byte
send and ordinary server reply succeed. The ICMP error leaves the cached
UDP seen-reply bit clear; the ordinary UDP reply sets it.

Six further probes are explicitly labeled **raw synthetic senders**. Their
constructed bytes, source commands, stdout, and unchanged native observations
are retained. An unmatched quoted port and a wrong outer destination fail
association and reach the drop-policy input chain. A related error with
outer TTL one is discarded without generating another error. A complete
quote with an invalid UDP checksum and a quote with an invalid IPv4 checksum
still associate and reach the host; incremental NAT preserves each invalid
checksum residue. A forged outer source `198.51.100.99` also associates and
lowers the host PMTU to 576. RELATED establishes tuple association, not
source authentication or quoted-checksum validity.

Native `min_pmtu = 552` and `mtu_expires = 600` readbacks precede the probes.
Per-probe route-get stdout independently shows the PMTU exception at 600,
its remaining lifetime counting down, and the forged decrease to 576 with
renewed lifetime. This run does not wait for physical cache expiry or test
the minimum-PMTU locking branch.

The independent checker consumes all 60 IPv4 frame reads from both ends of
all three veth links, all 15 gateway ingress trace episodes, every UDP
fragment family, and every assigned post-step raw Netlink snapshot. It
checks outer IPv4/ICMP checksums, whole UDP checksums at every hook,
complete quoted UDP checksum status, exact incremental quote translation,
RELATED/INVALID counters, exclusive hooks and policy, per-send MTUs,
offload readbacks, socket errno/ancillary bytes, and read-time fences.
Repeated trace identifiers and IPv4 IDs are not treated as global identity.
Every native producer source hash is checked against its retained source.
Mutation tests operate only on temporary synthetic copies.

```sh
UV_CACHE_DIR=/private/tmp/netlib-uv-cache uv run --locked python scripts/check_received_icmp_capture.py
UV_CACHE_DIR=/private/tmp/netlib-uv-cache uv run --locked python -m unittest discover -s scripts -p test_check_received_icmp_capture.py
```

Run `sh examples/received-icmp/recapture.sh /tmp/netlib-received-recapture`
with the pinned `netlib-icmp-capture:1` parent image. The recipe uses no
network or host mounts. The retained run used `docker run` directly;
[capture-invocation.json](capture-invocation.json) records its actual command,
image, and timestamps. Captured observations assume the retained configuration
was active; they do not prove capture authenticity, kernel refinement,
internal kernel timing, TLS cryptography, general ICMP handling, or arbitrary
IPv4 options and fragmentation of received ICMP errors.
