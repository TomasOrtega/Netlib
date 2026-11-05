# One campus session and gateway withdrawal

This experiment uses one controller history for authentication, installed policies, tracked NAT, delayed traffic, and planned gateway withdrawal.
Its pinned parent is the [safe handoff capture](../safe-handoff/README.md).
The earlier producers and saved observations remain unchanged.

## Shared session and forwarding history

The data topology contains `client`, primary gateway `a`, standby gateway `b`, and `server`.
The selected client socket is `192.0.2.2:41000`; its request targets `203.0.113.2:8080`.
Tracked NAT forwards to `198.51.100.2:9000` using public source `203.0.113.1:40000`.
Both directions retain the same confirmed binding across handoff.

A separate wired link joins `client/peer0` to `auth/auth0`.
Hostapd and wpa_supplicant perform EAP-TLS on that link.
The authenticated principal is `alice@campus.example.test`.
The [local demo credential](demo-credential.json) grants `campus-application/use`.
The [intent](requirements.json) binds that scope to the exact post-destination-NAT request and reply classes.
This binding is a reviewed controller input, without an anti-spoofing or signed-credential implementation proof.

Both gateways initially use generated deny policy.
Actual EAP success precedes credential installation and the generated permit installs.
The primary then establishes the selected flow, replicates it, and commits it into the standby.

An endpoint qdisc holds primary ticket zero while both endpoint routes move to the standby.
New standby request and reply traffic complete before the older primary ticket.
The primary processes that ticket before its drain barrier and data fence.

Withdrawal then stops the primary replication daemon, disables its synchronization link, and disables its IPv4 forwarding.
Readbacks retain all three disabled data/synchronization links, forwarding zero, and no remaining conntrackd process in that network namespace.
Subsequent boundaries contain no live primary tables, rulesets, or network exports.
Their explicit archive reference identifies the last live boundary before withdrawal.
The archived binding remains historical evidence.

Request and reply traffic continue through the standby after withdrawal.
Another queued request spans actual EAPOL Logoff and installation of generated deny on the standby.
It encounters that current deny after release.
A subsequent reply is also denied.

The selected execution contains 26 native operations and eight datagrams.
The bootstrap packet has no protected ticket.
Seven protected identities retire in order `1, 2, 0, 3, 4, 5, 6`.
Six datagrams reach their receiving sockets; two have measured receive timeouts.

## Retained evidence

Raw artifacts include complete command journals, EAPOL frames, sanitized authentication logs, public certificates, and the installed demo credential.
Private keys remain inside the runtime container and are deleted before export.
Endpoint NFLOG records early route assignment before controlled qdisc release.
Separate gateway frames, Netfilter logs, traces, socket receipts, and kernel dumps retain the selected processing outcomes.
Every admission must pass the complete IPv4 UDP codec; no checksum bytes are repaired.

Queue observations retain actual lengths, backlog, counters, delays, and drop counts.
A zero backlog alone does not establish drain.
The barrier also requires the selected ticket's actual processing and socket outcome.

A prewithdrawal standby log receipt separates earlier synchronization from the expected channel-removal error after primary withdrawal.
This evidence does not establish reliable synchronization after the channel is disabled.

## Reproduce

Build the pinned [safe handoff parent](../safe-handoff/README.md), configure Docker, then run:

```sh
examples/campus/recapture.sh /tmp/netlib-campus-recapture
```

The recipe builds offline from the existing parent and runs without external networking or host mounts.
The inherited runtime directory remains `/tmp/netlib-safe-handoff`; the recipe exports it into the new capture's `native` directory.
Fresh runs have their own certificates, packet identifiers, queue seeds, times, and hashes.

This is wired EAP evidence for the selected ordinary UDP flow and planned withdrawal sequence.
Wireless key installation, unexpected crashes with pending traffic, automatic convergence, expiry, physical timing bounds, and complete campus correspondence remain open.
Cryptography, authentic collection, principal-to-header ownership, and implementation refinement retain their explicit assumptions.
