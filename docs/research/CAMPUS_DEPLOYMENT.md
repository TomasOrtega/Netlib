# Coordinated wired session and gateway withdrawal

This milestone joins one wired EAP-TLS session with generated gateway policies, conntrack replication, queued traffic, and planned primary withdrawal.
The UDP client also runs the EAP peer in the same network namespace.
The selected run uses whole IPv4 UDP datagrams, fixed NAT, zone zero, and explicit route changes.
[Capture producer](../../examples/campus/exercise.py).
[Selected native manifest](../../examples/campus/native/capture.json).

This remains a finite joint trace, not the full campus deployment landmark.
It establishes neither Wi-Fi behavior, cryptographic model completeness, physical switch enforcement, nor general Linux kernel refinement.
Earlier notes retain the detailed [EAP](EAP_AUTHENTICATION.md), [replication](NATIVE_STATEFUL_FAILOVER.md), and [queue handoff](SAFE_GATEWAY_HANDOFF.md) boundaries.

## Authentication and configured ownership

RFC 9190 forbids authorization from the unauthenticated outer EAP identity.
It permits policy decisions combining authenticated EAP information with information from encapsulating protocols.
[RFC 9190, sections 2.2 and 5.6](https://www.rfc-editor.org/rfc/rfc9190.html#section-2.2).

The run configures the outer identity as `anonymous@campus.example.test` and checks the client certificate subject against `alice@campus.example.test`.
Its authenticator and supplicant select TLS 1.3 and private test certificates.
The authorized station export records `[AUTHORIZED]` before the local credential installation.
[Authenticator configuration](../../examples/campus/native/eap/hostapd.conf).
[Peer configuration](../../examples/campus/native/eap/success-supplicant.conf).
[Authorized station](../../examples/campus/native/eap/authorized-station.txt).

The credential is a local JSON fixture with an `integrity` Boolean and modeled expiry.
Copying it into the demo runtime does not validate a signature or issue a cryptographic bearer token.
Its subject and the selected UDP headers have an explicit configured association.
Namespace placement and matching strings do not prove cryptographic ownership of each UDP datagram.
[Installed credential](../../examples/campus/native/installed-demo-credential.json).
[Policy requirements](../../examples/campus/native/input/requirements.json).
[Installation operation](../../examples/campus/exercise.py).

Hostapd 2.12's wired driver exchanges EAPOL but supplies no station authorization callback.
Its logical station flag therefore does not establish a physical controlled data-port barrier.
This inference follows `src/drivers/driver_wired.c` and `src/ap/ieee802_1x.c` in the official release.
[Official hostapd 2.12 source](https://w1.fi/releases/hostapd-2.12.tar.gz).

The authentication link uses `peer0` and `auth0`; UDP traffic uses separate client links `cal` and `cbl`.
The installed gateway policies enforce this demo's data admission.
[Authentication network and endpoint bindings](../../examples/campus/native/capture.json).

## Policy location and NAT classes

Forwarded packets traverse prerouting, forward, and postrouting.
The documented priorities place destination NAT before forward filtering and source NAT afterward.
[Netfilter hook ordering](https://wiki.nftables.org/wiki-nftables/index.php/Netfilter_hooks).

The generated permit policy matches these headers at the forward hook:

| Class | Source | Destination |
| --- | --- | --- |
| REQUEST | `192.0.2.2:41000` | `198.51.100.2:9000` |
| REPLY | `198.51.100.2:9000` | `192.0.2.2:41000` |

These classes use headers after destination translation and before source translation.
They differ from the endpoint service address `203.0.113.2:8080` and the translated client address `203.0.113.1:40000`.
The retained trace exposes the selected headers at ingress, forward, and egress.
[Generated permit policy](../../examples/campus/native/input/permit.json).
[Gateway B trace](../../examples/campus/native/b-trace.txt).

Conntrack's original and reply directions describe connection metadata, not these generated policy class names.
Nftables provides separate expressions for packet headers and direction-specific conntrack tuple fields.
[Official nftables manual, conntrack expressions](https://netfilter.org/projects/nftables/manpage.html).

The source and committed records retain the original service tuple and the translated reply tuple separately.
B's committed record has zone zero, status `440`, and an observed remaining timeout of `179` seconds.
Its kernel connection identifier differs from A's identifier.
[A source record](../../examples/campus/native/establish-after-a-conntrack.json).
[B committed record](../../examples/campus/native/commit-after-b-conntrack.json).

Each gateway receives its own policy installation and subsequent ruleset exports.
The evidence boundary consumes the actual export available at each transition prefix.
An input policy file or command acknowledgment alone cannot establish the installed rules.
This interpretation assumes faithful exports and no concurrent policy writer within the selected intervals.
It provides no trusted global, instantaneous update across both gateways.
[Policy operations and readback references](../../examples/campus/native/capture.json).
[Installed primary permit](../../examples/campus/native/install-primary-permit-after-a-nftables.json).
[Installed standby permit](../../examples/campus/native/install-standby-permit-after-b-nftables.json).

## Selected tickets, drain, and withdrawal

One packet selects A before the client route changes.
The `cal` netem queue retains one packet with a 61-byte backlog while B serves an overtaking request and reply.
The delayed packet later reaches the server through A.
The barrier records its completion and an empty queue before A's two data interfaces are fenced.
[Pending primary queue](../../examples/campus/native/overtake-reply-after-cal-qdisc.json).
[Completion and fence sequence](../../examples/campus/native/capture.json).
[Primary barrier](../../examples/campus/native/primary-barrier-cal-qdisc.json).

The route acknowledgment alone supplies no drain observation.
Deleting a qdisc can discard queued traffic; deletion therefore cannot substitute for the selected packet's completion.
The pinned Linux and iproute2 source analysis specifies these narrower queue and acknowledgment semantics.
[Route acknowledgment implementation](https://git.kernel.org/pub/scm/network/iproute2/iproute2.git/tree/lib/libnetlink.c?id=dac1bc6021693902b25a961227e289791e429b91#n1003).
[Netem reset implementation](https://git.launchpad.net/~ubuntu-kernel/ubuntu/+source/linux/+git/noble/tree/net/sched/sch_netem.c?h=Ubuntu-6.8.0-117.117#n784).

Withdrawal then stops A's conntrackd, disables `syncl`, and sets `net.ipv4.ip_forward` to zero.
Readbacks show no matching conntrackd process, all three A links down, and forwarding disabled.
Linux documents zero as disabling IPv4 forwarding between interfaces.
[Daemon absence](../../examples/campus/native/withdraw-a-daemon.json).
[Disabled links](../../examples/campus/native/withdraw-a-disabled-links.json).
[Forwarding readback](../../examples/campus/native/withdraw-a-disabled-settings.txt).
[Linux IP sysctl documentation](https://www.kernel.org/doc/html/latest/networking/ip-sysctl.html).

The last full A state boundary is `withdraw-primary:before`.
After withdrawal checks finish, later boundaries contain an explicit archive reference rather than new A kernel queries.
Archived A conntrack and policy records remain historical observations, not claims about A's later live kernel state.
B subsequently delivers the selected continued request and reply without another A query.
This is planned withdrawal with observed preparation, not recovery from an unexpected failure.
[Archive boundary, retirement time, and socket results](../../examples/campus/native/capture.json).
[Recorded commands](../../examples/campus/native/commands.json).

## Logoff and denial of queued traffic

Hostapd's receive handler sets `eapolLogoff` on EAPOL-Logoff.
Its authenticated state transitions to disconnected, which sets the logical port unauthorized.
These operations occur in `src/ap/ieee802_1x.c` and `src/eapol_auth/eapol_auth_sm.c`.
[Official hostapd 2.12 source](https://w1.fi/releases/hostapd-2.12.tar.gz).

The producer invokes the live supplicant's Logoff command and observes the authenticator's disconnect event.
The later station export lacks `[AUTHORIZED]` and records one received EAPOL-Logoff.
A separate operation then installs B's deny policy.
Logoff and gateway policy installation are distinct observed transitions.
[Logged-off station](../../examples/campus/native/eap/logged-off-station.txt).
[Logoff and deny operation order](../../examples/campus/native/capture.json).

A second packet selects B while permission still holds.
Its `cbl` queue retains one packet with a 61-byte backlog through Logoff and the deny installation.
On service, B's trace records established conntrack classification followed by the current forward policy's drop.
The receiver times out, and B's conntrack record remains present.
[Pending standby queue](../../examples/campus/native/install-standby-deny-after-cbl-qdisc.json).
[Installed deny export](../../examples/campus/native/install-standby-deny-after-b-nftables.json).
[Drop trace](../../examples/campus/native/b-trace.txt).
[Retained connection](../../examples/campus/native/serve-standby-after-b-conntrack.json).
[Socket result](../../examples/campus/native/capture.json).

A later reply also reaches B and encounters the deny policy.
Established conntrack state grants no automatic nftables accept verdict.
An unmatched packet reaches the base chain's configured drop policy.
[Official nftables manual, chain policy and ruleset evaluation](https://netfilter.org/projects/nftables/manpage.html).
[Later reply trace](../../examples/campus/native/b-trace.txt).

The selected barriers account for their named tickets, not every possible driver, link, gateway, or application buffer.
Raw observations support this finite sequence under explicit capture and concurrency assumptions.
They do not prove every interleaving, automatic election, arbitrary crash recovery, or universal packet absence.
