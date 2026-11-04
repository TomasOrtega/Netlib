# A packet remains queued after a barrier

The private capture sends one UDP packet through NAT and a late postrouting filter.
A four-second netem delay holds that packet on the router's `outside0` output queue.
The capture confirms a visible conntrack row and one queued packet before installing a backend UDP barrier.
The old payload then reaches the server after installation.
A distinct later payload uses the same original tuple and receives a traced late drop.

The [checked evidence](checked-evidence.json) records two packet traces, eight hook visits, and four raw conntrack snapshots.
The qdisc observations report queue lengths `0`, `1`, `1`, and `0`.
The final qdisc counters report one packet, 66 bytes, and zero backlog.
The [observations](native/observations.json) retain monotonic send, receive, command, and observation intervals.
The receiver starts before the old send.
The old receive finishes after barrier installation and the later blocked send.

Both packets use the original tuple `192.0.2.2:31000` to `203.0.113.2:8080`.
The wire tuple is `203.0.113.1:40000` to `198.51.100.2:9000`.
The confirmed unreplied association retains status `440` across installation and delivery.
The later original packet remains classified `new` while using that cached association.
The barrier matches the backend address and UDP protocol at every destination port.
It runs at postrouting priority `110`, after source NAT and before confirmation in the supported ordinary path.
The [source note](../../docs/research/POSTROUTING_QUEUES.md) records the kernel and iproute2 evidence for this ordering.

## Verify the retained evidence

```sh
UV_CACHE_DIR=/private/tmp/netlib-uv-cache uv run --locked python scripts/check_drain_capture.py
UV_CACHE_DIR=/private/tmp/netlib-uv-cache uv run --locked python -m unittest discover -s scripts -p test_check_drain_capture.py
```

The verifier reads no Lean output and imports no native collector decoder.
It reuses the frozen lifecycle verifier's independent Netlink decoder and strict trace helpers.
It checks raw bytes against structured conntrack records, exact active rules, handles, policies, translated headers, and route selection.
It checks distinct payload identities, traced packet lengths, monotonic ordering, qdisc configuration, and counter changes.
The tests reject contradictory times, queue counts, delay settings, payloads, raw status, rule text, handles, policies, and missing evidence.

The `tc` JSON exports are retained producer output, not independent raw qdisc Netlink decoding.
Their counters contain no payload identity.
The mapping from the single queued packet to the old payload uses the isolated recipe and matching socket observations.
The recipe uses private namespaces, fixed permanent neighbors, and disabled IPv6.
The [neighbors](native/neighbors.json), [links](native/links.json), and namespace settings retain those conditions.

## Repeat the capture

The capture uses the pinned lifecycle image from the [parent recipe](../lifecycle/Dockerfile).
Its image ID is in the [provenance manifest](capture-provenance.json).
The runtime kernel and package inventory are retained separately.
The actual `tc` version is `6.17.0`; the actual `ip` version is `6.19.0`.

Run from the repository root with that image and a Linux Docker engine:

```sh
tar -cf - examples/drain/capture.sh examples/drain/exercise.py scripts/capture_conntrack.py | \
  docker run --rm --network none --cap-add NET_ADMIN --cap-add SYS_ADMIN \
    --security-opt seccomp=unconfined --security-opt apparmor=unconfined \
    -i sha256:566c6af8672a432d7b9db65593d54e5d6d5f0fd5e98e644979f9adefedc0bebd sh -c \
    'mkdir /task && tar -xf - -C /task && sh /task/examples/drain/capture.sh' > drain-capture.tar
mkdir -p drain-capture
tar -xf drain-capture.tar -C drain-capture
UV_CACHE_DIR=/private/tmp/netlib-uv-cache uv run --locked python scripts/check_drain_capture.py --capture-dir drain-capture
```

The command uses no host mounts or host networking.
The capabilities permit namespace and private procfs creation inside the disposable container.
A new capture needs its own evidence review and provenance.

## Scope

This finite capture demonstrates delayed delivery across one retained barrier installation.
It does not prove universal FIFO order, eventual service, or a physical drain-time bound.
It does not establish kernel C refinement, capture authenticity, complete packet history, or complete buffering visibility.
The barriers constrain later hook decisions.
They do not remove packets that have already passed those hooks.
