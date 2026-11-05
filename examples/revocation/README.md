# Late-filter revocation evidence

This experiment blocks UDP output to backend `198.51.100.2` at every port.
It uses a postrouting filter at priority 110, after source NAT and before confirmation.
The retained capture has six packet traces, 22 chain visits, and seven raw conntrack snapshots.

## Recorded behavior

| Phase | Observed result |
| --- | --- |
| First original and reply | DNAT and SNAT deliver both directions; the record gains seen-reply. |
| Tighten forward and change NAT | The cached original still reaches backend port 9000 through public port 40000. |
| Install the late barrier | The cached original reaches the barrier after NAT, then drops; its record remains. |
| Delete the record | The same original becomes fresh and drops at the established-only forward filter. |
| Allow fresh forwarding | A fresh packet uses new ports 9003 and 40001, then drops at the same late barrier without confirmation. |

The [native rules](native/setup.nft) first map `203.0.113.2:8080` to `198.51.100.2:9000`
and map the source to `203.0.113.1:40000`.
The [NAT update](native/tighten-and-change-nat.nft) proposes backend port 9003 and public port 40001 for fresh flows.
It does not replace the cached binding.
The [barrier rule](native/install-barrier.nft) selects destination `198.51.100.2` and protocol UDP, without a port constraint or state guard.

The [original text trace](native/trace.txt), [socket observations](native/observations.json),
[policy exports](native/barrier-closed.json), and raw state files remain unchanged.
[Checked evidence](checked-evidence.json) records every traced packet ID and its chain visits.
Classification and freshness rely on the recorded state and matching rules under the supported ordinary-tracking assumptions.
They are not direct observations of hidden kernel objects.

## Check the retained evidence

```sh
uv run --locked python scripts/check_revocation_capture.py examples/revocation/native
lake exe netlib lifecycle examples/revocation/replay.json --json
lake exe netlib lifecycle-blocks examples/revocation/replay.json examples/revocation/forbidden.json --from 3 --json
```

The independent Python verifier checks the raw Netlink messages, exported rules, trace order, and socket outcomes.
It reuses the frozen lifecycle trace and byte decoders; it does not read Lean results.
The [replay builder](../../scripts/build_revocation_example.py) derives the replay from that checked evidence.
The first barrier packet is operation 3 in the [seven-operation replay](replay.json).
The [forbidden selection](forbidden.json) covers post-NAT UDP output to the backend at any port.

The replay agrees with all supplied observations.
The exclusion command checks the late filters and excludes selected modeled outputs after the declared cutover.
Starting the exclusion check before the barrier fails, while those earlier packet observations still agree.
The [provenance manifest](capture-provenance.json) records producer versions, source hashes, image identity, commands, and fixture hashes.

## Reproduce in a disposable container

The capture used image `netlib-lifecycle-capture:6.19.0` with recorded ID
`sha256:566c6af8672a432d7b9db65593d54e5d6d5f0fd5e98e644979f9adefedc0bebd`.
The existing [conntrack](../conntrack/Dockerfile) and [lifecycle](../lifecycle/Dockerfile) Dockerfiles build its pinned producers.
The capture itself uses no host mounts or host networking.

From the repository root, prepare the four source dependencies and copy them into a new container:

```sh
docker build -t netlib-conntrack-capture:1.4.9 -f examples/conntrack/Dockerfile .
docker build -t netlib-lifecycle-capture:6.19.0 -f examples/lifecycle/Dockerfile .
task_dir=$(mktemp -d)
mkdir -p "$task_dir/examples/lifecycle" "$task_dir/examples/revocation" "$task_dir/scripts"
cp examples/lifecycle/exercise.py "$task_dir/examples/lifecycle/"
cp examples/revocation/capture.sh examples/revocation/exercise.py "$task_dir/examples/revocation/"
cp scripts/capture_conntrack.py "$task_dir/scripts/"
docker create --name netlib-revocation-example --network none \
  --cap-add NET_ADMIN --cap-add SYS_ADMIN \
  --security-opt seccomp=unconfined --security-opt apparmor=unconfined \
  netlib-lifecycle-capture:6.19.0 sh /task/examples/revocation/capture.sh
docker cp "$task_dir" netlib-revocation-example:/task
docker start --attach netlib-revocation-example > revocation.tar 2> revocation-stderr.txt
docker inspect netlib-revocation-example --format '{{.State.ExitCode}}'
docker rm netlib-revocation-example
mkdir new-native
tar -xf revocation.tar -C new-native
uv run --locked python scripts/check_revocation_capture.py new-native
```

`SYS_ADMIN` and the security options permit private namespace and procfs mounts inside the container.
The recipe enables forwarding only in its router namespace.
The successful capture exited with code 0.
Its [diagnostic output](capture-stderr.txt) retains package-index warnings from disabled networking and the native deletion count.
Trace IDs, native IDs, link addresses, and remaining timeout values can differ between captures.

## Scope

The native run covers UDP on kernel `6.8.0-117-generic`, not a TCP lifecycle or kernel C refinement.
The model requires accepted ordinary transport attachments, stable relevant tables, faithful observations, and complete selected packet events.
It excludes expiry, concurrent mutation, helpers, hidden clash objects, offload, and allocation recovery.
The fixed NAT rules supply proposals, not a proved allocator.
State comparison retains tuples, zones, NAT flags, and seen-reply while ignoring timeout, IDs, other metadata, and order.

The barrier blocks the selected output direction.
It does not assert that return traffic or other protocols are blocked, that records are removed, or that an application is isolated in every context.
Packets already past the barrier at cutover may still drain.
The experiment and model do not prove an atomic live cutover or queue-drain bound.
See the [lifecycle guide](../../docs/LIFECYCLE.md) for the full model boundary.
