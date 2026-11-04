# Tracked forwarding lifecycle

The lifecycle checker replays ordered packet calls through routing, NAT, and stateful filters.
Each call uses the state left by the previous call and one declared configuration snapshot.
The model separates lookup, packet classification, filtering, and confirmation.
Its report checks supplied observations against that model.

## Run the examples

```sh
lake exe netlib lifecycle examples/lifecycle/replay.json --json
lake exe netlib stateful-refines examples/lifecycle/native/forward-established-only.json examples/lifecycle/native/forward-initial.json --json
```

The replay includes nine packet events and one deletion event.
A completed report is compliant exactly when every supplied packet and state observation agrees with the ordered model execution.
Observed values never replace the modeled output or state.
Exit code 0 means agreement, 1 means a mismatched observation, and 2 means unsupported input or a processing error.

The second command compares the permission sets of two filters at the same hook and priority.
It checks all five state labels and all modeled headers.
The comparison is static; it does not replay a configuration history.

## Packet stages

Each supported packet follows this order:

1. Look up its full zone and header key in the confirmed table.
2. Attach the stored binding, or derive a fresh candidate from the selected native NAT table on a lookup miss.
3. Classify the packet and record a valid reply as seen before later filtering.
4. Apply destination translation, then destination routing and the forward filter.
5. Apply source translation, then the late postrouting filter.
6. Confirm a fresh candidate only after successful forwarding and a unique-key check.

A reply is classified as `established`.
An original packet is `new` until its record has seen a reply, then `established`.
The `fresh` field means a lookup miss; it is separate from the `new` classification.
An unreplied original can remain `new` while reusing an existing binding.
It does not evaluate new NAT rules or replace that binding.

A route, forward-filter, or late-filter drop leaves a fresh candidate unconfirmed.
An existing reply can set the seen-reply flag even when a later stage drops it.
The next original can then match an established-only filter.
Neither classification nor a stored binding establishes that an application received the earlier packet.

The core proves these ordering and state effects.
Successful operations preserve compatible tuple pairs and unique bidirectional zone/header keys.
That validity invariant does not prove a general security, revocation, or availability contract.
See the [proof index](PROOFS.md) for the exact theorem scope.

## Replay schema 1

The [complete example](../examples/lifecycle/replay.json) embeds these root fields:

| Field | Meaning |
| --- | --- |
| `schema` | The integer `1`. |
| `routing` | iproute2 version, explicit interface bindings, and a main-table IPv4 route snapshot. |
| `configs` | Configuration snapshots with unique nonempty IDs. |
| `initial` | A supported full-status conntrack capture, or null for a declared empty initial table. |
| `events` | Ordered packet and deletion events, including at least one packet. |

Routing uses iproute2 6.19.0 and the [existing interface-binding format](LINUX.md).
Each configuration has `id`, `forward`, `late`, and `nat` fields.
The three policy fields contain complete nftables 1.1.3 JSON table exports.
The forward filter must use the forward hook.
The late filter must use postrouting at a priority greater than 100 and less than 2147483647.
These limits place it after the supported source NAT stage and before confirmation.
The configuration ID selects a snapshot for one call; it does not prove an update protocol or a safe cutover.

### Events and observations

| Event type | Other fields |
| --- | --- |
| `packet` | `config`, `zone`, `packet`, `observed`, and `state`. |
| `erase` | `zone`, `packet`, and `state`. |

`config` refers to a declared configuration ID.
`zone` is a 16-bit effective conntrack zone.
Packet headers have `source`, `destination`, `protocol`, `sourcePort`, and `destinationPort` fields.
Addresses use dotted IPv4 strings; the other fields use bounded integers.
The input cannot supply a candidate or an authorization flag.

Each packet observation has these fields:

| Field | Meaning |
| --- | --- |
| `classification` | The supplied observation of the current packet's state label. |
| `fresh` | Whether lookup missed before processing. |
| `afterDestination` | The header after destination translation. |
| `afterSource` | The header after source translation, or null if that stage was not reached. |
| `nextHop` | The modeled route binding, or null for a route drop. |
| `disposition` | `forwarded`, `routeDrop`, `forwardDrop`, or `lateDrop`. |
| `output` | The forwarded header, or null for a drop. |

An `erase` event removes the complete associated record when either direction key matches.
Both lookup keys disappear together.
Deletion of an absent association leaves the table unchanged.
This event represents an explicit operation; the model does not infer deletion from a later observation.

An event's `state` is a full-status capture after that event, or null when no table observation was supplied.
Event `state: null` means unobserved, not empty.
This differs from root `initial: null`, which declares an empty starting table.

State comparison uses original and reply headers, effective zones, source and destination NAT flags, and the seen-reply flag.
It ignores remaining timeout, record IDs, marks, use counts, other status metadata, and record order.
The source capture and its metadata remain retained evidence.
Timeout is not advanced during replay.
A zero reported timeout remains valid evidence and does not establish expiration.

## Imported policy subset

Stateful filters contain one IPv4 table and one filter base chain at forward or postrouting.
Supported rules combine the shared header matches with an optional `ct state` selection and one accept or drop verdict.
The compiler preserves first-match order and the explicit chain policy for every supplied state and header.
Numeric state bits from `nft -nn` retain the same selections as supported symbolic names.
Repeated state predicates, unknown bits, unsupported operators, side effects, and expressions after a verdict cause errors.

The NAT table has one prerouting destination chain at priority -100 and one postrouting source chain at priority 100.
Both use NAT type and accept policy.
Rules contain supported header matches followed by one fixed `dnat` or `snat` address and optional port.
A miss preserves the incoming header; an omitted port preserves its incoming value.
A matching identity target still stops that chain.
Ranges, maps, sets, dynamic targets, masquerade, flags, extra chains, and extra statements are unsupported.

The checker derives fresh tuple proposals from these rules, rather than accepting proposals from the trace input.
The proposal's NAT flags describe endpoint changes.
It does not establish an allocation decision or a pool invariant.
Fixed targets can collide, and a missing configured port does not prove that a native allocator preserves it.
The model reports confirmation collisions as errors.
A replay assumes that a confirmed fixed proposal is the applicable native allocation.
It does not simulate native remapping or clash recovery.
Existing bindings retain their tuples across NAT rule changes until an explicit deletion removes them.

## Static filter refinement

`stateful-refines STRONGER.json WEAKER.json` checks that every context permitted by the stronger filter is permitted by the weaker one.
The contexts cover `new`, `established`, `related`, `invalid`, and `untracked`, with every modeled header.
This does not prove that every label/header combination is reachable in a native execution.

Both snapshots must have the same hook and priority.
The checker specializes each state into an ordinary ACL and uses exact header partitions.
The default budget is 100,000 cells, summed across all five states.
Budget exhaustion returns exit code 2 without a refinement answer.
A failed comparison returns exit code 1 with a state and header counterexample.

The check compares filters at one fixed context.
It does not compare routes, NAT tables, stored bindings, histories, revocation, or whole-network upgrade contracts.
An established-only rule can preserve old traffic while denying fresh traffic.
Static permission inclusion alone does not establish that an update removes those existing flows.
The [output exclusion checker](REVOCATION.md) adds a separate late-filter contract and carries it through a replay suffix.

## Native evidence

The retained experiment uses nftables 1.1.3, conntrack-tools 1.4.9,
libnetfilter_conntrack 1.1.1, and iproute2 6.19.0 on kernel `6.8.0-117-generic`.
It records nine UDP packets, 30 traced chain visits, and eight table observations.
The [original trace](../examples/lifecycle/native/trace.txt),
[socket observations](../examples/lifecycle/native/observations.json), and
[checked evidence](../examples/lifecycle/checked-evidence.json) remain available.
The [provenance manifest](../examples/lifecycle/capture-provenance.json) records producer sources, image identities, and file hashes.
The [offline verifier](../scripts/check_lifecycle_capture.py) checks the retained trace and raw snapshot evidence separately from the Lean replay.
Available rule text is checked against exported expressions; handle-only entries are joined to the selected snapshot.
For default-drop packets, classification and freshness rely on the ordinary valid-packet profile and visible-table lookup miss.
The checked evidence marks this inference separately from directly traced fields.

The experiment demonstrates these cases:

- Destination translation occurs before the forward filter; source translation occurs afterward.
- Fresh forward and late drops do not appear as confirmed records in the reported dump.
- An unreplied `new` original reuses its stored translation after the NAT rules change.
- A dropped first reply sets seen-reply, enabling a later original through an established-only rule.
- Deletion makes the old original a fresh lookup under the changed rules, where the forward filter drops it.

The [container build](../examples/lifecycle/Dockerfile),
[capture script](../examples/lifecycle/capture.sh), and
[packet exercise](../examples/lifecycle/exercise.py) preserve the recipe.
These observations do not establish exact behavior for other kernels or a complete packet history.
The lifecycle capture supplies no TCP transport-state evidence.

## Capture recipe

Run from the repository root with a Linux Docker engine:

```sh
docker build -t netlib-conntrack-capture:1.4.9 examples/conntrack
docker build -t netlib-lifecycle-capture:6.19.0 examples/lifecycle
tar -cf - examples/lifecycle/capture.sh examples/lifecycle/exercise.py scripts/capture_conntrack.py | \
  docker run --rm --cap-add NET_ADMIN --cap-add SYS_ADMIN \
    --security-opt seccomp=unconfined --security-opt apparmor=unconfined \
    -i netlib-lifecycle-capture:6.19.0 sh -c \
    'mkdir /task && tar -xf - -C /task && sh /task/examples/lifecycle/capture.sh' > lifecycle-capture.tar
mkdir -p lifecycle-capture
tar -xf lifecycle-capture.tar -C lifecycle-capture
uv run --locked python scripts/check_lifecycle_capture.py --capture-dir lifecycle-capture
```

The capabilities and security settings allow private namespace and procfs mounts in the disposable container.
The command uses no host mounts or host networking.
Producer source archives are pinned by hash; package repositories and the engine kernel can change.
The retained manifest identifies the original image and package inventory.

The [example builder](../scripts/build_lifecycle_example.py) derives the checked evidence and replay from the retained native directory:

```sh
uv run --locked python scripts/build_lifecycle_example.py
uv run --locked python scripts/check_profiles.py
```

The profile checks verify the manifest hashes and compare the generated replay with the retained file.
A new capture must have its own reviewed evidence and provenance.

## Model boundary

Packets must be valid, unfragmented IPv4 TCP or UDP inputs whose transport tracker accepts the modeled attachment.
The implementation checks the protocol number; transport validation is an external assumption.
TCP tracker reopening or replacement, including `NF_REPEAT`, is unsupported.
So are timeout evolution, concurrent table changes, races, helper expectations, related traffic, untracked traffic, offload, and recovery from allocation clashes.
The ordinary lifecycle produces only `new` and `established`; the separate static filter check covers all five labels.

The selected route and policy snapshots must describe the relevant stable namespace and hook context.
Other hooks must not change the modeled headers or decisions.
Local input/output, policy routing, fragmentation, checksums, neighbor resolution, and delivery timing remain outside the model.
The proofs do not refine kernel C or establish full TCP admission, capture authenticity, or completeness of visible kernel state.
See the [conntrack evidence boundary](CONNTRACK.md) and the [stateless Linux bundle](LINUX.md) for their separate scopes.
