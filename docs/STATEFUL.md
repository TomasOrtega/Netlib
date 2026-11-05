# Packet transformations and flow state

These models extend the packet library with explicit header changes and timed flow authorization.
The commands cover different questions:

| Command | Input coverage | Packet behavior |
| --- | --- | --- |
| `dataplane` | One named header per query. | The header remains fixed along a path. |
| `traffic` | Every header in the selected class. | Each queried path retains its initial header. |
| `transfer` | One initial header and all modeled paths and output headers. | Declared steps can overwrite header fields. |
| `nat-trace` | Every supplied packet event in one ordered trace. | Mappings and return-flow grants change over time. |

The Linux snapshot adapter still accepts its documented stateless subset.
The new models need separate bindings to native NAT and connection-tracking behavior.

## Header-changing forwarding

```sh
lake exe netlib transfer examples/transfer/dnat.json --json
lake exe netlib transfer examples/transfer/mediated.json --json
lake exe netlib transfer examples/transfer/gateway-bypass.json --json
```

The first example changes the destination address and port before later filtering.
The packet enters with destination port 80 and reaches the server with port 443.
Removing that rewrite makes the same initial packet fail.
The bypass example finds a path that avoids the declared firewall stage.

Transfer schema 1 contains `nodes`, `links`, and `query` fields, plus `schema: 1`.
Each link has `from`, `to`, `match`, and `rewrite` fields.
Its match uses the [packet-match format](TRAFFIC.md).
The guard reads the incoming header.
The rewrite applies before arrival at the target node.
Each matching link remains a permitted alternative.
Separate stage nodes represent ordered processing.

The rewrite has `source`, `destination`, `protocol`, `sourcePort`, and `destinationPort` fields.
Null preserves a field.
Address replacements use dotted IPv4 strings.
Protocol and port replacements use bounded integers.

The query has `kind`, `source`, `target`, `header`, and `gateways` fields.
Kinds are `reach`, `isolate`, and `mediated`.
The initial header has the same five fields as the rewrite, with concrete values instead of null.
Mediation needs a nonempty gateway list.
Other kinds require an empty list.

Reachability permits any resulting header at the target node.
Isolation excludes every resulting header.
Mediation excludes every bypass, including paths with rewritten headers.
A gateway endpoint satisfies mediation.
Zero-step self reachability remains part of the model.

### Finite state coverage

The checker constructs a finite header universe from initial values and every overwrite constant.
The universe also supports header reversal.
Closure proofs establish that no modeled path can escape it.
Each search vertex retains both its device and complete current header.
Returned paths and closed cuts have checked certificates.

The default budget is 4,096 device/header states.
The checker computes the exact product size before constructing its state list.
Budget exhaustion returns exit code 2 without a query result.
An internal certificate failure also returns an error.
Each returned answer covers the full query semantics.
There is no separate theorem guaranteeing successful search completion for every valid input.

## Timed source NAPT traces

```sh
lake exe netlib nat-trace examples/nat/secure.json --json
lake exe netlib nat-trace examples/nat/wrong-peer-admitted.json --json
lake exe netlib nat-trace examples/nat/expired-admitted.json --json
```

The model separates endpoint-independent mapping from address-and-port-dependent filtering.
A mapping identifies an inside endpoint and protocol with one public endpoint.
The same mapping can serve several remote peers.
Each peer still needs a live grant for its exact reversed five-tuple.
An active mapping alone does not authorize an arbitrary peer.

Source NAPT follows the terminology in [RFC 3022, section 2.2](https://www.rfc-editor.org/rfc/rfc3022.html#section-2.2).
[RFC 4787, sections 4.1 and 5](https://www.rfc-editor.org/rfc/rfc4787.html#section-4.1) separate mapping and filtering behavior.
This local model does not establish complete conformance with those documents.

### Trace schema 1

The root object has `schema`, `policy`, and `events` fields.
The policy uses the [packet-intent schema](COMPILER.md).
Outbound permission comes from its certified ACL.
The input cannot supply an `authorized` flag.

| Event type | Other fields |
| --- | --- |
| `outbound` | `packet`, `allocation`, `expiresAt`, and `observed`. |
| `inbound` | `packet` and `observed`. |
| `advance` | `now`. |
| `close` | The original outbound `packet`. |
| `flush` | None. |

An allocation has a dotted IPv4 `address` and a bounded `port`.
Packet fields are `source`, `destination`, `protocol`, `sourcePort`, and `destinationPort`.
Packet addresses use dotted strings.
Observed output is a complete packet or null for a recorded drop.
The trace must include a packet event and begin from the declared empty initial state.

Allocation and deadline values are supplied inputs.
Time uses one common abstract unit.
An `advance` event cannot move backward.
Expiration occurs when the current time reaches the deadline.
Closing a flow removes its grant while its mapping can remain.
Flushing clears mappings and grants while preserving the clock.

The auditor computes its model output independently of the observation.
Each finding preserves the event index, expected output, and observed output.
A report passes exactly when every supplied packet observation matches the model.
Correct denials can pass.
A passing report proves that each restored reply has an earlier outbound source permitted by the declared policy.
Trace completeness, accurate observations, and clock interpretation remain assumptions.

The default `--budget` is 100,000 policy partition cells.
It bounds policy compilation, not trace length, table size, or total processing time.

### Alias reuse and freshness

```sh
lake exe netlib nat-trace examples/nat/alias-reuse.json --json
```

This passing local trace demonstrates a freshness limit.
An old flow expires completely before a different inside endpoint reuses its public alias.
The delayed old reply has the same external five-tuple as a reply for the new flow.
The model therefore restores it to the new inside endpoint.

`Theory.NATReuse` proves that information loss and a general header-only indistinguishability result.
It also proves that the current safety invariant holds during the counterexample.
Mapping consistency and policy provenance cannot establish packet freshness.
Stronger freshness claims require additional observations or lifecycle assumptions.

The model excludes TCP flags, sequence windows, handshake state, checksums, fragmentation, and payload authentication.
It does not prove an allocation pool, native Linux conntrack correspondence, or RFC timeout minima.
The supplied public endpoints have no proved ownership or routability.
