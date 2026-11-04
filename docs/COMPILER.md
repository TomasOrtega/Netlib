# Compile packet requirements

The compiler accepts unordered permit and hard-deny requirements over packet classes.
It generates a firewall only when every permit is compatible with every prohibition.
Unspecified traffic is denied.
The [session compiler](SESSION_FIREWALL.md) derives these requirements from current EAP authorization and application credentials.

```sh
lake exe netlib compile-acl examples/linux/intent.json > generated.json
lake exe netlib compile-acl examples/linux/conflicting-intent.json
lake exe netlib compile-acl examples/linux/intent.json --budget 1000
```

The first command emits nftables JSON for review.
The second returns exit code 1 with the conflicting requirement IDs and a concrete packet.
Malformed input, unsupported emission, and exhausted budgets return exit code 2.
The command does not apply the generated firewall.

## Intent schema 1

The root object contains `schema` and `requirements` fields.
Each requirement contains `id`, `action`, and `match` fields.
Actions are `permit` and `deny`.
The match uses the [traffic-class format](TRAFFIC.md).

```json
{
  "schema": 1,
  "requirements": [
    {
      "id": "HTTPS",
      "action": "permit",
      "match": {
        "source": null,
        "destination": null,
        "protocol": 6,
        "sourcePorts": null,
        "destinationPorts": {"first": 443, "last": 443}
      }
    }
  ]
}
```

IDs must be unique and contain only letters, digits, underscores, hyphens, or periods.
Native comments impose a 128-byte ID limit.
An empty requirement list is invalid.
Empty packet classes have no effect on the abstract ACL semantics.
A prohibition-only policy compiles to deny every packet.

Port matches require an explicit TCP or UDP protocol for native emission.
The emitter rejects reversed ranges and unsupported protocol/port combinations.
It never changes a match by adding an unstated protocol condition.

## Proof chain

The exact packet partition finds every overlap between permitted and prohibited classes.
A conflict includes both original requirements and a header that satisfies both matches.
`Conflict.unsatisfiable` proves that no ACL can satisfy those two demands.
Budget exhaustion returns an error before a successful compilation can occur.

`ACL.Certified.correct` proves exact all-header equivalence between the source intent and the generated ACL.
`ACL.Certified.satisfies` establishes every declared permit and prohibition.
The certificate retains all original requirement IDs.
Emitted permit entries retain their individual IDs.

`Nftables.Emitted.correct` transfers the result to a structured native-format snapshot.
The JSON serializer and Linux execution have separate roundtrip and native interoperability tests.
They are not covered by that structured theorem.
The [Linux guide](LINUX.md#native-evidence) records the native producer evidence.

## Deployment scope

Generated JSON describes a dedicated IPv4 table named `netlib` and a forward chain named `forward`.
Its chain policy is drop.
Permit-rule comments preserve their requirement IDs.
The artifact contains additions and no removal of existing policies.
Its modeled meaning requires a fresh table and exclusive forwarding behavior for the selected packets.
Other base chains and hooks can change the final Linux decision.

The output is a configuration artifact for review.
The compiler does not prove the existing host state, deployment operation, or parser implementation.
Certified deployment transitions remain part of the broader roadmap.
