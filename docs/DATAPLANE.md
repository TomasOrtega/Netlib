# Packet and request checks

The data-plane command combines the packet, route, and identity models.
It reads a versioned JSON model and checks every selected endpoint pair.
Each successful report carries proofs for its results and final status.
Use [whole traffic classes](TRAFFIC.md) to check all headers selected by a packet match.

## Run the examples

Run these commands from the repository root:

```sh
lake exe netlib dataplane examples/dataplane/secure.json
lake exe netlib dataplane examples/dataplane/bypass.json --json
lake exe netlib dataplane examples/dataplane/acl-deny.json
lake exe netlib dataplane examples/dataplane/route-drop.json
lake exe netlib dataplane examples/dataplane/disabled.json
lake exe netlib dataplane examples/dataplane/unauthorized.json
```

The secure model passes four requirements.
An admitted request reaches the server through its enforcement gateway.
The same path blocks a principal whose identity check fails.
Packet rules also block the SSH traffic class.

The bypass model adds a host route and a physical link around the gateway.
The admitted request still reaches the server.
The denied request also reaches it through the bypass.
Both isolation and gateway mediation then fail.

The other models change one control:

| Model | Change | Result |
| --- | --- | --- |
| `acl-deny.json` | Put a deny rule before the permit rule. | Availability fails. |
| `route-drop.json` | Add a matching host drop route. | Availability fails. |
| `disabled.json` | Disable the final physical link. | Availability fails. |
| `unauthorized.json` | Remove the admitted principal's permission. | Availability fails. |

## Graph semantics

Each forwarding step must satisfy four controls:

1. Both nodes exist and an enabled physical link connects them.
2. The longest matching route selects that link's target.
3. The link's ordered access control list permits the packet.
4. The supplied request policy permits any step incident to an enforcement gateway.

The route lookup keeps the first entry when matching prefix lengths are equal.
A selected drop route has no next hop.
A missing route also has no next hop.
A route never creates a physical connection.

The first matching packet rule supplies the action.
The ACL default is deny.
An empty ACL therefore blocks its physical link for every packet.
An absent packet-match field accepts every value for that field.

Authentication and permission checks both control request admission.
A denied request cannot enter or leave the enforcement gateway set.
A path outside that set can still carry the request.
A separate mediation requirement detects this bypass.

Reachability includes a path with zero steps from a node to itself.
A denied request still has this self path.
A gateway at either endpoint satisfies a mediation requirement.
Mediation can hold when no path exists.
State a reachability requirement when availability is necessary.

## Schema 1

Every top-level field is necessary:

| Field | Content |
| --- | --- |
| `schema` | The integer `1`. |
| `devices` | Device records with `id`, `zone`, and `role`. |
| `groups` | Group records with `name` and `members`. |
| `links` | Physical link records with `from`, `to`, `enabled`, and `acl`. |
| `routes` | Route tables with `node` and `entries`. |
| `principals` | Principal records with `id` and Boolean `authenticated`. |
| `resources` | Declared resource names. |
| `operations` | Declared operation names. |
| `permissions` | Allowed triples of `principal`, `resource`, and `operation`. |
| `requests` | Named requests with `id`, `principal`, `resource`, and `operation`. |
| `traffic` | Named fixed packet headers. |
| `enforcement` | A nonempty node, zone, role, or group selector. |
| `requirements` | The complete query list. |

A traffic record has `id`, `source`, `destination`, `protocol`, `sourcePort`, and `destinationPort` fields.
The addresses are unsigned 32-bit integers.
Protocol numbers use 8 bits.
Port numbers use 16 bits.
The importer rejects fractional, negative, and out-of-range values.
For example, `167772161` represents the IPv4 address `10.0.0.1`.

A route entry has `destination` and `nextHop` fields.
Its destination has an `address` integer and a `length` from `0` through `32`.
A string next hop names a declared device.
A null next hop states a drop route.

An ACL rule has `match` and `action` fields.
Its action is `permit` or `deny`.
Every match has these fields:

- `source` and `destination` contain address prefixes or null.
- `protocol` contains a protocol number or null.
- `sourcePorts` and `destinationPorts` contain port ranges or null.

A port range has `first` and `last` fields.
Both bounds are inclusive.
The importer rejects reversed bounds.

Each requirement has these fields:

```json
{
  "id": "AVAILABLE",
  "kind": "reach",
  "source": "node:client",
  "target": "node:server",
  "traffic": "https",
  "request": "alice-read",
  "gateways": null
}
```

The kinds are `reach`, `isolate`, and `mediated`.
A mediated requirement must supply a nonempty gateway selector.
Other requirements must use null for `gateways`.
Each requirement applies to every selected source and target pair.
All traffic and request references must exist.
Every endpoint selection must contain a device.

Unknown fields, missing fields, duplicate names, and invalid references cause errors.
Physical endpoint pairs and route table names must be unique.
The importer also rejects duplicate permission triples.

## Guarantees and limits

`Config.finiteNetwork_eq_model` connects the executable edge test to the composed library graph.
Each search result contains an accepted path or closed-cut certificate.
`Check.Report.compliant_iff` proves that a successful report passes exactly when every original query holds.
The report also preserves the original query list and its order.

The model keeps one packet header and one request fixed along each queried path.
It excludes address rewriting, packet lifetime, connection state, and dynamic routing protocols.
It supports IPv4 headers only.

The input supplies identity results and permission facts.
Reviewers must check their source and accuracy.
Reviewers must also check the relation between packet addresses, resources, and device identities.
These inputs do not prove cryptographic authentication or live device behavior.
