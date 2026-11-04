# Whole traffic classes

The `traffic` command checks every packet selected by a packet match.
It reuses a named query from a validated data-plane configuration.
The query keeps its endpoint selectors, kind, gateway set, and named request.
The supplied match replaces its single named packet header.

## Run a check

```sh
lake exe netlib traffic examples/dataplane/secure.json AVAILABLE examples/traffic/https.json --json
lake exe netlib traffic examples/dataplane/secure.json IDENTITY examples/traffic/https.json --json
lake exe netlib traffic examples/dataplane/bypass.json GATEWAY examples/traffic/https.json --json
```

The first command checks availability for every selected HTTPS header and endpoint pair.
The second checks isolation for the query's denied request.
The third finds a gateway bypass.
A failing result includes concrete packet representatives and path or cut evidence.

The match object uses the ACL match format:

```json
{
  "source": null,
  "destination": null,
  "protocol": 6,
  "sourcePorts": null,
  "destinationPorts": {"first": 443, "last": 443}
}
```

All five fields are necessary.
Null selects every value for a field.
An address selection contains `address` and `length` fields.
A port selection contains inclusive `first` and `last` bounds.
Unknown fields, invalid bounds, and unknown query IDs cause errors.
An empty traffic selection cannot produce a passing check.

## Exact finite coverage

The partition collects each ACL match, route prefix, and selection predicate.
It divides each header field at every relevant boundary.
One representative covers each Cartesian cell.
The proof establishes that every header belongs to a represented cell.
It also establishes equal ACL, route, physical-link, and request decisions within a cell.

`Config.model_representative` connects each representative to the original composed data-plane model.
`Query.trafficMeaning_iff` lifts the finite cell checks to every selected header.
`Check.checkTraffic` returns a result whose `correct` field proves that equivalence.
The existing graph checker supplies the path and cut certificates.

The tests include exceptions at a source port and a destination address.
The original fixed-header report passes those configurations.
The whole-class checks find their availability loss and unauthorized bypass.

## Resource budget and scope

The default budget is 100,000 Cartesian cells.
The checker counts those cells before it constructs their packet representatives.
An exhausted budget returns exit code 2 without a compliance result.
Use an explicit limit when necessary:

```sh
lake exe netlib traffic examples/dataplane/secure.json AVAILABLE examples/traffic/https.json --budget 1000 --json
```

The budget bounds partition size.
It does not bound total graph-search time or report size.
The number of cells is the product of the per-field interval counts.

The model remains stateless and uses IPv4 headers.
One named request remains fixed throughout the check.
Headers keep the same values throughout a path.
The checker does not model NAT, connection tracking, or dynamic route changes.
The [data-plane guide](DATAPLANE.md) defines the configuration and device-mapping assumptions.
