"""Project checked daemon replication and fenced handoff without seeding either table."""

import json
import re
from pathlib import Path

from check_replication_capture import check_capture

ROOT = Path(__file__).resolve().parents[1]
DIRECTORY = ROOT / "examples/replication"
OUTPUTS = ("checked-evidence", "replay")
GATEWAYS = {"a": "primary", "b": "standby"}
LEGS = {"original": "client", "reply": "server"}
NEIGHBORS = {
    "car": "client",
    "cbr": "client",
    "sar": "server",
    "sbr": "server",
    "syncl": "sync",
    "syncr": "sync",
}


def select_table(document, name):
    indices = []
    for index, item in enumerate(document["nftables"]):
        if len(item) != 1:
            raise ValueError("A native nftables object must retain one named kind.")
        kind, value = next(iter(item.items()))
        if (
            kind == "metainfo"
            or (kind == "table" and value.get("family") == "ip" and value.get("name") == name)
            or (
                kind in {"chain", "rule"}
                and value.get("family") == "ip"
                and value.get("table") == name
            )
        ):
            indices.append(index)
    objects = [document["nftables"][index] for index in indices]
    if (
        sum("metainfo" in item for item in objects) != 1
        or sum("table" in item for item in objects) != 1
    ):
        raise ValueError(
            "The native export must contain the selected table and metadata exactly once."
        )
    return {"nftables": objects}, indices


def route_bindings(routes):
    bindings = []
    for route in routes:
        if route.get("type", "unicast") != "unicast":
            continue
        device = route["dev"]
        binding = {"device": device, "nextNode": NEIGHBORS[device], "gateway": route.get("gateway")}
        if binding not in bindings:
            bindings.append(binding)
    return bindings


def build(directory=DIRECTORY):
    directory = Path(directory)
    evidence = check_capture(directory / "native")

    def native(name):
        return json.loads((directory / "native" / name).read_text())

    capture = native("capture.json")
    if [row["id"] for row in evidence["events"]] != [row["id"] for row in capture["events"]]:
        raise ValueError("The checked native event inventory changed during projection.")
    version = (directory / "native/iproute2-version.txt").read_text()
    matched = re.search(r"iproute2-([0-9.]+)", version)
    if matched is None:
        raise ValueError("The native route exporter version is absent.")
    routing = {}
    routing_sources = {}
    for actor, gateway in GATEWAYS.items():
        source = capture["initial"]["networks"][actor]["routes"]["file"]
        routes = native(source)
        routing[gateway] = {
            "version": matched[1],
            "bindings": route_bindings(routes),
            "routes": routes,
        }
        routing_sources[gateway] = source
    configs, projected_tables, events, sources, omitted = [], [], [], [], []
    for native_index, (checked, event) in enumerate(
        zip(evidence["events"], capture["events"], strict=True)
    ):
        kind, name = event["type"], event["id"]
        if kind == "policy":
            omitted.append({"nativeEvent": native_index, "id": name})
            continue
        result = {
            "type": kind,
            "states": {
                gateway: native(event["after"]["conntrack"][actor]["file"])
                for actor, gateway in GATEWAYS.items()
            },
            "cache": None,
        }
        if kind == "packet":
            actor = event["gateway"]
            source = event["before"]["tables"][actor]["file"]
            document = native(source)
            config = {"id": name}
            for field, table in (
                ("forward", "netlib"),
                ("late", "netlib_late"),
                ("nat", "netlib_nat"),
            ):
                selected, indices = select_table(document, table)
                config[field] = selected
                projected_tables.append(
                    {"config": name, "field": field, "source": source, "objectIndices": indices}
                )
            configs.append(config)
            result.update(
                gateway=GATEWAYS[actor],
                leg=LEGS[event["leg"]],
                config=name,
                zone=0,
                rawIPv4=checked["inputHex"],
                observed={
                    "classification": checked["classification"],
                    "fresh": None,
                    "afterDestination": None,
                    "afterSource": None,
                    "nextHop": None,
                    "disposition": checked["disposition"],
                    "output": checked["outputEthernetHex"],
                },
            )
        elif kind == "stage":
            result.update(zone=0, key=checked["before"]["a"][0]["original"], cache=checked["cache"])
        elif kind == "commit":
            result["timeout"] = 180
        elif kind == "handoff":
            result.update(leg=LEGS[event["leg"]], gateway=GATEWAYS[event["destination"]])
        elif kind == "fence":
            result["gateway"] = GATEWAYS[event["gateway"]]
        else:
            raise ValueError(f"Unsupported checked handoff event: {kind}.")
        sources.append({"event": len(events), "nativeEvent": native_index, "id": name})
        events.append(result)
    evidence["projection"] = {
        "events": sources,
        "omittedPolicyEvents": omitted,
        "tables": projected_tables,
        "routing": routing_sources,
    }
    replay = {"schema": 1, "routing": routing, "configs": configs, "events": events}
    return evidence, replay


def main():
    evidence, replay = build()
    for name, value in zip(OUTPUTS, (evidence, replay), strict=True):
        (DIRECTORY / f"{name}.json").write_text(json.dumps(value, indent=2) + "\n")
    print(
        f"Built {len(replay['events'])} handoff replay events from {evidence['packetCount']} native datagrams."
    )


if __name__ == "__main__":
    main()
