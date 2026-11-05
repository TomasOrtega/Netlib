"""Project checked endpoint admissions and later gateway processing into one replay."""

import json
import re
from pathlib import Path

from build_replication_examples import GATEWAYS, LEGS, route_bindings, select_table
from check_safe_handoff_capture import check_capture

ROOT = Path(__file__).resolve().parents[1]
DIRECTORY = ROOT / "examples/safe-handoff"
OUTPUTS = ("checked-evidence", "replay")


def build(directory=DIRECTORY):
    directory = Path(directory)
    evidence = check_capture(directory / "native")

    def native(name):
        return json.loads((directory / "native" / name).read_text())

    def boundary(name):
        return evidence["boundaries"][name]

    def states(event):
        return {
            gateway: native(event["snapshots"]["after"][actor])
            for actor, gateway in GATEWAYS.items()
        }

    configs, table_sources = [], []

    def configuration(name, actor, observed):
        document = observed["tables"][actor]
        reference = observed["native"]["tables"][actor]["file"]
        config = {"id": name}
        for field, table in (
            ("forward", "netlib"),
            ("late", "netlib_late"),
            ("nat", "netlib_nat"),
        ):
            value, indices = select_table(document, table)
            config[field] = value
            table_sources.append(
                {"config": name, "field": field, "source": reference, "objectIndices": indices}
            )
        configs.append(config)
        return name

    initial = {
        gateway: configuration(f"initial-{gateway}", actor, boundary("initial"))
        for actor, gateway in GATEWAYS.items()
    }
    version = re.search(
        r"iproute2-([0-9.]+)", (directory / "native/iproute2-version.txt").read_text()
    )
    if version is None:
        raise ValueError("The native route exporter version is absent.")
    routing, route_sources = {}, {}
    for actor, gateway in GATEWAYS.items():
        observed = boundary("initial")
        routes = observed["networks"][actor]["routes"]
        routing[gateway] = {
            "version": version[1],
            "bindings": route_bindings(routes),
            "routes": routes,
        }
        route_sources[gateway] = observed["native"]["networks"][actor]["routes"]["file"]
    events, event_sources, omitted = [], [], []

    def append(value, native_index, native_event, phase):
        event_sources.append(
            {
                "event": len(events),
                "nativeEvent": native_index,
                "id": native_event["id"],
                "phase": phase,
            }
        )
        events.append(value)

    def observed(packet):
        return {
            "classification": packet["classification"],
            "fresh": packet["fresh"],
            "afterDestination": None,
            "afterSource": None,
            "nextHop": None,
            "disposition": packet["disposition"],
            "output": packet["outputEthernetHex"],
        }

    for index, event in enumerate(evidence["events"]):
        kind, name = event["type"], event["id"]
        if kind in {"qdisc", "barrier"}:
            omitted.append({"nativeEvent": index, "id": name, "type": kind})
            continue
        common = {"states": states(event), "cache": None}
        if kind == "packet" and name == "establish":
            packet = event["packet"]
            append(
                {
                    "type": "establish",
                    "zone": 0,
                    "rawIPv4": packet["admission"]["raw"],
                    "observed": observed(packet),
                    **common,
                },
                index,
                event,
                "establish",
            )
        elif kind in {"packet", "admit", "serve"}:
            packet = event["packet"]
            if kind in {"packet", "admit"}:
                admitted = {
                    "type": "admit",
                    "direction": event["leg"],
                    "rawIPv4": packet["admission"]["raw"],
                    "observedID": event["ticket"],
                    "states": {"primary": None, "standby": None}
                    if kind == "packet"
                    else common["states"],
                    "cache": None,
                }
                append(admitted, index, event, "admit")
            if kind in {"packet", "serve"}:
                served = {
                    "type": "serve",
                    "id": event["ticket"],
                    "rawIPv4": packet["inputHex"],
                    "observed": observed(packet),
                    **common,
                }
                append(served, index, event, "serve")
        elif kind == "stage":
            append(
                {
                    "type": "stage",
                    "zone": 0,
                    "key": event["before"]["a"][0]["original"],
                    **common,
                    "cache": event["cache"],
                },
                index,
                event,
                "stage",
            )
        elif kind == "commit":
            append({"type": "commit", "timeout": 180, **common}, index, event, "commit")
        elif kind == "handoff":
            append(
                {
                    "type": "handoff",
                    "leg": LEGS[event["leg"]],
                    "gateway": GATEWAYS[event["destination"]],
                    **common,
                },
                index,
                event,
                "handoff",
            )
        elif kind == "fence":
            append(
                {"type": "fence", "gateway": GATEWAYS[event["gateway"]], **common},
                index,
                event,
                "fence",
            )
        elif kind == "policy":
            actor = event["gateway"]
            config = configuration(name, actor, boundary(f"{name}:after"))
            append(
                {"type": "install", "gateway": GATEWAYS[actor], "config": config, **common},
                index,
                event,
                "install",
            )
        else:
            raise ValueError(f"Unsupported checked safe handoff event: {kind}.")
    evidence["projection"] = {
        "events": event_sources,
        "omittedQueueEvents": omitted,
        "tables": table_sources,
        "routing": route_sources,
    }
    replay = {
        "schema": 1,
        "routing": routing,
        "configs": configs,
        "initialConfigs": initial,
        "events": events,
    }
    return evidence, replay


def main():
    evidence, replay = build()
    for name, value in zip(OUTPUTS, (evidence, replay), strict=True):
        (DIRECTORY / f"{name}.json").write_text(json.dumps(value, indent=2) + "\n")
    print(
        f"Built {len(replay['events'])} safe handoff operations from {evidence['packetCount']} native datagrams."
    )


if __name__ == "__main__":
    main()
