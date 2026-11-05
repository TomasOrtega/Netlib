"""Project the fully checked native ingress-attachment execution for Lean."""

import argparse
import ipaddress
import json
import re
from pathlib import Path

from build_replication_examples import GATEWAYS, LEGS, NEIGHBORS, select_table
from check_attachment_capture import canonical_guard, check_capture

ROOT = Path(__file__).resolve().parents[1]
DIRECTORY = ROOT / "examples/attachments"
OUTPUTS = ("checked-evidence", "bundle")


def interface(reference):
    return {
        "namespace": reference["ns"],
        "ifindex": reference["ifindex"],
        "birth": reference["birth"],
    }


def traffic(header):
    return {
        "source": {"address": int(ipaddress.IPv4Address(header["source"])), "length": 32},
        "destination": {
            "address": int(ipaddress.IPv4Address(header["destination"])),
            "length": 32,
        },
        "protocol": header["protocol"],
        "sourcePorts": {"first": header["sourcePort"], "last": header["sourcePort"]},
        "destinationPorts": {
            "first": header["destinationPort"],
            "last": header["destinationPort"],
        },
    }


def route_bindings(routes):
    neighbors = {**NEIGHBORS, "aar": "attacker", "abr": "attacker"}
    bindings = []
    for route in routes:
        if route.get("type", "unicast") != "unicast":
            continue
        device = route["dev"]
        binding = {
            "device": device,
            "nextNode": neighbors[device],
            "gateway": route.get("gateway"),
        }
        if binding not in bindings:
            bindings.append(binding)
    return bindings


def observed(packet):
    rejected = not packet["guardAdmitted"]
    return {
        "classification": packet["classification"],
        "fresh": packet["fresh"],
        "afterDestination": None,
        "afterSource": None,
        "nextHop": None,
        "disposition": None if rejected else packet["disposition"],
        "output": packet["outputEthernetHex"],
    }


def project(evidence, directory):
    directory = Path(directory)

    def native(name):
        return json.loads((directory / "native" / name).read_text())

    def boundary(name):
        return evidence["boundaries"][name]

    def states(event):
        return {
            gateway: native(reference)
            if (reference := event["snapshots"]["after"].get(actor))
            else None
            for actor, gateway in GATEWAYS.items()
        }

    configs, table_sources = [], []

    def configuration(name, actor, source):
        config = {"id": name}
        for field, table in (
            ("forward", "netlib"),
            ("late", "netlib_late"),
            ("nat", "netlib_nat"),
        ):
            config[field], indices = select_table(source["tables"][actor], table)
            table_sources.append(
                {
                    "config": name,
                    "field": field,
                    "source": source["native"]["tables"][actor]["file"],
                    "objectIndices": indices,
                }
            )
        configs.append(config)
        return name

    initial = {
        gateway: configuration(f"initial-{gateway}", actor, boundary("initial"))
        for actor, gateway in GATEWAYS.items()
    }
    matched = re.search(
        r"iproute2-([0-9.]+)", (directory / "native/iproute2-version.txt").read_text()
    )
    if matched is None:
        raise ValueError("The native route exporter version is absent.")
    routing, route_sources = {}, {}
    for actor, gateway in GATEWAYS.items():
        routes = boundary("initial")["networks"][actor]["routes"]
        routing[gateway] = {
            "version": matched[1],
            "bindings": route_bindings(routes),
            "routes": routes,
        }
        route_sources[gateway] = boundary("initial")["native"]["networks"][actor]["routes"]["file"]

    phases = evidence["eapEvidence"]["phases"]
    if len(phases) != 1 or phases[0]["name"] != "success":
        raise ValueError("Use the single actual successful EAP episode.")
    phase = phases[0]
    frames = phase["frames"]
    before_logoff = phase["logoffFrame"] - 1
    if not 0 < phase["terminalFrame"] <= before_logoff < len(frames):
        raise ValueError("The actual terminal and Logoff prefixes are not ordered.")
    starts = sum(frame["eapol"]["type"] == 1 for frame in frames[:before_logoff])
    if starts != 1 or any(frame["eapol"]["type"] == 2 for frame in frames[:before_logoff]):
        raise ValueError("Use one actual Start and no earlier Logoff.")
    authentication, events, timeline = [], [], []
    sources, omitted, guard_sources = [], [], []
    consumed = 0

    def record(value, native_index, event, phase_name):
        sources.append(
            {
                "timeline": len(timeline),
                "nativeEvent": native_index,
                "id": event["id"],
                "phase": phase_name,
                **value,
            }
        )
        timeline.append(value)

    def auth(value, native_index, event, phase_name):
        record(
            {"type": "authentication", "event": len(authentication)},
            native_index,
            event,
            phase_name,
        )
        authentication.append(value)

    def auth_frames(stop, native_index, event):
        nonlocal consumed
        if not consumed < stop <= len(frames):
            raise ValueError("Authentication must consume the same advancing frame history.")
        while consumed < stop:
            frame = frames[consumed]
            auth(
                {
                    "type": "frame",
                    "raw": frame["raw"],
                    "authorized": phase["logicalAuthorization"]["afterLogoff"]
                    if consumed + 1 == phase["logoffFrame"]
                    else None,
                },
                native_index,
                event,
                f"frame/{consumed}",
            )
            consumed += 1
            if consumed == phase["terminalFrame"]:
                method = phase["methodEvidence"]
                auth(
                    {
                        "type": "method",
                        "round": 1 + starts,
                        "subject": method["subject"],
                        "method": method["method"],
                        "accepted": method["accepted"],
                        "source": "; ".join(
                            "native/eap/" + row["source"] for row in method["source"]
                        ),
                        "authorized": phase["logicalAuthorization"]["beforeLogoff"],
                    },
                    native_index,
                    event,
                    "method",
                )

    guards, attachments, maintenance = [], [], []
    for event in evidence["events"]:
        if event["type"] != "guard":
            continue
        name, actor = event["id"], event["gateway"]
        source = boundary(f"{name}:after")
        selected, indices = select_table(source["tables"][actor], "netlib_attachment")
        rules = canonical_guard(selected, source["networks"][actor]["links"])
        guards.append(
            {
                "id": name,
                "gateway": GATEWAYS[actor],
                "namespace": evidence["namespaceRefs"][actor],
                "bindings": [
                    {"name": port, "reference": interface(reference)}
                    for port, reference in evidence["interfaceRefs"][actor].items()
                ],
                "ruleset": selected,
            }
        )
        guard_sources.append(
            {
                "guard": name,
                "source": source["native"]["tables"][actor]["file"],
                "objectIndices": indices,
                "binding": event["native"]["result"]["binding"],
            }
        )
        if not event["active"]:
            continue
        for rule in rules:
            if rule["role"] == "SYNC":
                maintenance.append(
                    {
                        "ingress": interface(event["guard"]["dataPorts"]["maintenance"]),
                        "traffic": traffic(rule["header"]),
                    }
                )
            elif rule["role"] in {"ORIGINAL", "REPLY"}:
                direction = rule["role"].lower()
                attachments.append(
                    {
                        "id": f"{GATEWAYS[actor]}-{direction}",
                        "gateway": GATEWAYS[actor],
                        "ingress": interface(event["guard"]["dataPorts"][direction]),
                        "direction": direction,
                        "traffic": traffic(rule["header"]),
                    }
                )

    for index, event in enumerate(evidence["events"]):
        kind, name = event["type"], event["id"]

        def network(value, phase_name, packet=None):
            record(
                {
                    "type": "network",
                    "event": len(events),
                    "ingress": interface(packet["ingress"]) if packet else None,
                    "guard": packet["guardAdmitted"] if packet else None,
                },
                index,
                event,
                phase_name,
            )
            events.append(value)

        if kind == "authentication":
            if name == "authenticate":
                auth({"type": "begin", "authorized": None}, index, event, "begin")
                auth_frames(before_logoff, index, event)
            elif name == "logoff":
                auth_frames(len(frames), index, event)
            else:
                raise ValueError(f"Unsupported authentication operation: {name}.")
            continue
        if kind == "credential":
            auth(
                {"type": "install", "credential": evidence["credential"], "authorized": True},
                index,
                event,
                "credential",
            )
            continue
        if kind in {"qdisc", "barrier"}:
            omitted.append({"nativeEvent": index, "id": name, "type": kind})
            continue
        if kind in {"withdraw", "reset", "protect"}:
            record({"type": kind}, index, event, kind)
            continue
        if kind == "replication-start":
            record({"type": "maintenance", "entries": maintenance}, index, event, "maintenance")
            continue
        if kind == "guard":
            if event["active"]:
                for attachment in attachments:
                    if attachment["gateway"] == GATEWAYS[event["gateway"]]:
                        record(
                            {"type": "stage", "attachment": attachment["id"]},
                            index,
                            event,
                            "stage-attachment",
                        )
            record({"type": "installGuard", "guard": name}, index, event, "install-guard")
            continue
        common = {"states": states(event), "cache": None}
        if kind == "attack":
            packet = event["attack"]
            record(
                {
                    "type": "probe",
                    "gateway": GATEWAYS[event["gateway"]],
                    "ingress": interface(packet["ingress"]),
                    "direction": event["leg"],
                    "rawIPv4": packet["inputHex"],
                    "guard": packet["guardAdmitted"],
                    "observed": observed(packet),
                    "states": common["states"],
                },
                index,
                event,
                "probe",
            )
        elif kind == "packet" and name == "establish":
            packet = event["packet"]
            network(
                {
                    "type": "establish",
                    "zone": 0,
                    "rawIPv4": packet["admission"]["raw"],
                    "observed": observed(packet),
                    **common,
                },
                "establish",
                packet,
            )
        elif kind in {"packet", "admit", "serve", "serve-pair"}:
            packets = event["packets"] if kind == "serve-pair" else [event["packet"]]
            for ordinal, packet in enumerate(packets):
                ticket = packet["ticket"]
                if kind in {"packet", "admit"}:
                    network(
                        {
                            "type": "admit",
                            "direction": packet["leg"],
                            "rawIPv4": packet["admission"]["raw"],
                            "observedID": ticket,
                            "states": {"primary": None, "standby": None}
                            if kind == "packet"
                            else common["states"],
                            "cache": None,
                        },
                        "admit",
                    )
                if kind in {"packet", "serve", "serve-pair"}:
                    network(
                        {
                            "type": "serve",
                            "id": ticket,
                            "rawIPv4": packet["inputHex"],
                            "observed": observed(packet),
                            **common,
                            "states": {"primary": None, "standby": None}
                            if ordinal < len(packets) - 1
                            else common["states"],
                        },
                        "serve",
                        packet,
                    )
        elif kind == "stage":
            network(
                {
                    "type": "stage",
                    "zone": 0,
                    "key": event["before"]["a"][0]["original"],
                    **common,
                    "cache": event["cache"],
                },
                "replicate",
            )
        elif kind == "commit":
            network({"type": "commit", "timeout": 180, **common}, "commit")
        elif kind == "handoff":
            network(
                {
                    "type": "handoff",
                    "leg": LEGS[event["leg"]],
                    "gateway": GATEWAYS[event["destination"]],
                    **common,
                },
                "handoff",
            )
        elif kind == "fence":
            network({"type": "fence", "gateway": GATEWAYS[event["gateway"]], **common}, "fence")
        elif kind == "policy":
            actor = event["gateway"]
            config = configuration(name, actor, boundary(f"{name}:after"))
            network(
                {"type": "install", "gateway": GATEWAYS[actor], "config": config, **common},
                "install",
            )
        else:
            raise ValueError(f"Unsupported checked attachment operation: {kind}.")
    if consumed != len(frames):
        raise ValueError("Every actual EAP frame must be consumed in the joint history.")
    intent = native("input/requirements.json")
    evidence["projection"] = {
        "timeline": sources,
        "omittedQueueEvents": omitted,
        "tables": table_sources,
        "routing": route_sources,
        "guards": guard_sources,
    }
    bundle = {
        "schema": 1,
        "application": intent["requirements"][0]["scope"],
        "authentication": {
            "schema": 1,
            "context": {
                "consumer": evidence["eapEvidence"]["subject"],
                "producer": "campus-application",
                "issuer": "campus-authority",
            },
            "link": evidence["eapEvidence"]["link"],
            "events": authentication,
        },
        "intent": intent,
        "handoff": {
            "schema": 1,
            "routing": routing,
            "configs": configs,
            "initialConfigs": initial,
            "events": events,
        },
        "namespaces": {
            gateway: evidence["namespaceRefs"][actor] for actor, gateway in GATEWAYS.items()
        },
        "authenticationPort": interface(evidence["interfaceRefs"]["auth"]["auth0"]),
        "live": [
            interface(reference)
            for ports in evidence["interfaceRefs"].values()
            for reference in ports.values()
        ],
        "attachments": attachments,
        "guards": guards,
        "timeline": timeline,
    }
    return evidence, bundle


def build(directory=DIRECTORY, *, input_directory=DIRECTORY):
    directory = Path(directory)
    evidence = check_capture(directory / "native", input_directory=Path(input_directory))
    return project(evidence, directory)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("directory", nargs="?", type=Path, default=DIRECTORY)
    parser.add_argument("--input-directory", type=Path, default=DIRECTORY)
    arguments = parser.parse_args()
    evidence, bundle = build(arguments.directory, input_directory=arguments.input_directory)
    for name, value in zip(OUTPUTS, (evidence, bundle), strict=True):
        (arguments.directory / f"{name}.json").write_text(json.dumps(value, indent=2) + "\n")
    print(
        f"Built {len(bundle['timeline'])} attachment operations from {evidence['packetCount']} native datagrams."
    )


if __name__ == "__main__":
    main()
