"""Project one checked wired authentication and gateway withdrawal execution."""

import json
import re
from pathlib import Path

from build_replication_examples import GATEWAYS, LEGS, route_bindings, select_table
from check_campus_capture import check_capture

ROOT = Path(__file__).resolve().parents[1]
DIRECTORY = ROOT / "examples/campus"
OUTPUTS = ("checked-evidence", "bundle")


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

    phases = evidence["eapEvidence"]["phases"]
    if len(phases) != 1 or phases[0]["name"] != "success":
        raise ValueError("The joint deployment requires one actual successful EAP episode.")
    phase = phases[0]
    frames = phase["frames"]
    before_logoff = phase["logoffFrame"] - 1
    if not 0 < phase["terminalFrame"] <= before_logoff < len(frames):
        raise ValueError("The actual terminal and Logoff prefixes are not ordered.")
    starts = sum(frame["eapol"]["type"] == 1 for frame in frames[:before_logoff])
    if starts != 1 or any(frame["eapol"]["type"] == 2 for frame in frames[:before_logoff]):
        raise ValueError("The joint EAP projection requires one Start and no earlier Logoff.")
    authentication, events, timeline = [], [], []
    sources, omitted = [], []
    consumed = 0

    def append(kind, value, native_index, event, phase_name):
        values = authentication if kind == "authentication" else events
        reference = {"type": kind, "event": len(values)}
        values.append(value)
        sources.append(
            {
                "timeline": len(timeline),
                "nativeEvent": native_index,
                "id": event["id"],
                "phase": phase_name,
                **reference,
            }
        )
        timeline.append(reference)

    def auth_frames(stop, native_index, event):
        nonlocal consumed
        if not consumed < stop <= len(frames):
            raise ValueError(
                "Authentication observations must advance through the same frame history."
            )
        while consumed < stop:
            frame = frames[consumed]
            append(
                "authentication",
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
                append(
                    "authentication",
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
        if kind == "authentication":
            if name == "authenticate":
                if authentication or consumed:
                    raise ValueError("Authentication must begin with the single actual episode.")
                append(
                    "authentication", {"type": "begin", "authorized": None}, index, event, "begin"
                )
                auth_frames(before_logoff, index, event)
            elif name == "logoff":
                auth_frames(len(frames), index, event)
            else:
                raise ValueError(f"Unsupported authentication operation: {name}.")
            continue
        if kind == "credential":
            append(
                "authentication",
                {"type": "install", "credential": evidence["credential"], "authorized": True},
                index,
                event,
                "credential",
            )
            continue
        if kind == "withdraw":
            sources.append(
                {"timeline": len(timeline), "nativeEvent": index, "id": name, "phase": "withdraw"}
            )
            timeline.append({"type": "withdraw"})
            continue
        if kind in {"qdisc", "barrier"}:
            omitted.append({"nativeEvent": index, "id": name, "type": kind})
            continue
        common = {"states": states(event), "cache": None}

        def network(value, phase_name):
            append("network", value, index, event, phase_name)

        if kind == "packet" and name == "establish":
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
            )
        elif kind in {"packet", "admit", "serve"}:
            packet = event["packet"]
            if kind in {"packet", "admit"}:
                network(
                    {
                        "type": "admit",
                        "direction": event["leg"],
                        "rawIPv4": packet["admission"]["raw"],
                        "observedID": event["ticket"],
                        "states": {"primary": None, "standby": None}
                        if kind == "packet"
                        else common["states"],
                        "cache": None,
                    },
                    "admit",
                )
            if kind in {"packet", "serve"}:
                network(
                    {
                        "type": "serve",
                        "id": event["ticket"],
                        "rawIPv4": packet["inputHex"],
                        "observed": observed(packet),
                        **common,
                    },
                    "serve",
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
                "stage",
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
            raise ValueError(f"Unsupported checked campus event: {kind}.")
    if consumed != len(frames):
        raise ValueError("Every actual EAP frame must be consumed by the same joint history.")
    authentication_input = {
        "schema": 1,
        "context": {
            "consumer": evidence["eapEvidence"]["subject"],
            "producer": "campus-application",
            "issuer": "campus-authority",
        },
        "link": evidence["eapEvidence"]["link"],
        "events": authentication,
    }
    intent = json.loads((directory / "requirements.json").read_text())
    application = intent["requirements"][0]["scope"]
    evidence["projection"] = {
        "timeline": sources,
        "omittedQueueEvents": omitted,
        "tables": table_sources,
        "routing": route_sources,
    }
    bundle = {
        "schema": 1,
        "application": application,
        "authentication": authentication_input,
        "intent": intent,
        "handoff": {
            "schema": 1,
            "routing": routing,
            "configs": configs,
            "initialConfigs": initial,
            "events": events,
        },
        "timeline": timeline,
    }
    return evidence, bundle


def build(directory=DIRECTORY):
    directory = Path(directory)
    evidence = check_capture(directory / "native", input_directory=directory)
    return project(evidence, directory)


def main():
    evidence, bundle = build()
    for name, value in zip(OUTPUTS, (evidence, bundle), strict=True):
        (DIRECTORY / f"{name}.json").write_text(json.dumps(value, indent=2) + "\n")
    print(
        f"Built {len(bundle['timeline'])} campus operations from {evidence['packetCount']} native datagrams."
    )


if __name__ == "__main__":
    main()
