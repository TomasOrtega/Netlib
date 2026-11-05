"""Check selected queued admissions, current-policy service, and guarded fencing."""

import argparse
import json
from pathlib import Path

import check_replication_capture as legacy
from capture_evidence import SAFE_BASE, SAFE_TC, CaptureEvidence, EvidenceError, require

ROOT = Path(__file__).resolve().parents[1]
EVENTS = (
    ("establish", "packet", {"gateway": "a", "leg": "original"}),
    ("replicate", "stage", {"source": "a", "destination": "b"}),
    ("commit", "commit", {"gateway": "b"}),
    ("install-primary-delay", "qdisc", {"interface": "cal", "delayMilliseconds": 2500}),
    ("admit-primary", "admit", {"gateway": "a", "leg": "original", "ticket": 0}),
    ("client-route", "handoff", {"leg": "original", "source": "a", "destination": "b"}),
    ("server-route", "handoff", {"leg": "reply", "source": "a", "destination": "b"}),
    ("overtake-request", "packet", {"gateway": "b", "leg": "original", "ticket": 1}),
    ("overtake-reply", "packet", {"gateway": "b", "leg": "reply", "ticket": 2}),
    ("serve-primary", "serve", {"gateway": "a", "leg": "original", "ticket": 0}),
    ("primary-barrier", "barrier", {"gateway": "a"}),
    ("fence-primary", "fence", {"gateway": "a"}),
    ("install-standby-delay", "qdisc", {"interface": "cbl", "delayMilliseconds": 1500}),
    ("admit-standby", "admit", {"gateway": "b", "leg": "original", "ticket": 3}),
    ("install-deny", "policy", {"gateway": "b", "policy": "deny"}),
    ("serve-standby", "serve", {"gateway": "b", "leg": "original", "ticket": 3}),
    ("standby-barrier", "barrier", {"gateway": "b"}),
    ("install-permit", "policy", {"gateway": "b", "policy": "permit-established"}),
    ("continued-request", "packet", {"gateway": "b", "leg": "original", "ticket": 4}),
    ("continued-reply", "packet", {"gateway": "b", "leg": "reply", "ticket": 5}),
)
MARKERS = {
    "establish": "establish",
    0: "held-primary",
    1: "overtake-request",
    2: "overtake-reply",
    3: "held-standby",
    4: "continued-request",
    5: "continued-reply",
}


def endpoint_table(count):
    return [
        {"table": {"family": "ip", "name": "handoff_admission"}},
        legacy.nat.chain("handoff_admission", "admission", "filter", "postrouting", 210),
        {
            "rule": {
                "family": "ip",
                "table": "handoff_admission",
                "chain": "admission",
                "expr": [
                    {"match": {"op": "==", "left": {"meta": {"key": "l4proto"}}, "right": "udp"}},
                    {"counter": {"packets": count[0], "bytes": count[1]}},
                    {
                        "log": {
                            "prefix": "ROUTE_ADMIT",
                            "group": 43,
                            "snaplen": 65531,
                            "queue-threshold": 1,
                        }
                    },
                ],
            }
        },
    ]


def check_queue(rows, mode, pending, sent, length):
    require(isinstance(rows, list) and len(rows) == 1, "Expected one isolated root queue.")
    row = rows[0]
    require(
        set(row)
        == {
            "kind",
            "handle",
            "root",
            "refcnt",
            "options",
            "bytes",
            "packets",
            "drops",
            "overlimits",
            "requeues",
            "backlog",
            "qlen",
        }
        and row["root"] is True
        and type(row["refcnt"]) is int
        and 0 < row["refcnt"] < 2**32,
        "Unsupported queue statistics envelope.",
    )
    for field in ("bytes", "packets", "drops", "overlimits", "requeues", "backlog", "qlen"):
        legacy.integer(row[field])
    require(
        row["drops"] == row["overlimits"] == row["requeues"] == 0,
        "Queue reports loss, overlimits, or requeues.",
    )
    if mode is None:
        require(
            row["kind"] == "noqueue"
            and row["handle"] == "0:"
            and row["options"] == {}
            and all(row[key] == 0 for key in ("bytes", "packets", "backlog", "qlen")),
            "Deleted queue is not an empty noqueue readback.",
        )
    else:
        handle, delay = mode
        options = row["options"]
        require(
            row["kind"] == "netem"
            and row["handle"] == handle
            and set(options) == {"limit", "delay", "seed", "ecn", "gap"}
            and type(options["limit"]) is int
            and options["limit"] == 16
            and options["ecn"] is False
            and type(options["gap"]) is int
            and options["gap"] == 0
            and options["delay"] == {"delay": delay, "jitter": 0, "correlation": 0}
            and all(type(value) in (int, float) for value in options["delay"].values()),
            "Queue is not the selected delay-only netem configuration.",
        )
        legacy.integer(options["seed"])
        require(
            (row["qlen"], row["backlog"], row["packets"], row["bytes"])
            == (int(pending), length if pending else 0, sent, sent * length),
            "Selected pending queue count, backlog, or completion counters disagree.",
        )


def check_network(boundary, owners, fenced, modes):
    for actor, documents in boundary["networks"].items():
        links = documents["links"]
        require(
            len(links) == len(legacy.LINKS[actor]) + 1
            and {row["ifname"] for row in links} == {"lo", *legacy.LINKS[actor]},
            "Unexpected namespace link inventory.",
        )
        for row in links:
            name = row["ifname"]
            fields = {
                "ifindex",
                "ifname",
                "flags",
                "mtu",
                "qdisc",
                "operstate",
                "linkmode",
                "group",
                "txqlen",
                "link_type",
                "address",
                "broadcast",
            }
            if name != "lo":
                fields |= {"link_index", "link_netnsid"}
            require(
                set(row) == fields
                and row["linkmode"] == "DEFAULT"
                and row["group"] == "default"
                and row["txqlen"] == 1000
                and row["broadcast"]
                == ("00:00:00:00:00:00" if name == "lo" else "ff:ff:ff:ff:ff:ff")
                and (name == "lo" or type(row["link_netnsid"]) is int and row["link_netnsid"] >= 0),
                "Unsupported native link attributes or queue envelope.",
            )
            if name == "lo":
                require(
                    row["flags"] == ["LOOPBACK", "UP", "LOWER_UP"]
                    and row["link_type"] == "loopback"
                    and row["mtu"] == 65536
                    and row["qdisc"] == "noqueue"
                    and row["operstate"] == "UNKNOWN"
                    and row["address"] == "00:00:00:00:00:00",
                    "Loopback is unavailable.",
                )
                continue
            down = fenced and actor == "a" and name in ("car", "sar")
            no_carrier = fenced and name in ("cal", "sal")
            flags = (
                ["BROADCAST", "MULTICAST"]
                if down
                else ["NO-CARRIER", "BROADCAST", "MULTICAST", "UP"]
                if no_carrier
                else ["BROADCAST", "MULTICAST", "UP", "LOWER_UP"]
            )
            qdisc = (
                "netem"
                if actor == "client" and name in modes and modes[name] is not None
                else "noqueue"
            )
            require(
                (row["mtu"], row["address"], row["link_type"], row["qdisc"])
                == (1500, legacy.LINKS[actor][name][1], "ether", qdisc)
                and row["flags"] == flags
                and row["operstate"] == ("DOWN" if down or no_carrier else "UP"),
                "Native link queue, MTU, MAC, type, or fence state disagrees.",
            )
        actual_addresses = set()
        require(
            len(documents["addresses"]) == len(links), "Incomplete address interface inventory."
        )
        for row in documents["addresses"]:
            require(row["ifname"] in {"lo", *legacy.LINKS[actor]}, "Unknown addressed interface.")
            link = next(value for value in links if value["ifname"] == row["ifname"])
            require(
                {key: value for key, value in row.items() if key != "addr_info"}
                == {key: value for key, value in link.items() if key != "linkmode"}
                and len(row["addr_info"]) == 1,
                "Native address interface attributes contradict the link readback.",
            )
            for value in row["addr_info"]:
                require(
                    set(value)
                    == {
                        "family",
                        "local",
                        "prefixlen",
                        "scope",
                        "label",
                        "valid_life_time",
                        "preferred_life_time",
                    }
                    and value["family"] == "inet"
                    and value["label"] == row["ifname"]
                    and value["scope"] == ("host" if row["ifname"] == "lo" else "global")
                    and value["valid_life_time"] == value["preferred_life_time"] == 2**32 - 1,
                    "Unsupported native address attributes or lifetime.",
                )
                actual_addresses.add((row["ifname"], value["local"], value["prefixlen"]))
        require(
            actual_addresses
            == {("lo", "127.0.0.1", 8)}
            | {(name, value[0], 24) for name, value in legacy.LINKS[actor].items()},
            "Namespace address inventory disagrees.",
        )
        routes = []
        for destination, device, gateway, preferred, kind in legacy.expected_routes(
            actor, owners, fenced=fenced
        ):
            row = {"dst": destination, "flags": []}
            if kind:
                row["type"] = kind
            else:
                row["dev"] = device
                if gateway:
                    row["gateway"] = gateway
                if preferred:
                    row["prefsrc"] = preferred
                if "/" in destination:
                    row.update(protocol="kernel", scope="link")
                    if fenced and device in ("cal", "sal"):
                        row["flags"] = ["linkdown"]
            routes.append(row)
        require(
            sorted(documents["routes"], key=lambda row: json.dumps(row, sort_keys=True))
            == sorted(routes, key=lambda row: json.dumps(row, sort_keys=True)),
            "Per-leg route owners, selectors, or blackhole readback disagree.",
        )
        require(
            documents["rules"]
            == [
                {"priority": 0, "src": "all", "table": "local"},
                {"priority": 32766, "src": "all", "table": "main"},
                {"priority": 32767, "src": "all", "table": "default"},
            ],
            "Unexpected policy routing rules.",
        )
        neighbors = []
        for name in legacy.LINKS[actor]:
            if fenced and actor == "a" and name in ("car", "sar"):
                continue
            peer = legacy.OPPOSITE[name]
            address, mac = legacy.LINKS[legacy.INTERFACES[peer]][peer]
            neighbors.append({"dst": address, "dev": name, "lladdr": mac, "state": ["PERMANENT"]})
        require(
            sorted(documents["neighbors"], key=lambda row: row["dev"])
            == sorted(neighbors, key=lambda row: row["dev"]),
            "Permanent neighbor isolation disagrees.",
        )


def check_capture(directory):
    directory = Path(directory)
    evidence = CaptureEvidence.open(directory, "safe-handoff")
    manifest = legacy.nat.read_json(directory / "capture.json")
    require(
        [(event["id"], event["type"]) for event in manifest["events"]]
        == [(name, kind) for name, kind, _ in EVENTS],
        "Unexpected ordered safe handoff event inventory.",
    )
    boundaries = {"initial": evidence.read_boundary("initial")}
    for event in manifest["events"]:
        for side in ("before", "after"):
            boundaries[event["id"] + ":" + side] = evidence.read_boundary(event["id"] + ":" + side)
    boundaries["final"] = evidence.read_boundary("final")
    packets = {ticket: evidence.bind_packet(ticket) for ticket in MARKERS}
    raw = evidence.finish()
    owners, fenced, policy = {"original": "a", "reply": "a"}, False, "initial"
    statuses, identities = {"a": None, "b": None}, {}
    gateway_counts = {actor: {} for actor in legacy.GATEWAYS}
    endpoint_counts = {actor: (0, 0) for actor in ("client", "server")}
    modes = {"cal": None, "cbl": None}
    queued, sent = {"cal": False, "cbl": False}, {"cal": 0, "cbl": 0}
    lengths = {
        "cal": packets[0]["admission"]["ipLength"] + 14,
        "cbl": packets[3]["admission"]["ipLength"] + 14,
    }
    pending, completed = {}, set()
    report_events = []

    def check_boundary(name):
        value = boundaries[name]
        for actor, rows in value["conntrack"].items():
            require(
                len(rows) == int(statuses[actor] is not None),
                "Actual kernel record presence contradicts event prefix.",
            )
            for row in rows:
                maximum = (
                    30
                    if actor == "a" or row["status"] == 442
                    else 120
                    if row["status"] == 446
                    else 180
                )
                require(
                    row["original"] == legacy.ORIGINAL
                    and row["reply"] == legacy.WIRE_REPLY
                    and row["originalZone"] == row["replyZone"] == 0
                    and row["status"] == statuses[actor]
                    and type(row["id"]) is int
                    and type(row["remainingTTL"]) is int
                    and 0 < row["remainingTTL"] <= maximum
                    and row["mark"] == 0,
                    "Actual protected tuple, NAT flags, reply status, zone, lifetime, or mark disagrees.",
                )
                require(
                    actor not in identities or identities[actor] == row["id"],
                    "Selected kernel record changed identity.",
                )
                identities[actor] = row["id"]
            require(
                legacy.nat.objects(value["tables"][actor])
                == legacy.expected_tables(
                    "initial" if actor == "a" else policy, gateway_counts[actor]
                ),
                "Full current gateway ruleset or counters disagree.",
            )
        for actor in endpoint_counts:
            require(
                legacy.nat.objects(value["endpointTables"][actor])
                == endpoint_table(endpoint_counts[actor]),
                "Endpoint route-admission hook or counters disagree.",
            )
        check_network(value, owners, fenced, modes)
        for interface in modes:
            check_queue(
                value["qdiscs"][interface],
                modes[interface],
                queued[interface],
                sent[interface],
                lengths[interface],
            )
        return value

    initial = check_boundary("initial")
    require(
        raw["cacheViews"]["initial"] == {"a": [], "b": []},
        "External caches were not initially empty.",
    )
    stage_cache = None
    for event, (name, kind, metadata) in zip(manifest["events"], EVENTS, strict=True):
        require(
            set(event)
            == {
                "id",
                "type",
                "startNs",
                "endNs",
                "before",
                "after",
                "result",
                "commands",
                "polls",
                *metadata,
            }
            and all(
                event[key] == value
                and (type(event[key]) is int if type(value) is int else isinstance(event[key], str))
                for key, value in metadata.items()
            ),
            "Native event gateway, leg, ticket, or control metadata disagrees.",
        )
        before = check_boundary(name + ":before")
        operation = before["operation"]
        row = {
            **{key: event[key] for key in ("id", "type", *metadata)},
            "before": before["conntrack"],
            "snapshots": {
                "before": {
                    actor: reference["file"]
                    for actor, reference in before["native"]["conntrack"].items()
                }
            },
            "native": event,
        }
        if kind in ("packet", "admit", "serve"):
            ticket = event.get("ticket", "establish")
            packet = packets[ticket]
            require(
                packet["admission"]["dataHex"]
                == ("safe-handoff:" + MARKERS[ticket]).encode().hex(),
                "Packet ticket marker is not the selected actual input.",
            )
            row["packet"] = packet
            if kind in ("packet", "admit"):
                require(
                    packet["gateway"] == owners[packet["leg"]]
                    and not (fenced and packet["gateway"] == "a"),
                    "Route admission selected a stale or fenced current owner.",
                )
                if ticket != "establish":
                    require(
                        statuses[packet["gateway"]] is not None and stage_cache is not None,
                        "Protected admission occurred before actual ready binding installation.",
                    )
                    require(
                        type(ticket) is int
                        and ticket not in pending
                        and ticket not in completed
                        and ticket == len(pending) + len(completed),
                        "Protected ticket allocation is not fresh and ordered.",
                    )
                    pending[ticket] = packet["gateway"]
                actor = "client" if packet["leg"] == "original" else "server"
                count, byte_count = endpoint_counts[actor]
                endpoint_counts[actor] = count + 1, byte_count + packet["admission"]["ipLength"]
                if kind == "admit":
                    interface = packet["admission"]["interface"]
                    require(
                        modes[interface] is not None
                        and not queued[interface]
                        and packet["admission"]["readEndNs"] < event["endNs"],
                        "Held ticket lacks a read admission and isolated pending queue.",
                    )
                    queued[interface] = True
            if kind in ("packet", "serve"):
                actor = packet["gateway"]
                if ticket != "establish":
                    require(
                        pending.get(ticket) == actor,
                        "Serve does not select the actual pending ticket's assigned gateway.",
                    )
                    del pending[ticket]
                    completed.add(ticket)
                require(
                    packet["disposition"]
                    == ("forwardDrop" if policy == "deny" and actor == "b" else "forwarded"),
                    "Actual service contradicts the assigned gateway's current policy.",
                )
                state = packet["classification"].upper()
                size = packet["admission"]["ipLength"]
                for key in (
                    "INGRESS",
                    "TRACKED",
                    state,
                    *(() if packet["outgoing"] is None else ("EGRESS",)),
                ):
                    count, byte_count = gateway_counts[actor].get(key, (0, 0))
                    gateway_counts[actor][key] = count + 1, byte_count + size
                if ticket == "establish":
                    statuses["a"] = 440
                elif ticket == 2:
                    statuses["b"] = 442
                elif ticket == 3:
                    statuses["b"] = 446
                if kind == "serve":
                    interface = packet["admission"]["interface"]
                    require(queued[interface], "Selected held ticket was not pending at service.")
                    queued[interface] = False
                    sent[interface] = 1
        elif kind == "stage":
            source = before["conntrack"]["a"][0]
            result = event["result"]
            require(
                event["commands"]
                == [reference["command"] for reference in result["attempts"]]
                + [result["internal"]["command"]],
                "Stage omits actual cache reads.",
            )
            for index, reference in enumerate(result["attempts"]):
                cache = legacy.decode_cache_xml(operation["exports"][reference["file"]])
                require(
                    cache
                    == (
                        [{"original": legacy.ORIGINAL, "unreplied": True, "assured": False}]
                        if index == len(result["attempts"]) - 1
                        else []
                    ),
                    "Actual external cache presence or status labels disagree.",
                )
            legacy.check_internal_cache(operation["exports"][result["internal"]["file"]], source)
            command = operation["commands"][-2]
            incoming = [
                data
                for data in raw["syncData"]
                if data["actor"] == "a"
                and data["packetType"] == 0
                and data["source"].startswith("b-")
                and data["timeNs"] < command["startNs"]
                and data["attributes"]["status"] == source["status"]
            ]
            require(
                incoming,
                "Cache stage lacks an actual incoming source record before the cache read.",
            )
            attrs = incoming[-1]["attributes"]
            stage_cache = [
                {
                    "original": attrs["original"],
                    "zone": attrs.get("zone", 0),
                    "sourceNAT": {"address": attrs["sourceNAT"], "port": attrs["sourceNATPort"]},
                    "destinationNAT": {
                        "address": attrs["destinationNAT"],
                        "port": attrs["destinationNATPort"],
                    },
                    "seenReply": bool(attrs["status"] & 2),
                }
            ]
            row.update(
                cache=stage_cache, cacheSource=result["external"]["file"], sourceSync=incoming
            )
        else:
            expected = control_commands(name)
            require(
                [command["arguments"] for command in operation["commands"]] == expected,
                "Native control command arguments contradict the named event.",
            )
            if kind == "barrier":
                interface, ticket, completion = (
                    ("cal", 0, "serve-primary")
                    if name == "primary-barrier"
                    else ("cbl", 3, "serve-standby")
                )
                result = event["result"]
                require(
                    set(result) == {"qdisc", "ticket", "completion", "deleteCommand"}
                    and result["ticket"] == ticket
                    and result["completion"] == completion
                    and result["deleteCommand"] == event["commands"][-1]
                    and ticket in completed
                    and ticket not in pending,
                    "Drain barrier does not bind actual selected ticket completion.",
                )
                check_queue(
                    operation["exports"][result["qdisc"]["file"]],
                    modes[interface],
                    False,
                    1,
                    lengths[interface],
                )
                modes[interface], sent[interface] = None, 0
            else:
                require(
                    event["result"]
                    == (event["commands"] if kind == "fence" else event["commands"][0]),
                    "Control result aliases a different actual command.",
                )
                if kind == "commit":
                    require(
                        stage_cache is not None and not before["conntrack"]["b"],
                        "Commit lacks a staged actual source or has a destination collision.",
                    )
                    statuses["b"] = 440
                elif kind == "qdisc":
                    interface = event["interface"]
                    require(
                        modes[interface] is None,
                        "Queue installation replaces selected pending work.",
                    )
                    modes[interface] = ("10:", 2.5) if interface == "cal" else ("20:", 1.5)
                elif kind == "handoff":
                    require(
                        statuses["b"] is not None,
                        "Endpoint handoff precedes actual standby readiness.",
                    )
                    owners[event["leg"]] = "b"
                elif kind == "fence":
                    require(
                        owners == {"original": "b", "reply": "b"}
                        and "a" not in pending.values()
                        and 0 in completed
                        and modes["cal"] is None,
                        "Fence precedes route ownership and selected primary ticket drain.",
                    )
                    fenced = True
                elif kind == "policy":
                    policy = "deny" if event["policy"] == "deny" else "permit"
        require(
            event["polls"]
            == ([event["result"]["admission"]["poll"]] if kind in ("packet", "admit") else []),
            "Native event poll inventory disagrees.",
        )
        after = check_boundary(name + ":after")
        row["after"] = after["conntrack"]
        row["snapshots"]["after"] = {
            actor: reference["file"] for actor, reference in after["native"]["conntrack"].items()
        }
        report_events.append(row)
    final = check_boundary("final")
    require(
        not pending and completed == set(range(6)) and fenced,
        "Final selected tickets or primary fence are incomplete.",
    )
    old = packets[0]
    require(
        old["admission"]["readEndNs"] < boundaries["client-route:before"]["operation"]["startNs"]
        and old["incoming"]["timeNs"] > packets[2]["receiver"]["response"]["endNs"]
        and old["incoming"]["timeNs"] > boundaries["server-route:before"]["operation"]["endNs"],
        "Selected old primary ticket does not actually outlive both handoffs and overtaking standby traffic.",
    )
    delayed = packets[3]
    require(
        delayed["admission"]["readEndNs"]
        < boundaries["install-deny:before"]["operation"]["startNs"]
        < delayed["incoming"]["timeNs"],
        "Held standby ticket does not span the actual current-policy change.",
    )
    require(
        raw["cacheViews"]["final"]
        == {
            "a": [{"original": legacy.ORIGINAL, "unreplied": False, "assured": True, "mark": 0}],
            "b": [{"original": legacy.ORIGINAL, "unreplied": True, "assured": False}],
        },
        "Final replicated caches disagree with actual gateway status updates.",
    )
    require(
        manifest["endNs"] - manifest["startNs"] < 30_000_000_000,
        "Capture exceeds selected finite lifetime scope.",
    )
    observations = [
        ("admit-primary:after", "cal"),
        ("client-route:after", "cal"),
        ("server-route:after", "cal"),
        ("overtake-reply:after", "cal"),
        ("serve-primary:after", "cal"),
        ("admit-standby:after", "cbl"),
        ("install-deny:after", "cbl"),
        ("serve-standby:after", "cbl"),
    ]
    return {
        **{
            key: raw[key]
            for key in (
                "schema",
                "profile",
                "packetCount",
                "snapshotCount",
                "frameCount",
                "nflogCount",
                "syncFrameCount",
            )
        },
        "initial": initial["conntrack"],
        "initialSnapshots": {
            actor: reference["file"] for actor, reference in initial["native"]["conntrack"].items()
        },
        "final": final["conntrack"],
        "events": report_events,
        "boundaries": boundaries,
        "queuePendingCounts": [
            boundaries[name]["qdiscs"][interface][0]["qlen"] for name, interface in observations
        ],
        "safeFence": {
            "completedPrimaryTicket": True,
            "completion": "serve-primary",
            "barrierSource": manifest["events"][10]["result"]["qdisc"]["file"],
            "fence": "fence-primary",
        },
    }


def control_commands(name):
    prefix = ["ip", "netns", "exec"]
    if name == "commit":
        return [prefix + ["b", "conntrackd", "-C", f"{SAFE_BASE}/b.conf", "-c"]]
    if name in ("install-primary-delay", "install-standby-delay"):
        interface, handle, delay = (
            ("cal", "10:", "2500ms")
            if name == "install-primary-delay"
            else ("cbl", "20:", "1500ms")
        )
        return [
            prefix
            + [
                "client",
                SAFE_TC,
                "qdisc",
                "add",
                "dev",
                interface,
                "root",
                "handle",
                handle,
                "netem",
                "limit",
                "16",
                "delay",
                delay,
            ]
        ]
    if name in ("client-route", "server-route"):
        return [
            prefix
            + (
                [
                    "client",
                    "ip",
                    "route",
                    "replace",
                    "203.0.113.2/32",
                    "via",
                    "192.0.3.1",
                    "dev",
                    "cbl",
                    "src",
                    "192.0.2.2",
                ]
                if name == "client-route"
                else [
                    "server",
                    "ip",
                    "route",
                    "replace",
                    "203.0.113.1/32",
                    "via",
                    "198.51.101.1",
                    "dev",
                    "sbl",
                    "src",
                    "198.51.100.2",
                ]
            )
        ]
    if name == "fence-primary":
        return [
            prefix + ["a", "ip", "link", "set", interface, "down"] for interface in ("car", "sar")
        ]
    if name in ("primary-barrier", "standby-barrier"):
        interface = "cal" if name == "primary-barrier" else "cbl"
        return [
            prefix + ["client", SAFE_TC, "-j", "-s", "-d", "qdisc", "show", "dev", interface],
            prefix + ["client", SAFE_TC, "qdisc", "del", "dev", interface, "root"],
        ]
    if name == "install-deny":
        return [prefix + ["b", "nft", "flush", "chain", "ip", "netlib", "forward"]]
    require(name == "install-permit", "Unknown control event.")
    return [
        prefix
        + [
            "b",
            "nft",
            "add",
            "rule",
            "ip",
            "netlib",
            "forward",
            "ct",
            "state",
            "established",
            "accept",
        ]
    ]


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "directory", nargs="?", type=Path, default=ROOT / "examples/safe-handoff/native"
    )
    parser.add_argument("--output", type=Path)
    args = parser.parse_args(argv)
    try:
        report = check_capture(args.directory)
    except (EvidenceError, ValueError, KeyError, TypeError, OSError, IndexError) as error:
        parser.exit(1, f"Safe handoff capture rejected: {error}\n")
    if args.output:
        args.output.write_text(json.dumps(report, indent=2) + "\n")
    print(
        f"Verified {report['packetCount']} inputs, {report['snapshotCount']} kernel dumps, and both selected queue barriers."
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
