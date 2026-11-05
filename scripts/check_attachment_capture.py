"""Check ingress-bound session attachments and same-tuple adversary observations."""

import argparse
import ipaddress
import json
import re
from pathlib import Path

import check_replication_capture as replication
from attachment_capture_evidence import (
    ARCHIVE,
    ATTACHMENT_TASK,
    AttachmentEvidence,
    accounting,
    countdown_compatible,
    resolve_iif,
)
from capture_evidence import SAFE_BASE, SAFE_TC, EvidenceError, require
from check_campus_capture import EVENTS as CAMPUS_EVENTS
from check_campus_capture import campus_control_commands, tables_match
from check_safe_handoff_capture import check_queue, control_commands, endpoint_table

ROOT = Path(__file__).resolve().parents[1]
EVENTS = (
    ("authenticate", "authentication"),
    ("credential", "credential"),
    ("install-primary-permit", "policy"),
    ("install-standby-permit", "policy"),
    ("unsafe-original", "attack"),
    ("reset-tracking", "reset"),
    ("start-replication", "replication-start"),
    ("install-primary-attachment", "guard"),
    ("install-standby-attachment", "guard"),
    ("protect-marker", "protect"),
    ("fresh-original-a", "attack"),
    ("fresh-original-b", "attack"),
    ("establish", "packet"),
    ("cached-original-a", "attack"),
    ("forged-reply-a", "attack"),
    ("replicate", "stage"),
    ("commit", "commit"),
    ("cached-original-b", "attack"),
    ("forged-reply-b", "attack"),
    ("install-primary-delay", "qdisc"),
    ("admit-primary", "admit"),
    ("client-route", "handoff"),
    ("server-route", "handoff"),
    ("overtake-request", "packet"),
    ("overtake-reply", "packet"),
    ("serve-primary", "serve"),
    ("primary-barrier", "barrier"),
    ("fence-primary", "fence"),
    ("withdraw-primary", "withdraw"),
    ("continued-request", "packet"),
    ("continued-reply", "packet"),
    ("install-original-delay", "qdisc"),
    ("install-reply-delay", "qdisc"),
    ("admit-stale-original", "admit"),
    ("admit-stale-reply", "admit"),
    ("logoff", "authentication"),
    ("install-standby-attachment-deny", "guard"),
    ("serve-stale-pair", "serve-pair"),
    ("original-barrier", "barrier"),
    ("reply-barrier", "barrier"),
    ("install-standby-deny", "policy"),
)


def canonical_guard_rule(rule, links):
    require(
        set(rule) <= {"family", "table", "chain", "handle", "comment", "expr"}
        and rule["family"] == "ip"
        and rule["table"] == "netlib_attachment"
        and rule["chain"] == "ingress",
        "Unexpected attachment guard rule envelope.",
    )
    expressions = rule["expr"]
    require(
        expressions and expressions[-1] in ({"accept": None}, {"drop": None}),
        "Attachment guard has no supported final verdict.",
    )
    require(
        rule.get("comment") in {"SYNC", "ORIGINAL", "REPLY", "FALLBACK"},
        "Attachment rule lost its selected controller role.",
    )
    result = {
        "role": rule["comment"],
        "verdict": "accept" if expressions[-1] == {"accept": None} else "drop",
    }
    fields = {}
    for expression in expressions[:-1]:
        if set(expression) == {"log"}:
            require("log" not in result, "Duplicate attachment log statement.")
            value = expression["log"]
            require(
                value
                == {
                    "prefix": "ATTACH_ALLOW" if result["verdict"] == "accept" else "ATTACH_DROP",
                    "group": 42,
                    "snaplen": 65531,
                    "queue-threshold": 1,
                },
                "Attachment decision log changed its raw evidence contract.",
            )
            result["log"] = value["prefix"]
            continue
        require(
            "log" not in result and set(expression) == {"match"},
            "Attachment guard predicate follows its decision log or uses unsupported effects.",
        )
        value = expression["match"]
        require(
            set(value) == {"op", "left", "right"} and value["op"] == "==",
            "Unsupported attachment predicate.",
        )
        left, right = value["left"], value["right"]
        if left == {"meta": {"key": "iif"}}:
            require("ifindex" not in result, "Duplicate attachment input-interface predicate.")
            result["ifindex"] = resolve_iif(expression, links)
            continue
        if left == {"meta": {"key": "l4proto"}}:
            require(
                "protocol" not in fields and type(right) is int and right == 17,
                "Attachment guard has a different or repeated transport protocol.",
            )
            fields["protocol"] = right
            continue
        require(
            set(left) == {"payload"} and set(left["payload"]) == {"protocol", "field"},
            "Attachment guard must match a numeric input interface and the complete pre-NAT tuple.",
        )
        protocol, field = left["payload"]["protocol"], left["payload"]["field"]
        if protocol == "ip" and field in ("saddr", "daddr"):
            if isinstance(right, dict):
                require(
                    set(right) == {"prefix"}
                    and set(right["prefix"]) == {"addr", "len"}
                    and type(right["prefix"]["len"]) is int
                    and right["prefix"]["len"] == 32,
                    "Attachment address predicate is not an exact host.",
                )
                right = right["prefix"]["addr"]
            require(isinstance(right, str), "Attachment address export is not a native string.")
            key, selected = (
                ("source" if field == "saddr" else "destination"),
                str(ipaddress.IPv4Address(right)),
            )
        else:
            require(
                protocol == "udp"
                and field in ("sport", "dport")
                and type(right) is int
                and 0 <= right < 65536,
                "Unsupported attachment transport selector.",
            )
            key, selected = ("sourcePort" if field == "sport" else "destinationPort"), right
        require(key not in fields, "Duplicate attachment tuple field.")
        fields[key] = selected
    if fields:
        require(
            set(fields)
            in (
                {"source", "destination", "sourcePort", "destinationPort"},
                {"source", "destination", "sourcePort", "destinationPort", "protocol"},
            )
            and "ifindex" in result
            and result["verdict"] == "accept",
            "Attachment allow rule omits a pre-NAT tuple field or input index.",
        )
        result["header"] = {**fields, "protocol": 17}
    else:
        require(
            result == {"role": "FALLBACK", "verdict": "drop", "log": "ATTACH_DROP"},
            "Attachment fallback must log and drop without an implicit bypass.",
        )
    return result


def canonical_guard(document, links, *, transaction=False, replace=False):
    rows = document["nftables"]
    require(
        isinstance(rows, list) and all(isinstance(row, dict) and len(row) == 1 for row in rows),
        "Malformed native attachment table.",
    )
    deleted = [row["delete"] for row in rows if "delete" in row]
    require(
        deleted == ([{"table": {"family": "ip", "name": "netlib_attachment"}}] if replace else [])
        and (not replace or transaction),
        "Attachment replacement omits or changes its explicit table deletion.",
    )
    meta = [row["metainfo"] for row in rows if "metainfo" in row]
    tables = [row["table"] for row in rows if "table" in row]
    chains = [row["chain"] for row in rows if "chain" in row]
    rules = [row["rule"] for row in rows if "rule" in row]
    if transaction:
        require(
            all(
                type(expression["match"]["right"]) is int
                for rule in rules
                for expression in rule["expr"]
                if expression.get("match", {}).get("left") == {"meta": {"key": "iif"}}
            ),
            "Actual guard installation must use captured numeric input indices.",
        )
    require(
        len(rows) == len(meta) + len(tables) + len(chains) + len(rules) + len(deleted)
        and len(meta) == len(tables) == len(chains) == 1
        and (
            meta[0] == {"json_schema_version": 1}
            if transaction
            else meta[0].get("version") == "1.1.3"
        )
        and type(meta[0]["json_schema_version"]) is int
        and meta[0]["json_schema_version"] == 1,
        "Unexpected extra attachment objects or producer version.",
    )
    require(
        {key: value for key, value in tables[0].items() if key != "handle"}
        == {"family": "ip", "name": "netlib_attachment"},
        "Unexpected attachment table identity.",
    )
    require(
        {key: value for key, value in chains[0].items() if key != "handle"}
        == {
            "family": "ip",
            "table": "netlib_attachment",
            "name": "ingress",
            "type": "filter",
            "hook": "prerouting",
            "prio": -300,
            "policy": "drop",
        },
        "Attachment guard does not precede ordinary conntrack or deny by default.",
    )
    return [canonical_guard_rule(rule, links) for rule in rules]


def expected_guard(actor, links, allow, peer_source_port):
    require(
        type(peer_source_port) is int and 0 < peer_source_port < 65536,
        "Maintenance guard lacks the actual peer daemon socket source port.",
    )
    maintenance = {
        "source": "10.10.0.2" if actor == "a" else "10.10.0.1",
        "destination": "10.10.0.1" if actor == "a" else "10.10.0.2",
        "protocol": 17,
        "sourcePort": peer_source_port,
        "destinationPort": 3780,
    }
    index = {row["ifname"]: row["ifindex"] for row in links}
    result = [
        {
            "role": "SYNC",
            "verdict": "accept",
            "ifindex": index["syncl" if actor == "a" else "syncr"],
            "header": maintenance,
        }
    ]
    if allow:
        for role, name, header in (
            ("ORIGINAL", "car" if actor == "a" else "cbr", replication.ORIGINAL),
            ("REPLY", "sar" if actor == "a" else "sbr", replication.WIRE_REPLY),
        ):
            result.append(
                {
                    "role": role,
                    "verdict": "accept",
                    "log": "ATTACH_ALLOW",
                    "ifindex": index[name],
                    "header": header,
                }
            )
    return result + [{"role": "FALLBACK", "verdict": "drop", "log": "ATTACH_DROP"}]


MARKERS = {
    "establish": "establish",
    0: "held-primary",
    1: "overtake-request",
    2: "overtake-reply",
    3: "continued-request",
    4: "continued-reply",
    5: "stale-original",
    6: "stale-reply",
}
METADATA = {name: values for name, _, values in CAMPUS_EVENTS if name in dict(EVENTS)}
METADATA.update(
    {
        "unsafe-original": {"gateway": "a", "leg": "original", "securityPhase": "unsafe"},
        "reset-tracking": {},
        "start-replication": {},
        "protect-marker": {},
        "install-primary-attachment": {"gateway": "a", "active": True},
        "install-standby-attachment": {"gateway": "b", "active": True},
        "install-standby-attachment-deny": {"gateway": "b", "active": False},
        "install-original-delay": {
            "actor": "client",
            "interface": "cbl",
            "delayMilliseconds": 2500,
        },
        "install-reply-delay": {"actor": "server", "interface": "sbl", "delayMilliseconds": 2500},
        "admit-stale-original": {"gateway": "b", "leg": "original", "ticket": 5},
        "admit-stale-reply": {"gateway": "b", "leg": "reply", "ticket": 6},
        "serve-stale-pair": {"gateway": "b", "tickets": [5, 6]},
        "original-barrier": {"gateway": "b"},
        "reply-barrier": {"gateway": "b"},
    }
)
for _name, _gateway, _leg in (
    ("fresh-original-a", "a", "original"),
    ("fresh-original-b", "b", "original"),
    ("cached-original-a", "a", "original"),
    ("forged-reply-a", "a", "reply"),
    ("cached-original-b", "b", "original"),
    ("forged-reply-b", "b", "reply"),
):
    METADATA[_name] = {"gateway": _gateway, "leg": _leg, "securityPhase": "guarded"}


def table_view(document, selected):
    return {
        "nftables": [
            row
            for row in document["nftables"]
            if "metainfo" in row
            or selected(
                next(iter(row.values())).get("name")
                if "table" in row
                else next(iter(row.values())).get("table")
            )
        ]
    }


def unchanged_tracking(before, after, evidence):
    require(
        set(before["conntrack"]) == set(after["conntrack"]),
        "Isolated drop changed live gateway inventory.",
    )
    for actor, rows in before["conntrack"].items():
        following = after["conntrack"][actor]
        require(len(rows) == len(following), "Early drop created or destroyed a native connection.")
        for earlier, later in zip(rows, following, strict=True):
            require(
                {
                    key: value
                    for key, value in earlier.items()
                    if key not in ("raw", "remainingTTL", "use")
                }
                == {
                    key: value
                    for key, value in later.items()
                    if key not in ("raw", "remainingTTL", "use")
                }
                and accounting(earlier["raw"]) == accounting(later["raw"]),
                "Early drop changed conntrack identity, tuple, NAT/status/mark/zone, or accounting.",
            )
            countdown_compatible(
                earlier["remainingTTL"],
                later["remainingTTL"],
                evidence.commands[before["native"]["conntrack"][actor]["command"]],
                evidence.commands[after["native"]["conntrack"][actor]["command"]],
            )


def attachment_control_commands(name, event):
    if name == "credential":
        return [
            [
                "install",
                "-m",
                "0644",
                "/task/attachments/input/demo-credential.json",
                "/run/netlib-attachments/demo-credential.json",
            ],
            ["cat", "/run/netlib-attachments/demo-credential.json"],
        ]
    if name == "withdraw-primary":
        values = campus_control_commands(name, event)
        values.insert(8, ["ip", "netns", "exec", "a", "ip", "link", "set", "aar", "down"])
        values[-1] = ["ip", "netns", "exec", "a", "python3", ATTACHMENT_TASK, "daemon-stopped"]
        return values
    if event["type"] in ("authentication", "policy"):
        return campus_control_commands(name, event)
    if name in ("install-original-delay", "install-reply-delay"):
        actor, interface, handle = (
            ("client", "cbl", "20:")
            if name == "install-original-delay"
            else ("server", "sbl", "30:")
        )
        return [
            [
                "ip",
                "netns",
                "exec",
                actor,
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
                "2500ms",
            ]
        ]
    if name in ("original-barrier", "reply-barrier"):
        actor, interface = ("client", "cbl") if name == "original-barrier" else ("server", "sbl")
        return [
            [
                "ip",
                "netns",
                "exec",
                actor,
                SAFE_TC,
                "-j",
                "-s",
                "-d",
                "qdisc",
                "show",
                "dev",
                interface,
            ],
            ["ip", "netns", "exec", actor, SAFE_TC, "qdisc", "del", "dev", interface, "root"],
        ]
    return control_commands(name)


def check_capture(directory, *, input_directory=ROOT / "examples/attachments"):
    from attachment_network_evidence import check_network

    directory, input_directory = Path(directory), Path(input_directory)
    evidence = AttachmentEvidence(directory)
    manifest = evidence.manifest
    for name in ("requirements.json", "demo-credential.json", "deny.json", "permit.json"):
        require(
            (directory / "input" / name).read_bytes() == (input_directory / name).read_bytes(),
            "Retained inputs differ from the reviewed intent, credential, or policy.",
        )
    require(
        isinstance(manifest["captureID"], str)
        and re.fullmatch(
            r"[0-9a-f]{8}-[0-9a-f]{4}-4[0-9a-f]{3}-[89ab][0-9a-f]{3}-[0-9a-f]{12}",
            manifest["captureID"],
        ),
        "Missing producer execution identity.",
    )
    require(
        [(row["id"], row["type"]) for row in manifest["events"]] == list(EVENTS),
        "Unexpected ordered attachment event inventory.",
    )
    boundaries = {"initial": evidence.boundary("initial")}
    for event in manifest["events"]:
        for side in ("before", "after"):
            key = event["id"] + ":" + side
            boundaries[key] = evidence.boundary(key)
    boundaries["final"] = evidence.boundary("final")
    packets = {ticket: evidence.packet(ticket, None) for ticket in MARKERS}
    attacks = {name: evidence.bind_attack(name) for name in evidence.attacks}
    raw = evidence.finish()
    owners = {"original": "a", "reply": "a"}
    policy, guard = {"a": "deny", "b": "deny"}, {"a": None, "b": None}
    statuses, identities = {"a": None, "b": None}, {}
    totals = {
        actor: {leg: {"packets": 0, "bytes": 0} for leg in ("original", "reply")}
        for actor in ("a", "b")
    }
    gateway_counts, endpoint_counts = {"a": {}, "b": {}}, {"client": (0, 0), "server": (0, 0)}
    modes, queued, sent = (
        dict.fromkeys(("cal", "cbl", "sbl")),
        dict.fromkeys(("cal", "cbl", "sbl"), False),
        dict.fromkeys(("cal", "cbl", "sbl"), 0),
    )
    lengths = {
        interface: packets[ticket]["admission"]["ipLength"] + 14
        for interface, ticket in (("cal", 0), ("cbl", 5), ("sbl", 6))
    }
    authenticated = credential = reset = started = protected = fenced = withdrawn = False
    pending, completed, report_events, guard_bindings = {}, set(), [], {}
    stage_cache = None

    def check_boundary(name):
        value = boundaries[name]
        for actor, rows in value["conntrack"].items():
            require(
                len(rows) == int(statuses[actor] is not None),
                f"Kernel record presence contradicts event prefix at {name}/{actor}.",
            )
            for row in rows:
                require(
                    row["original"] == replication.ORIGINAL
                    and row["reply"] == replication.WIRE_REPLY
                    and row["originalZone"] == row["replyZone"] == 0
                    and row["status"] == statuses[actor]
                    and type(row["id"]) is int
                    and type(row["remainingTTL"]) is int
                    and 0
                    < row["remainingTTL"]
                    <= (
                        30
                        if actor == "a" or row["status"] == 442
                        else 120
                        if row["status"] == 446
                        else 180
                    )
                    and row["mark"] == 0,
                    "Native tuple, NAT/status, zone, mark, or lifetime contradicts actual service history.",
                )
                require(
                    actor not in identities or identities[actor] == row["id"],
                    "Kernel connection identity changed inside one tracked epoch.",
                )
                identities[actor] = row["id"]
                require(
                    accounting(row["raw"]) == totals[actor],
                    "Native full-table accounting differs from actual accepted service history.",
                )
            current = value["tables"][actor]
            require(
                tables_match(
                    table_view(current, lambda table: table != "netlib_attachment"),
                    policy[actor],
                    gateway_counts[actor],
                    input_directory,
                ),
                f"Current complete ordinary ruleset/counters disagree at {name}/{actor}.",
            )
            selected = table_view(current, lambda table: table == "netlib_attachment")
            if guard[actor] is None:
                require(
                    len(selected["nftables"]) == 1, "A guard exists before its actual installation."
                )
            else:
                peer = "b" if actor == "a" else "a"
                require(
                    canonical_guard(selected, value["networks"][actor]["links"])
                    == expected_guard(
                        actor,
                        value["networks"][actor]["links"],
                        guard[actor],
                        evidence.maintenance[peer]["sourcePort"],
                    ),
                    "Installed guard differs from its explicit numeric attachment transaction.",
                )
        for actor, counts in endpoint_counts.items():
            require(
                replication.nat.objects(value["endpointTables"][actor]) == endpoint_table(counts),
                "Endpoint admission table/counters differ.",
            )
        check_network(value, owners, fenced, modes, withdrawn, evidence.auth_link)
        for interface in modes:
            check_queue(
                value["qdiscs"][interface],
                modes[interface],
                queued[interface],
                sent[interface],
                lengths[interface],
            )
        return value

    def record_service(packet, *, unsafe=False):
        actor, leg = packet["gateway"], packet["leg"]
        interface = (
            ("car" if actor == "a" else "cbr")
            if leg == "original"
            else ("sar" if actor == "a" else "sbr")
        )
        admitted = unsafe or (
            guard[actor] is True and packet["ingress"] == evidence.interface_refs[actor][interface]
        )
        require(
            packet["guardAdmitted"] == admitted
            and packet["disposition"] == ("forwarded" if admitted else "ingressDrop"),
            "Actual packet contradicts its current installed ingress guard.",
        )
        size = packet["incoming"]["ipLength"]
        keys = ["INGRESS"]
        if admitted:
            require(policy[actor] == "permit", "Accepted data lacks current ordinary permit.")
            expected_state = (
                "new"
                if statuses[actor] is None or (leg == "original" and not statuses[actor] & 2)
                else "established"
            )
            require(
                packet["classification"] == expected_state
                and packet["fresh"] == (statuses[actor] is None),
                "Native conntrack classification/freshness differs from actual table prefix.",
            )
            keys.extend(("TRACKED", expected_state.upper(), "EGRESS"))
            if statuses[actor] is None:
                statuses[actor] = 440
            elif leg == "reply":
                statuses[actor] |= 2
            elif statuses[actor] & 2:
                statuses[actor] |= 4
            totals[actor][leg]["packets"] += 1
            totals[actor][leg]["bytes"] += size
        else:
            require(
                packet["classification"] is None and packet["fresh"] is None,
                "Early drop invents a conntrack lookup/classification.",
            )
        for key in keys:
            count, byte_count = gateway_counts[actor].get(key, (0, 0))
            gateway_counts[actor][key] = count + 1, byte_count + size

    initial = check_boundary("initial")
    for event in manifest["events"]:
        name, kind = event["id"], event["type"]
        metadata = METADATA[name]
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
                event[key] == value and type(event[key]) is type(value)
                for key, value in metadata.items()
            ),
            "Event gateway, leg, ticket, phase, or operation metadata differs.",
        )
        before = check_boundary(name + ":before")
        operation, result = before["operation"], event["result"]
        row = {
            "id": name,
            "type": kind,
            **metadata,
            "before": before["conntrack"],
            "native": event,
            "snapshots": {
                "before": {
                    actor: ref["file"] for actor, ref in before["native"]["conntrack"].items()
                }
            },
        }
        if kind in ("packet", "admit", "serve", "serve-pair"):
            require(protected, "Legitimate protected data precedes actual guard readiness.")
            selected = (
                [packets[ticket] for ticket in result.get("tickets", event.get("tickets", []))]
                if kind == "serve-pair"
                else [packets[event.get("ticket", "establish")]]
            )
            if kind == "serve-pair":
                ingress_logs = {log["source"]: log for log in evidence.logs[event["gateway"]]}
                selected.sort(
                    key=lambda packet: ingress_logs[packet["ingressSource"]]["localSequence"]
                )
                row["serviceOrder"] = [packet["ticket"] for packet in selected]
                row["serviceSources"] = [packet["ingressSource"] for packet in selected]
            for packet in selected:
                ticket = packet["ticket"]
                require(
                    packet["admission"]["dataHex"]
                    == ("attachments:" + MARKERS[ticket]).encode().hex(),
                    "Selected legitimate marker differs from actual input.",
                )
                if kind in ("packet", "admit"):
                    require(
                        packet["gateway"] == owners[packet["leg"]]
                        and not (fenced and packet["gateway"] == "a"),
                        "Admission used a stale/fenced route owner.",
                    )
                    if ticket != "establish":
                        require(
                            stage_cache is not None
                            and statuses[packet["gateway"]] is not None
                            and ticket == len(pending) + len(completed)
                            and ticket not in pending
                            and ticket not in completed,
                            "Ticket admission precedes ready binding or reuses an old allocation.",
                        )
                        pending[ticket] = packet["gateway"]
                    actor = "client" if packet["leg"] == "original" else "server"
                    count, size = endpoint_counts[actor]
                    endpoint_counts[actor] = count + 1, size + packet["admission"]["ipLength"]
                    if kind == "admit":
                        interface = packet["admission"]["interface"]
                        require(
                            modes[interface] is not None and not queued[interface],
                            "Held ticket lacks its isolated installed queue.",
                        )
                        queued[interface] = True
                if kind != "admit":
                    if ticket != "establish":
                        require(
                            pending.pop(ticket, None) == packet["gateway"],
                            "Service does not consume its original assigned gateway/ticket.",
                        )
                        completed.add(ticket)
                    record_service(packet)
                    if kind in ("serve", "serve-pair"):
                        interface = packet["admission"]["interface"]
                        require(queued[interface], "Held service has no pending queue admission.")
                        queued[interface], sent[interface] = False, 1
            row["packets" if kind == "serve-pair" else "packet"] = (
                selected if kind == "serve-pair" else selected[0]
            )
        elif kind == "attack":
            attack = attacks[name]
            require(
                bytes.fromhex(attack["incoming"]["payloadHex"]) == ("attachments:" + name).encode(),
                "Attack marker differs from its actual raw input.",
            )
            require(
                authenticated
                and credential
                and (not protected if name == "unsafe-original" else protected),
                "Adversary history lacks its actual session/phase.",
            )
            require(
                attack["ingress"]
                != evidence.interface_refs[event["gateway"]][
                    ("car" if event["gateway"] == "a" else "cbr")
                    if event["leg"] == "original"
                    else ("sar" if event["gateway"] == "a" else "sbr")
                ],
                "Adversary used the attached legitimate input instance.",
            )
            record_service(attack, unsafe=name == "unsafe-original")
            row["attack"] = attack
        elif kind == "reset":
            require(
                not reset and not started and statuses == {"a": 440, "b": None},
                "Reset does not close exactly the unsafe counterexample epoch.",
            )
            require(
                event["commands"]
                == [result["commands"][actor] for actor in ("a", "b")]
                + [result["tables"][actor]["command"] for actor in ("a", "b")],
                "Reset journal omits flush/full-table readbacks.",
            )
            require(
                [command["arguments"] for command in operation["commands"][:2]]
                == [["ip", "netns", "exec", actor, "conntrack", "-F"] for actor in ("a", "b")]
                and all(
                    operation["exports"][ref["file"]] == [] for ref in result["tables"].values()
                ),
                "Explicit native reset did not empty both full tables.",
            )
            statuses, identities = {"a": None, "b": None}, {}
            totals = {
                actor: {leg: {"packets": 0, "bytes": 0} for leg in ("original", "reply")}
                for actor in ("a", "b")
            }
            reset = True
        elif kind == "replication-start":
            require(
                reset
                and not started
                and statuses == {"a": None, "b": None}
                and set(result)
                == {
                    "daemons",
                    "resynchronization",
                    "socketAttempts",
                    "socketReadiness",
                    "cacheReadiness",
                },
                "Daemon startup does not begin a fresh reset epoch.",
            )
            expected = []
            for actor in ("a", "b"):
                expected += [
                    [
                        "ip",
                        "netns",
                        "exec",
                        actor,
                        "conntrackd",
                        "-C",
                        f"{SAFE_BASE}/{actor}.conf",
                        "-d",
                    ],
                    [
                        "ip",
                        "netns",
                        "exec",
                        actor,
                        "conntrackd",
                        "-C",
                        f"{SAFE_BASE}/{actor}.conf",
                        "-s",
                        "runtime",
                    ],
                ]
            expected += [
                [
                    "ip",
                    "netns",
                    "exec",
                    actor,
                    "conntrackd",
                    "-C",
                    f"{SAFE_BASE}/{actor}.conf",
                    "-n",
                ]
                for actor in ("a", "b")
            ]
            require(
                [command["arguments"] for command in operation["commands"][:6]] == expected
                and [result["daemons"][actor]["startCommand"] for actor in ("a", "b")]
                == [event["commands"][0], event["commands"][2]]
                and list(result["resynchronization"].values()) == event["commands"][4:6],
                "Daemon startup/resynchronization journal differs.",
            )
            attempts = result["socketAttempts"]
            require(
                len(attempts["a"]) == len(attempts["b"]) and 0 < len(attempts["a"]) <= 40,
                "Daemon socket polling omits a peer or exceeds its bounded actual loop.",
            )
            indices = (
                event["commands"][:6]
                + [
                    attempts[actor][index]["command"]
                    for index in range(len(attempts["a"]))
                    for actor in ("a", "b")
                ]
                + [
                    result["cacheReadiness"][actor][kind]["command"]
                    for actor in ("a", "b")
                    for kind in ("internal", "external")
                ]
            )
            require(
                event["commands"] == indices,
                "Startup journal contains an unmodeled mutation or skips a readiness receipt.",
            )
            started = True
        elif kind == "guard":
            actor, active = event["gateway"], event["active"]
            require(
                event["commands"]
                == [result["binding"]["sources"][kind]["command"] for kind in ("links", "identity")]
                + [result["command"]],
                "Guard journal contains an unmodeled mutation or omits its native sources.",
            )
            require(
                started
                and not (withdrawn and actor == "a")
                and active == (authenticated and credential),
                "Guard installation uses a stale EAP prefix or retired gateway.",
            )
            binding = operation["exports"][result["binding"]["file"]]
            peer = "b" if actor == "a" else "a"
            links = operation["exports"][result["binding"]["sources"]["links"]["file"]]
            identity = operation["exports"][result["binding"]["sources"]["identity"]["file"]]
            require(
                links == before["networks"][actor]["links"]
                and identity["interfaces"] == evidence.birth_identities[actor]["interfaces"],
                "Guard sources contradict the contemporaneous native link or interface lifetime.",
            )
            expected_roles = [
                {
                    "role": role,
                    "interface": interface,
                    "ifindex": evidence.interface_refs[actor][interface]["ifindex"],
                }
                for role, interface in (
                    ("original", "car" if actor == "a" else "cbr"),
                    ("reply", "sar" if actor == "a" else "sbr"),
                    ("maintenance", "syncl" if actor == "a" else "syncr"),
                )
            ]
            require(
                binding
                == {
                    "gateway": actor,
                    "namespace": f"net:[{evidence.namespace_refs[actor]['id']}]",
                    "scope": {"resource": "campus-application", "operation": "use"},
                    "principal": raw["credential"]["subject"],
                    "authenticationEvent": "authenticate",
                    "credentialEvent": "credential",
                    "authenticationPort": {
                        "namespace": "auth",
                        "interface": "auth0",
                        "source": manifest["namespaceLifetimes"]["auth"]["identity"],
                    },
                    "currentAuthenticationEvent": "credential" if active else "logoff",
                    "active": active,
                    "maintenanceSource": {
                        "gateway": peer,
                        "sourcePort": evidence.maintenance[peer]["sourcePort"],
                        "socketInode": evidence.maintenance[peer]["socketInode"],
                        "source": manifest["events"][6]["result"]["socketReadiness"][peer],
                    },
                    "roles": expected_roles,
                    "sources": result["binding"]["sources"],
                },
                "Controller binding is not the current subject/round/scope, exact namespace/interface lifetime, and real peer socket.",
            )
            require(
                canonical_guard(
                    operation["exports"][result["file"]],
                    links,
                    transaction=True,
                    replace=guard[actor] is not None,
                )
                == expected_guard(actor, links, active, evidence.maintenance[peer]["sourcePort"]),
                "Actual numeric guard input differs from current controller binding.",
            )
            guard[actor] = active
            guard_bindings[name] = binding
            row["guard"] = {
                "active": active,
                "binding": binding,
                "authenticationPort": evidence.interface_refs["auth"]["auth0"],
                "dataPorts": {
                    role["role"]: evidence.interface_refs[actor][role["interface"]]
                    for role in expected_roles
                },
            }
        elif kind == "protect":
            require(
                event["commands"]
                == [
                    result["cacheReadiness"][actor][kind]["command"]
                    for actor in ("a", "b")
                    for kind in ("internal", "external")
                ],
                "Protected marker journal contains an unmodeled mutation or skips actual readiness.",
            )
            require(
                reset
                and started
                and not protected
                and guard == {"a": True, "b": True}
                and statuses == {"a": None, "b": None}
                and set(result)
                == {"initialBoundary", "guardInstallations", "bindings", "cacheReadiness"}
                and result["initialBoundary"] == "protect-marker:before"
                and result["guardInstallations"]
                == {"a": "install-primary-attachment", "b": "install-standby-attachment"}
                and result["bindings"]
                == {
                    actor: evidence.events[result["guardInstallations"][actor]]["result"][
                        "binding"
                    ]["file"]
                    for actor in ("a", "b")
                },
                "Protected suffix lacks actual current guards, live attachments, or empty reset state.",
            )
            protected = True
        elif kind == "stage":
            source = before["conntrack"]["a"][0]
            require(
                protected
                and stage_cache is None
                and event["commands"]
                == [ref["command"] for ref in result["attempts"]] + [result["internal"]["command"]],
                "Stage omits actual cache reads or repeats old state.",
            )
            for index, ref in enumerate(result["attempts"]):
                require(
                    replication.decode_cache_xml(operation["exports"][ref["file"]])
                    == (
                        [{"original": replication.ORIGINAL, "unreplied": True, "assured": False}]
                        if index == len(result["attempts"]) - 1
                        else []
                    ),
                    "External cache poll contradicts real unreplied source state.",
                )
            replication.check_internal_cache(
                operation["exports"][result["internal"]["file"]], source
            )
            incoming = [
                data
                for data in raw["syncData"]
                if data["actor"] == "a"
                and data["packetType"] == 0
                and data["source"].startswith("b-")
                and data["timeNs"] < operation["commands"][-2]["startNs"]
                and data["attributes"]["status"] == source["status"]
            ]
            require(incoming, "Cache stage lacks actual guarded source synchronization data.")
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
            require(
                [command["arguments"] for command in operation["commands"]]
                == attachment_control_commands(name, event),
                "Control command arguments contradict their declared operation.",
            )
            if kind == "authentication":
                if name == "authenticate":
                    require(not authenticated and not credential, "Authentication episode repeats.")
                    authenticated = True
                else:
                    require(
                        authenticated
                        and credential
                        and result["command"] == event["commands"][0]
                        and operation["commands"][0]["stdout"] == "OK\n",
                        "Actual Logoff does not close the current session.",
                    )
                    authenticated = False
            elif kind == "credential":
                require(
                    authenticated
                    and not credential
                    and result["command"] == event["commands"][0]
                    and result["input"] == "input/demo-credential.json"
                    and raw["credential"]
                    == replication.nat.read_json(input_directory / "demo-credential.json"),
                    "Credential is not a single installation for this actual authenticated session.",
                )
                credential = True
            elif kind == "policy":
                require(
                    not (withdrawn and event["gateway"] == "a")
                    and event["policy"] == ("permit" if authenticated and credential else "deny"),
                    "Ordinary policy uses stale authentication or retired gateway.",
                )
                policy[event["gateway"]] = event["policy"]
            elif kind == "commit":
                require(
                    stage_cache is not None
                    and not before["conntrack"]["b"]
                    and result == event["commands"][0],
                    "Commit lacks actual staged source or has a destination collision.",
                )
                statuses["b"] = 440
            elif kind == "qdisc":
                interface = event["interface"]
                require(
                    modes[interface] is None and result == event["commands"][0],
                    "Queue installation replaces selected work or aliases another command.",
                )
                modes[interface] = ({"cal": "10:", "cbl": "20:", "sbl": "30:"}[interface], 2.5)
            elif kind == "handoff":
                require(
                    statuses["b"] is not None and result == event["commands"][0],
                    "Handoff precedes actual standby readiness.",
                )
                owners[event["leg"]] = "b"
            elif kind == "barrier":
                interface, ticket, completion = (
                    ("cal", 0, "serve-primary")
                    if name == "primary-barrier"
                    else ("cbl", 5, "serve-stale-pair")
                    if name == "original-barrier"
                    else ("sbl", 6, "serve-stale-pair")
                )
                require(
                    set(result) == {"qdisc", "ticket", "completion", "deleteCommand"}
                    and result["ticket"] == ticket
                    and result["completion"] == completion
                    and result["deleteCommand"] == event["commands"][-1]
                    and ticket in completed
                    and ticket not in pending,
                    "Drain barrier does not bind actual completion of its selected ticket.",
                )
                check_queue(
                    operation["exports"][result["qdisc"]["file"]],
                    modes[interface],
                    False,
                    1,
                    lengths[interface],
                )
                modes[interface], sent[interface] = None, 0
            elif kind == "fence":
                require(
                    result == event["commands"]
                    and owners == {"original": "b", "reply": "b"}
                    and "a" not in pending.values()
                    and 0 in completed
                    and modes["cal"] is None,
                    "Fence precedes actual primary drain or route ownership.",
                )
                fenced = True
            elif kind == "withdraw":
                require(
                    fenced
                    and owners == {"original": "b", "reply": "b"}
                    and "a" not in pending.values()
                    and 0 in completed
                    and modes["cal"] is None
                    and set(result)
                    == {
                        "archiveBoundary",
                        "retiredAtNs",
                        "cache",
                        "statistics",
                        "standbyLogBefore",
                        "commands",
                        "checks",
                    }
                    and result["archiveBoundary"] == ARCHIVE
                    and result["retiredAtNs"] == operation["commands"][-1]["endNs"]
                    and result["commands"] == event["commands"][6:10]
                    and set(result["checks"]) == {"links", "forwarding", "daemon"},
                    "Withdrawal lacks a completed drain/fence or actual final verification receipt.",
                )
                checks = {
                    key: operation["exports"][ref["file"]] for key, ref in result["checks"].items()
                }
                archived_links = {link["ifname"]: link for link in before["networks"]["a"]["links"]}
                require(
                    {link["ifname"]: link for link in checks["links"]}
                    == {
                        name: link
                        if name == "lo"
                        else {**link, "flags": ["BROADCAST", "MULTICAST"], "operstate": "DOWN"}
                        for name, link in archived_links.items()
                    }
                    and checks["forwarding"] == "net.ipv4.ip_forward = 0\n"
                    and set(checks["daemon"])
                    == {"startNs", "endNs", "namespace", "matchingProcesses"}
                    and checks["daemon"]["matchingProcesses"] == []
                    and checks["daemon"]["namespace"]
                    == f"net:[{evidence.namespace_refs['a']['id']}]",
                    "Actual withdrawal leaves an A link, forwarding, or daemon live.",
                )
                command = evidence.commands[result["checks"]["daemon"]["command"]]
                replication.interval(checks["daemon"], command["startNs"], command["endNs"])
                require(
                    all(
                        command["arguments"][:4] != ["ip", "netns", "exec", "a"]
                        for command in evidence.commands
                        if command["startNs"] > result["retiredAtNs"]
                    ),
                    "Live A command follows actual retirement.",
                )
                withdrawn = True
            else:
                raise EvidenceError("Unknown attachment operation.")
        require(
            event["polls"]
            == ([result["admission"]["poll"]] if kind in ("packet", "admit") else []),
            "Event poll inventory differs from actual route admission.",
        )
        after = check_boundary(name + ":after")
        if (kind == "attack" and name != "unsafe-original") or kind == "serve-pair":
            unchanged_tracking(before, after, evidence)
        row["after"] = after["conntrack"]
        row["snapshots"]["after"] = {
            actor: ref["file"] for actor, ref in after["native"]["conntrack"].items()
        }
        report_events.append(row)
    final = check_boundary("final")
    require(
        not pending
        and completed == set(range(7))
        and fenced
        and withdrawn
        and protected
        and not authenticated
        and credential
        and guard == {"a": True, "b": False},
        "Final selected tickets, explicit guard invalidation, or primary withdrawal are incomplete.",
    )
    old = packets[0]
    require(
        old["admission"]["readEndNs"] < boundaries["client-route:before"]["operation"]["startNs"]
        and old["incoming"]["timeNs"] > packets[2]["receiver"]["response"]["endNs"]
        and old["incoming"]["timeNs"] > boundaries["server-route:before"]["operation"]["endNs"],
        "Primary queued packet does not span actual handoffs and overtaking standby request/reply.",
    )
    for ticket in (5, 6):
        require(
            packets[ticket]["admission"]["readEndNs"]
            < boundaries["logoff:before"]["operation"]["startNs"]
            < boundaries["install-standby-attachment-deny:before"]["operation"]["endNs"]
            < packets[ticket]["incoming"]["timeNs"],
            "Queued original/reply does not span actual Logoff and explicit installed guard invalidation.",
        )
    require(
        raw["cacheViews"]["final"]
        == {
            "a": [
                {"original": replication.ORIGINAL, "unreplied": False, "assured": False, "mark": 0}
            ],
            "b": [{"original": replication.ORIGINAL, "unreplied": True, "assured": False}],
        }
        and manifest["endNs"] - manifest["startNs"] < 30_000_000_000,
        "Final actual caches or finite selected lifetime disagree.",
    )
    protected_initial = boundaries["protect-marker:before"]
    return {
        **{
            key: raw[key]
            for key in (
                "schema",
                "profile",
                "captureID",
                "packetCount",
                "snapshotCount",
                "frameCount",
                "nflogCount",
                "syncFrameCount",
                "eapEvidence",
                "credential",
            )
        },
        "initial": initial["conntrack"],
        "initialSnapshots": {
            actor: ref["file"] for actor, ref in initial["native"]["conntrack"].items()
        },
        "protectedInitial": protected_initial["conntrack"],
        "protectedInitialSnapshots": {
            actor: ref["file"] for actor, ref in protected_initial["native"]["conntrack"].items()
        },
        "final": final["conntrack"],
        "events": report_events,
        "boundaries": boundaries,
        "namespaceRefs": evidence.namespace_refs,
        "interfaceRefs": evidence.interface_refs,
        "maintenance": evidence.maintenance,
        "guardBindings": guard_bindings,
        "protectedEpoch": {
            "reset": "reset-tracking",
            "startup": "start-replication",
            "protect": "protect-marker",
            "unsafeWitness": "unsafe-original",
        },
        "withdrawal": {
            "archiveBoundary": ARCHIVE,
            "retiredAtNs": evidence.events["withdraw-primary"]["result"]["retiredAtNs"],
            "observedLivePrimaryAfter": False,
        },
        "safeFence": {
            "completedPrimaryTicket": True,
            "completion": "serve-primary",
            "barrierSource": evidence.events["primary-barrier"]["result"]["qdisc"]["file"],
            "fence": "fence-primary",
        },
    }


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "directory", nargs="?", type=Path, default=ROOT / "examples/attachments/native"
    )
    parser.add_argument("--output", type=Path)
    args = parser.parse_args(argv)
    try:
        result = check_capture(args.directory)
    except (EvidenceError, ValueError, TypeError, KeyError, IndexError, OSError) as error:
        parser.exit(1, f"Attachment capture rejected: {error}\n")
    if args.output:
        args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(
        f"Verified one attached session, {result['packetCount']} datagrams, and eight pre-conntrack drops."
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
