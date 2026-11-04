"""Check retained lifecycle traces, socket observations, and raw Netlink snapshots.

This offline evidence check imports no native collector decoder. It checks the
recorded experiment, without proving kernel execution or complete event coverage.
"""

import argparse
import ipaddress
import json
import re
import shlex
import sys
from pathlib import Path


class EvidenceError(ValueError):
    """Required native evidence is absent, malformed, or contradictory."""


def require(condition, message):
    if not condition:
        raise EvidenceError(message)


def unique_object(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, f"Duplicate JSON key {key}.")
        result[key] = value
    return result


def read_json(path):
    return json.loads(Path(path).read_text(), object_pairs_hook=unique_object)


def bounded(value, size):
    require(type(value) is int and 0 <= value < size, f"Invalid bounded integer {value!r}.")
    return value


def header(value):
    require(
        set(value) == {"source", "destination", "protocol", "sourcePort", "destinationPort"},
        "Unexpected packet fields.",
    )
    for name in ("source", "destination"):
        try:
            parsed = ipaddress.IPv4Address(value[name])
        except ipaddress.AddressValueError as error:
            raise EvidenceError("Invalid IPv4 address.") from error
        require(str(parsed) == value[name], "Invalid IPv4 address.")
    bounded(value["protocol"], 256)
    bounded(value["sourcePort"], 65536)
    bounded(value["destinationPort"], 65536)
    require(value["protocol"] in (6, 17), "Require TCP or UDP packet evidence.")
    return value


def reverse(packet):
    return {
        "source": packet["destination"],
        "destination": packet["source"],
        "protocol": packet["protocol"],
        "sourcePort": packet["destinationPort"],
        "destinationPort": packet["sourcePort"],
    }


def tokens_value(tokens, prefix, *, required=True):
    values = [
        tokens[index + len(prefix)]
        for index in range(len(tokens) - len(prefix))
        if tokens[index : index + len(prefix)] == prefix
    ]
    require(
        len(values) <= 1 and (values or not required), f"Missing or repeated {' '.join(prefix)}."
    )
    return values[0] if values else None


def trace_packet(text):
    tokens = shlex.split(text)
    transports = [kind for kind in ("tcp", "udp") if kind in tokens]
    require(len(transports) == 1, "Missing or conflicting transport packet fields.")
    protocol = transports[0]
    packet = header(
        {
            "source": tokens_value(tokens, ["ip", "saddr"]),
            "destination": tokens_value(tokens, ["ip", "daddr"]),
            "protocol": 6 if protocol == "tcp" else 17,
            "sourcePort": int(tokens_value(tokens, [protocol, "sport"])),
            "destinationPort": int(tokens_value(tokens, [protocol, "dport"])),
        }
    )
    ip_id = tokens_value(tokens, ["ip", "id"], required=False)
    return {
        "packet": packet,
        "iif": tokens_value(tokens, ["iif"]),
        "oif": tokens_value(tokens, ["oif"], required=False),
        "ipId": bounded(int(ip_id), 65536) if ip_id is not None else None,
    }


def parse_trace(text):
    traces = {}
    for number, line in enumerate(text.splitlines(), 1):
        if not line.strip():
            continue
        matched = re.fullmatch(r"trace id ([0-9a-f]{8}) ip (\S+) (\S+) (.*)", line.strip())
        require(matched is not None, f"Unsupported trace line {number}.")
        trace_id, table, chain, body = matched.groups()
        trace = traces.setdefault(trace_id, {"id": trace_id, "stages": []})
        stages = trace["stages"]
        require(
            not any(
                stage["verdicts"] and stage["verdicts"][-1]["verdict"] == "drop" for stage in stages
            ),
            f"Trace {trace_id} continues after a drop.",
        )
        if body.startswith("packet: "):
            stages.append(
                {
                    "table": table,
                    "chain": chain,
                    "line": number,
                    **trace_packet(body[8:]),
                    "verdicts": [],
                }
            )
            continue
        require(
            stages and (stages[-1]["table"], stages[-1]["chain"]) == (table, chain),
            f"Orphan or reordered verdict at trace line {number}.",
        )
        stage = stages[-1]
        require(
            not stage["verdicts"] or stage["verdicts"][-1]["verdict"] == "continue",
            f"Contradictory terminal verdicts at trace line {number}.",
        )
        policy = re.fullmatch(r"policy (accept|drop)", body)
        rule = re.fullmatch(r"(.*?) \(verdict (accept|drop|continue)\)", body)
        require(policy or rule, f"Unsupported verdict at trace line {number}.")
        if policy:
            verdict = {"kind": "policy", "verdict": policy[1], "line": number}
        else:
            handle = re.fullmatch(r"unknown rule handle ([0-9]+)", rule[1])
            require(handle or rule[1].startswith("rule "), f"Unsupported rule at line {number}.")
            verdict = {
                "kind": "rule",
                "verdict": rule[2],
                "line": number,
                "handle": int(handle[1]) if handle else None,
                "text": None if handle else rule[1][5:],
            }
        stage["verdicts"].append(verdict)
    require(traces, "The trace contains no packet evidence.")
    for trace in traces.values():
        for stage in trace["stages"]:
            require(
                stage["verdicts"] and stage["verdicts"][-1]["verdict"] in ("accept", "drop"),
                f"Trace {trace['id']} has an incomplete chain visit.",
            )
    return list(traces.values())


def decode_snapshot(document):
    require(document.get("schema") == 1 and document.get("family") == 2, "Invalid snapshot schema.")
    request = bytes.fromhex(document["request"])
    require(len(request) == 20, "Invalid Netlink request size.")
    byteorder = "little" if request[:4] == b"\x14\0\0\0" else "big"

    def word(data, start, size):
        require(start + size <= len(data), "Truncated Netlink field.")
        return int.from_bytes(data[start : start + size], byteorder)

    def attributes(data, depth=0):
        require(depth <= 32, "Excessive nested attribute depth.")
        fields, position = {}, 0
        while position < len(data):
            length, kind = word(data, position, 2), word(data, position + 2, 2)
            require(
                4 <= length and position + ((length + 3) // 4 * 4) <= len(data),
                "Malformed Netlink attribute.",
            )
            key = kind & 0x3FFF
            require(key not in fields, "Duplicate Netlink attribute.")
            payload = data[position + 4 : position + length]
            fields[key] = attributes(payload, depth + 1) if kind & 0x8000 else payload
            position += (length + 3) // 4 * 4
        return fields

    def scalar(fields, key, size, optional=False):
        value = fields.get(key)
        if value is None and optional:
            return None
        require(
            isinstance(value, bytes) and len(value) == size, "Missing or invalid scalar attribute."
        )
        return int.from_bytes(value, "big")

    def tuple_header(fields):
        ips, proto = fields[1], fields[2]
        require(isinstance(ips, dict) and isinstance(proto, dict), "Missing nested tuple fields.")
        return header(
            {
                "source": str(ipaddress.IPv4Address(scalar(ips, 1, 4))),
                "destination": str(ipaddress.IPv4Address(scalar(ips, 2, 4))),
                "protocol": scalar(proto, 1, 1),
                "sourcePort": scalar(proto, 2, 2),
                "destinationPort": scalar(proto, 3, 2),
            }
        )

    require(
        (word(request, 0, 4), word(request, 4, 2), word(request, 6, 2)) == (20, 0x101, 0x301)
        and request[16:] == b"\x02\0\0\0",
        "Unexpected Netlink request or filtering.",
    )
    require(word(request, 8, 4) and word(request, 12, 4), "Missing request sequence or port.")
    decoded, completed = [], False
    for text in document["messages"]:
        raw = bytes.fromhex(text)
        require(
            not completed and len(raw) >= 16 and word(raw, 0, 4) == len(raw),
            "Truncated message or data after completion.",
        )
        require(raw[8:16] == request[8:16], "Netlink sequence or port disagreement.")
        kind, flags = word(raw, 4, 2), word(raw, 6, 2)
        require(flags & 0x10 == 0 and flags & 2, "Interrupted or non-multipart Netlink dump.")
        if kind == 3:
            require(flags == 2 and raw[16:] == bytes(4), "Unsuccessful Netlink completion.")
            completed = True
            continue
        require(
            kind == 0x100 and flags in (2, 0x22) and raw[16:20] == b"\x02\0\0\0",
            "Unexpected conntrack message.",
        )
        fields = attributes(raw[20:])
        original, reply = tuple_header(fields[1]), tuple_header(fields[2])
        require(original["protocol"] == reply["protocol"], "Tuple protocol disagreement.")
        default = scalar(fields, 18, 2, optional=True)
        original_zone = scalar(fields[1], 3, 2, optional=True)
        reply_zone = scalar(fields[2], 3, 2, optional=True)
        require(
            default is None or (original_zone is None and reply_zone is None),
            "Conflicting default and directional zones.",
        )
        decoded.append(
            {
                "original": original,
                "reply": reply,
                "originalZone": original_zone if original_zone is not None else (default or 0),
                "replyZone": reply_zone if reply_zone is not None else (default or 0),
                "status": scalar(fields, 3, 4),
                "remainingTTL": scalar(fields, 7, 4, optional=True),
                "id": scalar(fields, 12, 4, optional=True),
                "mark": scalar(fields, 8, 4, optional=True),
                "use": scalar(fields, 11, 4, optional=True),
                "raw": raw.hex(),
            }
        )
    require(completed, "Missing successful Netlink DONE completion.")
    require(decoded == document["entries"], "Raw and structured snapshot fields disagree.")
    return decoded


STATE_BITS = {"invalid": 1, "established": 2, "related": 4, "new": 8, "untracked": 64}


def native_match(expression, state, packet):
    left, right, operator = expression["left"], expression["right"], expression["op"]
    if left == {"ct": {"key": "state"}}:
        require(operator in ("in", "=="), "Unsupported native state operator.")
        if type(right) is int:
            bounded(right, 128)
            require(right > 0 and right & ~79 == 0, "Unsupported native state bits.")
            return (
                bool(right & STATE_BITS[state]) if operator == "in" else right == STATE_BITS[state]
            )
        values = right.get("set") if isinstance(right, dict) else right
        if isinstance(values, list):
            require(operator == "in" or isinstance(right, dict), "Ambiguous state-list equality.")
            require(
                values and all(isinstance(value, str) and value in STATE_BITS for value in values),
                "Unsupported state-list elements.",
            )
            require(len(set(values)) == len(values), "Repeated state-list elements.")
            return state in values
        require(right in STATE_BITS, "Unsupported native state value.")
        return state == right
    require(operator == "==", "Unsupported native header operator.")
    if left == {"meta": {"key": "l4proto"}}:
        return packet["protocol"] == right
    field = left["payload"]
    protocol, name = field["protocol"], field["field"]
    if protocol == "ip" and name in ("saddr", "daddr"):
        address = ipaddress.IPv4Address(packet["source" if name == "saddr" else "destination"])
        if isinstance(right, dict):
            prefix = right["prefix"]
            return address in ipaddress.IPv4Network(
                f"{prefix['addr']}/{prefix['len']}", strict=False
            )
        return address == ipaddress.IPv4Address(right)
    require(
        protocol in ("tcp", "udp") and name in ("sport", "dport"), "Unsupported native payload."
    )
    return (
        packet["protocol"] == (6 if protocol == "tcp" else 17)
        and packet["sourcePort" if name == "sport" else "destinationPort"] == right
    )


def native_chain(document, table, chain):
    objects = document["nftables"]
    chains = [
        item["chain"]
        for item in objects
        if "chain" in item and item["chain"]["table"] == table and item["chain"]["name"] == chain
    ]
    require(len(chains) == 1, "Missing or ambiguous exported native chain.")
    rules = [
        item["rule"]
        for item in objects
        if "rule" in item and item["rule"]["table"] == table and item["rule"]["chain"] == chain
    ]
    require(
        chains[0]["family"] == "ip" and all(rule["family"] == "ip" for rule in rules),
        "Unsupported native chain family.",
    )
    return chains[0], rules


def selected_rule(document, table, chain, state, packet):
    chain_record, rules = native_chain(document, table, chain)
    for rule in rules:
        expressions = rule["expr"]
        require(expressions and len(expressions[-1]) == 1, "Missing native terminal statement.")
        conditions = []
        for expression in expressions[:-1]:
            require(set(expression) == {"match"}, "Unsupported native rule expression.")
            conditions.append(native_match(expression["match"], state, packet))
        if all(conditions):
            return rule, expressions[-1]
    return None, {chain_record["policy"]: None}


def check_filter(stage, document, state, expected):
    selected, action = selected_rule(
        document, stage["table"], stage["chain"], state, stage["packet"]
    )
    require(
        action == {expected: None}, "Exported filter rules contradict the expected lifecycle case."
    )
    observed = stage["verdicts"][-1]
    require(observed["verdict"] == expected, "Kernel filter verdict contradicts the export.")
    if selected is None:
        require(observed["kind"] == "policy", "Trace rule contradicts an exported policy decision.")
    else:
        require(observed["kind"] == "rule", "Trace policy contradicts an exported matching rule.")
        if observed["handle"] is not None:
            require(observed["handle"] == selected["handle"], "Native rule handle disagreement.")
        else:
            words = shlex.split(observed["text"])
            require(
                "comment" in words and words[words.index("comment") + 1] == selected.get("comment"),
                "Native rule comment disagreement.",
            )
            if "ct" in words:
                index = words.index("ct")
                require(
                    words[index : index + 3] == ["ct", "state", state],
                    "Trace state guard disagreement.",
                )


def check_capture(directory, *, trace_path=None, observations_path=None):
    directory = Path(directory)
    trace_path = Path(trace_path) if trace_path else directory / "trace.txt"
    observations = read_json(observations_path or directory / "observations.json")
    require(
        not (directory / "trace-errors.txt").read_text().strip(),
        "Native trace monitor reported errors.",
    )
    traces = parse_trace(trace_path.read_text())
    names = [
        "forward-drop",
        "late-drop",
        "first-original",
        "unreplied-after-nat-update",
        "first-reply-dropped",
        "existing-after-update",
        "fresh-after-update",
        "old-after-delete",
    ]
    require(
        [row["phase"] for row in observations] == names, "Missing or reordered lifecycle phases."
    )
    snapshots = {
        name: decode_snapshot(read_json(directory / f"{name}.json"))
        for name in (
            "forward-drop-state",
            "late-drop-state",
            "opened-state",
            "unreplied-updated-state",
            "reply-dropped-state",
            "updated-state",
            "deleted-state",
            "after-delete-packet-state",
        )
    }
    for name in (
        "forward-drop-state",
        "late-drop-state",
        "deleted-state",
        "after-delete-packet-state",
    ):
        require(snapshots[name] == [], f"{name} unexpectedly contains a visible confirmed row.")
    require(len(snapshots["opened-state"]) == 1, "Expected one newly opened visible flow.")
    opened = snapshots["opened-state"][0]
    require(opened["status"] == 440, "Opened flow must not yet have SEEN_REPLY.")
    for name, expected_status in (
        ("unreplied-updated-state", 440),
        ("reply-dropped-state", 442),
        ("updated-state", 442),
    ):
        rows = snapshots[name]
        require(len(rows) == 1, f"{name} must retain exactly the cached flow.")
        for key in ("original", "reply", "originalZone", "replyZone", "id"):
            require(rows[0][key] == opened[key], f"{name} changed the cached {key}.")
        require(rows[0]["status"] == expected_status, f"{name} has unexpected lifecycle status.")
    original, reply = opened["original"], opened["reply"]
    wire, restored = reverse(reply), reverse(original)
    initial = read_json(directory / "forward-initial.json")
    reply_filter = read_json(directory / "forward-drop-reply.json")
    established = read_json(directory / "forward-established-only.json")
    late_filter = read_json(directory / "late.json")
    nat_initial = read_json(directory / "nat-initial.json")
    nat_changed = read_json(directory / "nat-changed.json")
    trace_names = ("netlib_trace", "trace")
    destination_names = ("netlib_nat", "destination")
    forward_names = ("netlib_filter", "forward")
    source_names = ("netlib_nat", "source")
    late_names = ("netlib_late", "late")
    for document, key, kind, hook, priority in (
        (initial, forward_names, "filter", "forward", 0),
        (reply_filter, forward_names, "filter", "forward", 0),
        (established, forward_names, "filter", "forward", 0),
        (late_filter, late_names, "filter", "postrouting", 200),
        (nat_initial, destination_names, "nat", "prerouting", -100),
        (nat_initial, source_names, "nat", "postrouting", 100),
        (nat_changed, destination_names, "nat", "prerouting", -100),
        (nat_changed, source_names, "nat", "postrouting", 100),
    ):
        chain, _ = native_chain(document, *key)
        require(
            (chain["type"], chain["hook"], chain["prio"]) == (kind, hook, priority),
            "Exported native hook order contradicts the experiment.",
        )
    _, changed_source = selected_rule(nat_changed, *source_names, "new", original)
    require(
        changed_source == {"snat": {"addr": wire["source"], "port": 40001}},
        "The changed SNAT rule does not record the distinct new allocation.",
    )
    routes = read_json(directory / "routes.json")
    calls = []
    for row in observations:
        calls.append((row["phase"], header(row["sent"]["packet"]), row))
        if row["phase"] == "existing-after-update":
            calls.append((row["phase"] + ":reply", header(row["reply"]["packet"]), row))
    require(len(traces) == len(calls) == 9, "Trace and socket call counts disagree.")
    phases = []
    for trace, (phase, sent, row) in zip(traces, calls, strict=True):
        stages = trace["stages"]
        require(
            stages[0]["packet"] == sent, f"{phase}: trace input contradicts sent socket header."
        )
        is_reply = phase in ("first-reply-dropped", "existing-after-update:reply")
        fresh = phase in (
            "forward-drop",
            "late-drop",
            "first-original",
            "fresh-after-update",
            "old-after-delete",
        )
        state = "established" if is_reply or phase == "existing-after-update" else "new"
        denied = phase in (
            "forward-drop",
            "first-reply-dropped",
            "fresh-after-update",
            "old-after-delete",
        )
        expected_keys = [trace_names] + ([destination_names] if fresh else []) + [forward_names]
        if not denied:
            expected_keys += ([source_names] if fresh else []) + [late_names]
        require(
            [(stage["table"], stage["chain"]) for stage in stages] == expected_keys,
            f"{phase}: unexpected or missing hook-chain visits.",
        )
        forward = next(
            stage for stage in stages if (stage["table"], stage["chain"]) == forward_names
        )
        if fresh:
            source = (
                nat_changed if phase in ("fresh-after-update", "old-after-delete") else nat_initial
            )
            _, nat = selected_rule(source, *destination_names, state, sent)
            require(set(nat) == {"dnat"}, f"{phase}: missing DNAT evidence.")
            after_destination = {
                **sent,
                "destination": nat["dnat"]["addr"],
                "destinationPort": nat["dnat"]["port"],
            }
        else:
            require(
                sent == (reply if is_reply else original), f"{phase}: cached input tuple mismatch."
            )
            after_destination = (
                {
                    **reply,
                    "destination": original["source"],
                    "destinationPort": original["sourcePort"],
                }
                if is_reply
                else {
                    **original,
                    "destination": reply["source"],
                    "destinationPort": reply["sourcePort"],
                }
            )
        require(
            forward["packet"] == after_destination,
            f"{phase}: FORWARD must observe post-DNAT header.",
        )
        matching_routes = [
            route
            for route in routes
            if ipaddress.IPv4Address(after_destination["destination"])
            in ipaddress.IPv4Network(route["dst"])
        ]
        require(matching_routes, "No exported route covers the post-DNAT destination.")
        longest = max(ipaddress.IPv4Network(route["dst"]).prefixlen for route in matching_routes)
        selected_routes = [
            route
            for route in matching_routes
            if ipaddress.IPv4Network(route["dst"]).prefixlen == longest
        ]
        require(
            len(selected_routes) == 1 and selected_routes[0]["dev"] == forward["oif"],
            "Post-DNAT routing contradicts the observed output interface.",
        )
        active_filter = (
            reply_filter
            if phase == "first-reply-dropped"
            else established
            if phase
            in (
                "existing-after-update",
                "existing-after-update:reply",
                "fresh-after-update",
                "old-after-delete",
            )
            else initial
        )
        check_filter(forward, active_filter, state, "drop" if denied else "accept")
        for stage in stages:
            require(
                stage["iif"] == ("outside0" if is_reply else "inside0"),
                "Input interface disagreement.",
            )
            require(
                stage["ipId"] == stages[0]["ipId"], "IP packet identity changes within a trace."
            )
            if stage["oif"] is not None:
                require(
                    stage["oif"] == ("inside0" if is_reply else "outside0"),
                    "Output interface disagreement.",
                )
        if not denied:
            after_source = restored if is_reply else wire
            if fresh:
                source_stage = next(stage for stage in stages if stage["chain"] == "source")
                require(
                    source_stage["packet"] == after_destination, "SNAT input header disagreement."
                )
                _, nat = selected_rule(nat_initial, *source_names, state, after_destination)
                require(set(nat) == {"snat"}, "Missing SNAT evidence.")
                after_source = {
                    **after_destination,
                    "source": nat["snat"]["addr"],
                    "sourcePort": nat["snat"]["port"],
                }
            late = stages[-1]
            require(
                late["packet"] == after_source,
                f"{phase}: late filter must observe post-SNAT header.",
            )
            check_filter(late, late_filter, state, "drop" if phase == "late-drop" else "accept")
        result_key = "client" if is_reply else "server"
        observed = row[result_key]
        if denied or phase == "late-drop":
            require(observed is None, f"{phase}: dropped packet unexpectedly reached a socket.")
        else:
            require(
                observed and header(observed["packet"]) == after_source,
                f"{phase}: socket output contradicts the kernel trace.",
            )
            input_key = "reply" if phase.endswith(":reply") else "sent"
            require(
                observed["payload"] == row[input_key]["payload"], "Socket payload disagreement."
            )
        disposition = (
            "forwardDrop" if denied else "lateDrop" if phase == "late-drop" else "forwarded"
        )
        require(forward["oif"] in ("inside0", "outside0"), "Missing modeled next-hop interface.")
        phases.append(
            {
                "phase": phase,
                "traceId": trace["id"],
                "state": state,
                "fresh": fresh,
                "input": sent,
                "afterDestination": forward["packet"],
                "afterSource": stages[-1]["packet"] if not denied else None,
                "output": stages[-1]["packet"] if disposition == "forwarded" else None,
                "disposition": disposition,
                "nextHop": "client" if forward["oif"] == "inside0" else "server",
                "fieldEvidence": {
                    "input": "trace-packet",
                    "afterDestination": "trace-forward-packet",
                    "afterSource": "not-reached" if denied else "trace-late-packet",
                    "output": "trace-and-socket"
                    if disposition == "forwarded"
                    else "trace-drop-and-socket-absence",
                    "disposition": "trace-terminal-verdict-and-socket-outcome",
                    "nextHop": "trace-oif-with-declared-interface-mapping",
                    "state": "valid-ordinary-key-miss-assumption-and-filter-evaluation"
                    if phase in ("fresh-after-update", "old-after-delete")
                    else "matching-exported-rule-state-guard",
                    "fresh": "visible-snapshots-and-supported-ordinary-profile-assumption",
                },
                "stages": stages,
            }
        )
    return {
        "schema": 1,
        "scope": "checked-native-lifecycle-evidence",
        "traceCount": len(traces),
        "packetCount": sum(len(trace["stages"]) for trace in traces),
        "snapshotCount": len(snapshots),
        "phases": phases,
    }


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--capture-dir", type=Path, default=Path("examples/lifecycle/native"))
    parser.add_argument("--trace", type=Path)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args(argv)
    try:
        report = check_capture(args.capture_dir, trace_path=args.trace)
        if args.output:
            args.output.write_text(json.dumps(report, indent=2) + "\n")
        print(
            f"Verified {report['traceCount']} traces, {report['packetCount']} hook packets, "
            f"and {report['snapshotCount']} raw snapshots."
        )
    except (ValueError, OSError, KeyError, TypeError) as error:
        print(f"lifecycle evidence: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
