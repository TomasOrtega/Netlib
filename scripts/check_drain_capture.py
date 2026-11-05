"""Check retained postrouting, queue, socket, and raw conntrack evidence.

This checks a finite private experiment. It does not prove kernel execution,
capture authenticity, queue identity, or a universal drain-time bound.
"""

import argparse
import ipaddress
import json
import shlex
import sys
from pathlib import Path

from check_lifecycle_capture import EvidenceError as EvidenceError
from check_lifecycle_capture import (
    bounded,
    check_filter,
    check_rule_trace,
    check_trace_stage,
    decode_snapshot,
    header,
    native_chain,
    parse_trace,
    read_json,
    require,
    reverse,
    rule_tokens,
    tokens_value,
)

QUEUE_COMMAND = [
    "tc",
    "qdisc",
    "add",
    "dev",
    "outside0",
    "root",
    "handle",
    "10:",
    "netem",
    "limit",
    "32",
    "delay",
    "4000ms",
]
BARRIER_COMMAND = (
    'add rule ip netlib_late late ip daddr 198.51.100.2 meta l4proto udp drop comment "BARRIER"\n'
)
OLD_PAYLOAD = "drain-old-already-queued"
BLOCKED_PAYLOAD = "drain-new-after-barrier"


def interval(record):
    start, end = record["startNs"], record["endNs"]
    bounded(start, 2**64)
    bounded(end, 2**64)
    require(0 < start <= end, "Invalid monotonic interval.")
    return start, end


def named_interval(record, filename):
    require(
        set(record) == {"startNs", "endNs", "file"} and record["file"] == filename,
        "Unexpected evidence file or interval fields.",
    )
    return interval(record)


def table_profile(document, table, specifications):
    objects = document["nftables"]
    require(all(len(item) == 1 for item in objects), "Invalid exported object.")
    metadata = [item["metainfo"] for item in objects if "metainfo" in item]
    tables = [item["table"] for item in objects if "table" in item]
    chains = [item["chain"] for item in objects if "chain" in item]
    require(
        len(metadata) == len(tables) == 1
        and (metadata[0]["version"], metadata[0]["json_schema_version"]) == ("1.1.3", 1),
        "Unexpected nftables producer.",
    )
    require(
        tables[0]["family"] == "ip" and tables[0]["name"] == table, "Unexpected exported table."
    )
    require(
        len(chains) == len(specifications)
        and {chain["name"] for chain in chains} == set(specifications),
        "Unexpected exported chain inventory.",
    )
    require(
        all(next(iter(item)) in {"metainfo", "table", "chain", "rule"} for item in objects),
        "Unsupported exported object.",
    )
    for name, (kind, hook, priority, policy) in specifications.items():
        chain, rules = native_chain(document, table, name)
        require(
            type(chain["prio"]) is int
            and (chain["type"], chain["hook"], chain["prio"], chain["policy"])
            == (kind, hook, priority, policy),
            "Exported hook order or policy disagreement.",
        )
        for rule in rules:
            require(
                type(rule["handle"]) is int and rule["handle"] > 0, "Invalid exported rule handle."
            )


def check_qdisc(document, *, count, backlog, packets, byte_count):
    require(isinstance(document, list) and len(document) == 1, "Expected one isolated root qdisc.")
    row = document[0]
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
        },
        "Unsupported qdisc fields.",
    )
    require(
        (row["kind"], row["handle"]) == ("netem", "10:") and row["root"] is True,
        "Unexpected root netem qdisc.",
    )
    options = row["options"]
    require(
        type(options["limit"]) is int
        and type(options["gap"]) is int
        and all(type(value) in (int, float) for value in options["delay"].values()),
        "Invalid qdisc numeric configuration fields.",
    )
    require(
        set(options) == {"limit", "delay", "seed", "ecn", "gap"}
        and options["limit"] == 32
        and options["delay"] == {"delay": 4, "jitter": 0, "correlation": 0}
        and options["ecn"] is False
        and options["gap"] == 0,
        "Qdisc configuration contradicts the delay-only command.",
    )
    bounded(options["seed"], 2**64)
    bounded(row["refcnt"], 2**32)
    for name in ("bytes", "packets", "drops", "overlimits", "requeues", "backlog", "qlen"):
        bounded(row[name], 2**64)
    require(
        (row["qlen"], row["backlog"], row["packets"], row["bytes"])
        == (count, backlog, packets, byte_count),
        "Qdisc queue count or byte counters disagree.",
    )
    require(
        row["drops"] == row["overlimits"] == row["requeues"] == 0,
        "The isolated qdisc reports drops, overlimits, or requeues.",
    )
    return row


def check_isolation(directory):
    neighbors = read_json(directory / "neighbors.json")
    require(
        len(neighbors) == 2
        and {(row["dst"], row["dev"], row["lladdr"], tuple(row["state"])) for row in neighbors}
        == {
            ("192.0.2.2", "inside0", "02:00:00:00:01:02", ("PERMANENT",)),
            ("198.51.100.2", "outside0", "02:00:00:00:02:02", ("PERMANENT",)),
        },
        "Missing permanent router neighbors.",
    )
    links = read_json(directory / "links.json")
    require(
        {row["ifname"] for row in links} == {"lo", "inside0", "outside0"},
        "Unexpected router link inventory.",
    )
    for row in links:
        require("UP" in row["flags"], "A private router link is down.")
    for namespace in ("client", "router", "server"):
        expected = (
            f"net.ipv4.ip_forward = {int(namespace == 'router')}\n"
            "net.ipv6.conf.all.disable_ipv6 = 1\n"
            "net.ipv6.conf.default.disable_ipv6 = 1\n"
        )
        require(
            (directory / f"{namespace}-settings.txt").read_text() == expected,
            "Namespace forwarding or IPv6 isolation settings disagree.",
        )


def check_capture(directory, *, trace_path=None, observations_path=None):
    directory = Path(directory)
    observations = read_json(observations_path or directory / "observations.json")
    require(
        set(observations)
        == {
            "schema",
            "qdisc",
            "conntrack",
            "receiver",
            "install",
            "old",
            "receiverAfterOld",
            "blocked",
        }
        and type(observations["schema"]) is int
        and observations["schema"] == 1,
        "Unsupported drain observations.",
    )
    require(
        not (directory / "trace-errors.txt").read_text().strip(),
        "The native trace monitor reported errors.",
    )
    require(
        (directory / "tc-version.txt").read_text().strip() == "tc utility, iproute2-6.17.0",
        "Unexpected tc producer version.",
    )
    require(
        (directory / "iproute2-version.txt").read_text().strip() == "ip utility, iproute2-6.19.0",
        "Unexpected ip producer version.",
    )
    require(
        read_json(directory / "queue-command.json") == QUEUE_COMMAND,
        "Unexpected queue installation command.",
    )
    require(
        (directory / "install-barrier.nft").read_text() == BARRIER_COMMAND,
        "Unexpected native barrier command.",
    )
    check_isolation(directory)
    install_start, install_end = named_interval(observations["install"], "install-barrier.nft")
    old, blocked = observations["old"], observations["blocked"]
    require(
        set(old) == {"sent", "server"} and set(blocked) == {"sent", "server", "timeout"},
        "Unsupported socket observations.",
    )
    original = header(old["sent"]["packet"])
    require(
        original
        == {
            "source": "192.0.2.2",
            "destination": "203.0.113.2",
            "protocol": 17,
            "sourcePort": 31000,
            "destinationPort": 8080,
        },
        "Unexpected original socket tuple.",
    )
    require(
        header(blocked["sent"]["packet"]) == original,
        "The blocked send must reuse the confirmed original tuple.",
    )
    require(
        old["sent"]["payload"] == old["server"]["payload"] == OLD_PAYLOAD
        and blocked["sent"]["payload"] == BLOCKED_PAYLOAD,
        "Socket payload identity disagreement.",
    )
    require(
        blocked["server"] is None
        and blocked["timeout"]["packet"] is None
        and blocked["timeout"]["payload"] is None,
        "A blocked packet reached the server.",
    )
    old_start, old_end = interval(old["sent"])
    receive_start, receive_end = interval(old["server"])
    blocked_start, blocked_end = interval(blocked["sent"])
    timeout_start, timeout_end = interval(blocked["timeout"])
    receiver_ready = bounded(observations["receiver"]["readyNs"], 2**64)
    after_ready = bounded(observations["receiverAfterOld"]["readyNs"], 2**64)
    require(
        receive_start <= receiver_ready < old_start <= old_end < install_start < install_end,
        "The old receive and send must start before installation.",
    )
    require(install_end < receive_end, "The old packet must be received after installation.")
    require(
        install_end
        < blocked_start
        <= blocked_end
        < receive_end
        < timeout_start
        <= after_ready
        <= timeout_end,
        "The blocked send or socket timeout has contradictory timing.",
    )
    qdisc_intervals, qdisc_rows = {}, []
    qdisc = observations["qdisc"]
    require(
        set(qdisc) == {"configured", "pending", "blocked", "drained"}, "Missing queue observation."
    )
    frame_length = 14 + 20 + 8 + len(OLD_PAYLOAD.encode("ascii"))
    for name, count, packets in (
        ("configured", 0, 0),
        ("pending", 1, 0),
        ("blocked", 1, 0),
        ("drained", 0, 1),
    ):
        qdisc_intervals[name] = named_interval(qdisc[name], f"qdisc-{name}.json")
        qdisc_rows.append(
            check_qdisc(
                read_json(directory / qdisc[name]["file"]),
                count=count,
                backlog=frame_length * count,
                packets=packets,
                byte_count=frame_length * packets,
            )
        )
    require(
        all(row["options"] == qdisc_rows[0]["options"] for row in qdisc_rows),
        "The queue configuration changed during the experiment.",
    )
    require(
        qdisc_intervals["configured"][1] < receive_start
        and old_end
        < qdisc_intervals["pending"][0]
        <= qdisc_intervals["pending"][1]
        < install_start,
        "The pending queue observation must precede installation.",
    )
    require(
        blocked_end < qdisc_intervals["blocked"][0] <= qdisc_intervals["blocked"][1] < receive_end
        and timeout_end < qdisc_intervals["drained"][0],
        "The blocked or drained queue observation has contradictory timing.",
    )
    conntrack = observations["conntrack"]
    require(
        set(conntrack) == {"initial", "pending", "blocked", "drained"},
        "Missing raw conntrack observation.",
    )
    snapshots, snapshot_intervals = {}, {}
    for name in ("initial", "pending", "blocked", "drained"):
        snapshot_intervals[name] = named_interval(conntrack[name], f"{name}-state.json")
        snapshots[name] = decode_snapshot(read_json(directory / conntrack[name]["file"]))
    require(snapshots["initial"] == [], "The initial confirmed table must be empty.")
    require(
        snapshot_intervals["initial"][1] < receive_start
        and qdisc_intervals["pending"][1]
        < snapshot_intervals["pending"][0]
        <= snapshot_intervals["pending"][1]
        < install_start
        and blocked_end
        < snapshot_intervals["blocked"][0]
        <= snapshot_intervals["blocked"][1]
        < qdisc_intervals["blocked"][0]
        and qdisc_intervals["drained"][1] < snapshot_intervals["drained"][0],
        "The confirmed-table observation has contradictory timing.",
    )
    require(len(snapshots["pending"]) == 1, "Expected one confirmed pending flow.")
    opened = snapshots["pending"][0]
    for name in ("pending", "blocked", "drained"):
        rows = snapshots[name]
        require(
            len(rows) == 1 and rows[0]["status"] == 440, "Expected one confirmed unreplied NAT row."
        )
        require(
            all(
                rows[0][key] == opened[key]
                for key in ("original", "reply", "originalZone", "replyZone", "id")
            ),
            "The cached association changed.",
        )
    wire = reverse(opened["reply"])
    require(
        opened["original"] == original
        and opened["originalZone"] == opened["replyZone"] == 0
        and wire
        == {
            "source": "203.0.113.1",
            "destination": "198.51.100.2",
            "protocol": 17,
            "sourcePort": 40000,
            "destinationPort": 9000,
        },
        "The raw confirmed association contradicts the socket tuples.",
    )
    require(header(old["server"]["packet"]) == wire, "Server socket header disagreement.")
    tables = {
        name: read_json(directory / f"{name}.json")
        for name in ("instrumentation", "nat", "forward", "late-before", "late-after")
    }
    table_profile(
        tables["instrumentation"],
        "netlib_trace",
        {"trace": ("filter", "prerouting", -301, "accept")},
    )
    _, instrumentation = native_chain(tables["instrumentation"], "netlib_trace", "trace")
    require(
        len(instrumentation) == 1
        and instrumentation[0]["expr"]
        == [{"mangle": {"key": {"meta": {"key": "nftrace"}}, "value": 1}}],
        "The exported trace instrumentation is unsupported.",
    )
    table_profile(
        tables["nat"],
        "netlib_nat",
        {
            "destination": ("nat", "prerouting", -100, "accept"),
            "source": ("nat", "postrouting", 100, "accept"),
        },
    )
    table_profile(tables["forward"], "netlib_filter", {"forward": ("filter", "forward", 0, "drop")})
    for name in ("late-before", "late-after"):
        table_profile(
            tables[name], "netlib_late", {"late": ("filter", "postrouting", 110, "accept")}
        )
    _, before_rules = native_chain(tables["late-before"], "netlib_late", "late")
    _, after_rules = native_chain(tables["late-after"], "netlib_late", "late")
    require(
        not before_rules
        and len(after_rules) == 1
        and rule_tokens(after_rules[0])
        == ["ip", "daddr", "198.51.100.2", "meta", "l4proto", "udp", "drop", "comment", "BARRIER"],
        "The late barrier must cover backend UDP at every port.",
    )
    traces = parse_trace(Path(trace_path or directory / "trace.txt").read_text())
    require(len(traces) == 2, "Expected exactly two packet traces.")
    routes = read_json(directory / "routes.json")
    after_destination = {
        **original,
        "destination": wire["destination"],
        "destinationPort": wire["destinationPort"],
    }
    selected_routes = [
        row
        for row in routes
        if ipaddress.IPv4Address(wire["destination"]) in ipaddress.IPv4Network(row["dst"])
    ]
    require(
        len(selected_routes) == 1 and selected_routes[0]["dev"] == "outside0",
        "The exported route contradicts the traced egress.",
    )
    phases = []
    for index, trace in enumerate(traces):
        fresh = index == 0
        stages = trace["stages"]
        keys = [("netlib_trace", "trace")]
        if fresh:
            keys += [("netlib_nat", "destination")]
        keys += [("netlib_filter", "forward")]
        if fresh:
            keys += [("netlib_nat", "source")]
        keys += [("netlib_late", "late")]
        require(
            [(stage["table"], stage["chain"]) for stage in stages] == keys,
            "Unexpected or missing packet hook visits.",
        )
        check_trace_stage(stages[0])
        require(stages[0]["packet"] == original, "Trace ingress contradicts the socket send.")
        expected_payload = OLD_PAYLOAD if fresh else BLOCKED_PAYLOAD
        trace_lines = Path(trace_path or directory / "trace.txt").read_text().splitlines()
        for stage in stages:
            require(
                stage["iif"] == "inside0"
                and stage["ipId"] is not None
                and stage["ipId"] == stages[0]["ipId"]
                and stage["oif"] in (None, "outside0"),
                "Packet interface or identity disagreement.",
            )
            tokens = shlex.split(trace_lines[stage["line"] - 1])
            require(
                int(tokens_value(tokens, ["udp", "length"])) == len(expected_payload) + 8
                and int(tokens_value(tokens, ["ip", "length"])) == len(expected_payload) + 28,
                "Trace lengths contradict the distinct socket payloads.",
            )
        if fresh:
            destination, source = stages[1], stages[3]
            require(
                destination["packet"] == original and source["packet"] == after_destination,
                "The NAT trace input headers disagree.",
            )
            _, dnat = check_rule_trace(destination, tables["nat"], "new")
            _, snat = check_rule_trace(source, tables["nat"], "new")
            require(
                dnat == {"dnat": {"addr": "198.51.100.2", "port": 9000}}
                and snat == {"snat": {"addr": "203.0.113.1", "port": 40000}},
                "The traced NAT actions contradict the confirmed binding.",
            )
        forward = stages[2 if fresh else 1]
        require(
            forward["packet"] == after_destination and forward["oif"] == "outside0",
            "The forward trace must observe the routed post-DNAT header.",
        )
        check_filter(forward, tables["forward"], "new", "accept")
        late = stages[-1]
        require(
            late["packet"] == wire and late["oif"] == "outside0",
            "The late trace must observe the post-SNAT header.",
        )
        check_filter(
            late,
            tables["late-before" if fresh else "late-after"],
            "new",
            "accept" if fresh else "drop",
        )
        phases.append(
            {
                "phase": "queued-before-barrier" if fresh else "blocked-after-barrier",
                "traceId": trace["id"],
                "inputPacket": original,
                "state": "new",
                "fresh": fresh,
                "afterDestination": after_destination,
                "afterSource": wire,
                "nextHop": "server",
                "disposition": "forwarded" if fresh else "lateDrop",
                "output": wire if fresh else None,
                "fieldEvidence": {
                    "state": "matching-exported-rule-state-guard",
                    "fresh": "raw-visible-snapshot-and-ordinary-tracking-assumption",
                    "output": "post-SNAT-trace-and-delayed-socket"
                    if fresh
                    else "trace-drop-and-timeout",
                },
                "stages": stages,
            }
        )
    require(
        traces[0]["stages"][0]["ipId"] != traces[1]["stages"][0]["ipId"],
        "The two packets need distinct retained IP identities.",
    )
    return {
        "schema": 1,
        "scope": "checked-native-drain-evidence",
        "traceCount": len(traces),
        "packetCount": sum(len(trace["stages"]) for trace in traces),
        "snapshotCount": len(snapshots),
        "phases": phases,
        "queueCounts": [row["qlen"] for row in qdisc_rows],
        "queueSnapshots": qdisc_rows,
        "oldReceivedAfterInstall": True,
        "install": observations["install"],
        "oldReceiveNs": receive_end,
        "queueIdentityAssumption": "isolated-recipe-and-socket-payloads-not-qdisc-counters",
        "limits": [
            "finite-capture",
            "no-kernel-C-refinement",
            "no-capture-authenticity-proof",
            "no-universal-FIFO-or-liveness-proof",
            "no-drain-time-bound",
        ],
    }


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--capture-dir", type=Path, default=Path("examples/drain/native"))
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
    except (ValueError, OSError, KeyError, TypeError, OverflowError) as error:
        print(f"drain evidence: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
