"""Check native late-barrier evidence independently of Lean replay outputs."""

import argparse
import ipaddress
import json
from pathlib import Path

from check_lifecycle_capture import (
    EvidenceError,
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
    selected_rule,
)

PHASES = [
    "first-original",
    "first-reply",
    "cached-after-update",
    "cached-after-barrier",
    "fresh-after-delete",
    "fresh-through-barrier",
]
SNAPSHOTS = [
    "opened-state",
    "replied-state",
    "retained-state",
    "barrier-state",
    "deleted-state",
    "fresh-denied-state",
    "fresh-barrier-state",
]


def check_capture(directory):
    directory = Path(directory)
    require(not (directory / "trace-errors.txt").read_text().strip(), "Native trace errors.")
    observations = read_json(directory / "observations.json")
    require([row["phase"] for row in observations] == PHASES, "Missing or reordered phases.")
    traces = parse_trace((directory / "trace.txt").read_text())
    require(len(traces) == len(PHASES), "Extra or missing native packet traces.")
    snapshots = {name: decode_snapshot(read_json(directory / f"{name}.json")) for name in SNAPSHOTS}
    require(len(snapshots["opened-state"]) == 1, "Expected one newly confirmed flow.")
    opened = snapshots["opened-state"][0]
    original, reply = header(opened["original"]), header(opened["reply"])
    wire, restored = reverse(reply), reverse(original)
    require(
        original
        == {
            "source": "192.0.2.2",
            "destination": "203.0.113.2",
            "protocol": 17,
            "sourcePort": 31000,
            "destinationPort": 8080,
        }
        and wire
        == {
            "source": "203.0.113.1",
            "destination": "198.51.100.2",
            "protocol": 17,
            "sourcePort": 40000,
            "destinationPort": 9000,
        },
        "The initial native tuple pair differs from the declared experiment.",
    )
    for name in ("opened-state", "replied-state", "retained-state", "barrier-state"):
        require(len(snapshots[name]) == 1, f"{name}: cached flow missing or additional flow.")
        row = snapshots[name][0]
        for key in ("original", "reply", "originalZone", "replyZone", "id"):
            require(row[key] == opened[key], f"{name}: cached {key} changed.")
        require(row["originalZone"] == row["replyZone"] == 0, "Expected zone zero.")
        require(row["status"] & 440 == 440, f"{name}: confirmation or completed NAT flag missing.")
        require(row["status"] & ~1470 == 0, f"{name}: unsupported ordinary status.")
        require(
            bool(row["status"] & 2) == (name != "opened-state"), "Seen-reply evidence mismatch."
        )
    for name in ("deleted-state", "fresh-denied-state", "fresh-barrier-state"):
        require(not snapshots[name], f"{name}: unexpected visible confirmed flow.")
    documents = {
        name: read_json(directory / f"{name}.json")
        for name in (
            "nat-initial",
            "nat-changed",
            "forward-initial",
            "forward-established-only",
            "forward-fresh-allowed",
            "barrier-open",
            "barrier-closed",
        )
    }
    trace_names = ("netlib_trace", "trace")
    destination_names = ("netlib_nat", "destination")
    source_names = ("netlib_nat", "source")
    forward_names = ("netlib_filter", "forward")
    barrier_names = ("netlib_barrier", "barrier")
    for document in documents.values():
        require(document["nftables"][0]["metainfo"]["version"] == "1.1.3", "Wrong nft version.")
        require(
            document["nftables"][0]["metainfo"]["json_schema_version"] == 1, "Wrong nft schema."
        )
    for name, key, kind, hook, priority in (
        ("nat-initial", destination_names, "nat", "prerouting", -100),
        ("nat-initial", source_names, "nat", "postrouting", 100),
        ("nat-changed", destination_names, "nat", "prerouting", -100),
        ("nat-changed", source_names, "nat", "postrouting", 100),
        ("forward-initial", forward_names, "filter", "forward", 0),
        ("forward-established-only", forward_names, "filter", "forward", 0),
        ("forward-fresh-allowed", forward_names, "filter", "forward", 0),
        ("barrier-open", barrier_names, "filter", "postrouting", 110),
        ("barrier-closed", barrier_names, "filter", "postrouting", 110),
    ):
        chain, _ = native_chain(documents[name], *key)
        require(
            (chain["type"], chain["hook"], chain["prio"]) == (kind, hook, priority),
            "Hook order mismatch.",
        )
    barrier, rules = native_chain(documents["barrier-closed"], *barrier_names)
    require(barrier["policy"] == "accept" and len(rules) == 1, "Unexpected barrier structure.")
    require(
        rules[0]["expr"]
        == [
            {
                "match": {
                    "op": "==",
                    "left": {"payload": {"protocol": "ip", "field": "daddr"}},
                    "right": "198.51.100.2",
                }
            },
            {"match": {"op": "==", "left": {"meta": {"key": "l4proto"}}, "right": 17}},
            {"drop": None},
        ],
        "The barrier must select every UDP port at the backend address.",
    )
    _, changed_source = selected_rule(documents["nat-changed"], *source_names, "new", original)
    require(
        changed_source == {"snat": {"addr": "203.0.113.1", "port": 40001}}, "SNAT update missing."
    )
    routes = read_json(directory / "routes.json")
    phases = []
    configs = ["initial", "initial", "tightened", "barrier", "barrier", "fresh-allowed"]
    for index, (trace, observation, config) in enumerate(
        zip(traces, observations, configs, strict=True)
    ):
        phase = observation["phase"]
        sent = header(observation["sent"]["packet"])
        if phase == "first-original":
            require(sent == original, "The first trace differs from the confirmed original.")
        if phase == "fresh-after-delete":
            require(sent == original, "The fresh attempt differs from the deleted original.")
        is_reply = phase == "first-reply"
        fresh = phase in ("first-original", "fresh-after-delete", "fresh-through-barrier")
        state = "new" if fresh else "established"
        forward_drop = phase == "fresh-after-delete"
        late_drop = phase in ("cached-after-barrier", "fresh-through-barrier")
        stages = trace["stages"]
        check_trace_stage(stages[0])
        require(stages[0]["packet"] == sent, f"{phase}: trace input differs from socket input.")
        expected = [trace_names] + ([destination_names] if fresh else []) + [forward_names]
        if not forward_drop:
            expected += ([source_names] if fresh else []) + [barrier_names]
        require(
            [(stage["table"], stage["chain"]) for stage in stages] == expected,
            f"{phase}: unexpected hook visits.",
        )
        if fresh:
            active_nat = documents["nat-initial" if index == 0 else "nat-changed"]
            destination_stage = next(
                stage for stage in stages if (stage["table"], stage["chain"]) == destination_names
            )
            require(destination_stage["packet"] == sent, "Destination NAT input mismatch.")
            check_rule_trace(destination_stage, active_nat, state)
            _, nat = selected_rule(active_nat, *destination_names, state, sent)
            require(set(nat) == {"dnat"}, "Missing fixed DNAT target.")
            after_destination = {
                **sent,
                "destination": nat["dnat"]["addr"],
                "destinationPort": nat["dnat"]["port"],
            }
        else:
            require(sent == (reply if is_reply else original), "Cached input tuple changed.")
            after_destination = (
                {
                    **reply,
                    "destination": original["source"],
                    "destinationPort": original["sourcePort"],
                }
                if is_reply
                else {
                    **original,
                    "destination": wire["destination"],
                    "destinationPort": wire["destinationPort"],
                }
            )
        forward = next(
            stage for stage in stages if (stage["table"], stage["chain"]) == forward_names
        )
        require(
            forward["packet"] == after_destination,
            "Forward input is not the expected post-DNAT packet.",
        )
        matching = [
            route
            for route in routes
            if ipaddress.IPv4Address(after_destination["destination"])
            in ipaddress.IPv4Network(route["dst"])
        ]
        require(matching, "No route for translated destination.")
        width = max(ipaddress.IPv4Network(route["dst"]).prefixlen for route in matching)
        matching = [
            route for route in matching if ipaddress.IPv4Network(route["dst"]).prefixlen == width
        ]
        require(
            len(matching) == 1 and matching[0]["dev"] == forward["oif"],
            "Route/export interface mismatch.",
        )
        filter_name = (
            "forward-initial"
            if index < 2
            else "forward-fresh-allowed"
            if index == 5
            else "forward-established-only"
        )
        check_filter(forward, documents[filter_name], state, "drop" if forward_drop else "accept")
        after_source = None
        if not forward_drop:
            if fresh:
                source_stage = next(
                    stage for stage in stages if (stage["table"], stage["chain"]) == source_names
                )
                require(source_stage["packet"] == after_destination, "Source NAT input mismatch.")
                check_rule_trace(source_stage, active_nat, state)
                _, nat = selected_rule(active_nat, *source_names, state, after_destination)
                require(set(nat) == {"snat"}, "Missing fixed SNAT target.")
                after_source = {
                    **after_destination,
                    "source": nat["snat"]["addr"],
                    "sourcePort": nat["snat"]["port"],
                }
            else:
                after_source = restored if is_reply else wire
            require(
                stages[-1]["packet"] == after_source,
                "Barrier did not see the expected post-SNAT packet.",
            )
            check_filter(
                stages[-1],
                documents["barrier-closed" if index >= 3 else "barrier-open"],
                state,
                "drop" if late_drop else "accept",
            )
        for stage in stages:
            require(
                stage["iif"] == ("outside0" if is_reply else "inside0"),
                "Unexpected input interface.",
            )
            require(stage["ipId"] == stages[0]["ipId"], "Packet ID changed within one trace.")
            if stage["oif"] is not None:
                require(
                    stage["oif"] == ("inside0" if is_reply else "outside0"),
                    "Unexpected output interface.",
                )
        received = observation["received"]
        output = None if forward_drop or late_drop else after_source
        if output is None:
            require(received is None, "A traced drop reached the application.")
        else:
            require(
                received is not None and header(received["packet"]) == output,
                "Socket output differs from traced output.",
            )
            require(
                received["payload"] == observation["sent"]["payload"], "Socket payload changed."
            )
        expected_snapshot = [
            "opened-state",
            "replied-state",
            "retained-state",
            "barrier-state",
            "fresh-denied-state",
            "fresh-barrier-state",
        ][index]
        require(
            observation["state"] == expected_snapshot,
            "Observation points to the wrong state capture.",
        )
        phases.append(
            {
                "phase": phase,
                "config": config,
                "snapshot": expected_snapshot + ".json",
                "traceId": trace["id"],
                "input": sent,
                "state": state,
                "fresh": fresh,
                "afterDestination": after_destination,
                "afterSource": after_source,
                "nextHop": "client" if is_reply else "server",
                "disposition": "forwardDrop"
                if forward_drop
                else "lateDrop"
                if late_drop
                else "forwarded",
                "output": output,
                "fieldEvidence": {
                    "input": "trace-packet-and-socket-send",
                    "afterDestination": "trace-forward-packet",
                    "afterSource": "trace-postrouting-packet" if after_source else "not-reached",
                    "state": "exported-matching-rule-and-ordinary-profile-inference",
                    "fresh": "visible-table-and-ordinary-profile-assumption",
                    "output": "trace-verdict-and-socket-observation",
                    "nextHop": "trace-oif-with-declared-interface-binding",
                },
                "stages": stages,
            }
        )
    return {
        "schema": 1,
        "scope": "checked-native-revocation-evidence",
        "traceCount": len(traces),
        "packetCount": sum(len(trace["stages"]) for trace in traces),
        "snapshotCount": len(snapshots),
        "phases": phases,
        "erase": {
            "beforePhase": "fresh-after-delete",
            "packet": original,
            "zone": 0,
            "snapshot": "deleted-state.json",
        },
    }


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("directory", type=Path)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args(argv)
    try:
        result = check_capture(args.directory)
        text = json.dumps(result, indent=2) + "\n"
        if args.output:
            args.output.write_text(text)
        else:
            print(text, end="")
    except (EvidenceError, KeyError, TypeError, ValueError, OSError) as error:
        parser.exit(2, f"Revocation evidence error: {error}\n")


if __name__ == "__main__":
    main()
