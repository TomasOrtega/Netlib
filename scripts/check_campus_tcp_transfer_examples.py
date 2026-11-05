"""Compare planned TCP transfer reports with independent constructed evidence.

This manual helper does not compile Lean or send packets.
"""

import argparse
import copy
import json
import tempfile
from pathlib import Path

import campus_tcp_transfer_reference as reference
import check_campus_tcp_examples as common

BINARY = common.BINARY


def expected_transfer(oracle):
    if not oracle["compliant"]:
        return {"status": "failed"}
    transfer = oracle["final"]["transfer"]
    ready = (
        transfer["primaryFenced"]
        and not transfer["paused"]
        and set(transfer["owners"].values()) == {"standby"}
    )
    if not ready:
        return {"status": "pending"}
    cache = transfer["cache"]
    source_preserved = all(
        oracle["final"]["gateways"]["primary"][key] == cache[key]
        for key in ("records", "confirmed", "admission", "historyTransitions")
    )
    if not source_preserved:
        return {"status": "failed"}

    def time(kind, actor=None):
        return next(
            step["index"]
            for step in oracle["steps"]
            if step["event"]["kind"] == kind
            and (actor is None or step["event"].get("actor") == actor)
        )

    installation = transfer["installation"]
    return {
        "status": "checked",
        "pausedAt": time("pause"),
        "stagedAt": installation["stagedAt"],
        "installedAt": installation["index"],
        "clientRouteAt": time("switchRoute", "client"),
        "serverRouteAt": time("switchRoute", "server"),
        "fencedAt": time("fencePrimary"),
        "resumedAt": time("resume"),
        "historyTransitions": installation["historyTransitions"],
        "sourcePreserved": source_preserved,
    }


def audit_transfer(report, name):
    common.audit_bytes(report, name)
    outputs = report["outputs"]
    pending = {}
    next_ticket = 0
    for step in report["steps"]:
        event = step["event"]
        if event["kind"] == "assign":
            actor = outputs[event["output"]]["actor"]
            transfer = step["before"]["transfer"]
            assert not transfer["paused"], (name, step["index"], "paused assignment")
            pending[next_ticket] = (transfer["owners"][actor], transfer["routeEpoch"])
            next_ticket += 1
        elif event["kind"] == "serve" and step["supported"]:
            gateway, epoch = pending.pop(event["ticket"])
            service = step["service"]
            assert (service["gateway"], service["routeEpoch"]) == (gateway, epoch), (
                name,
                step["index"],
                "immutable gateway",
            )
            if gateway == "primary":
                assert not step["before"]["transfer"]["primarySealed"], (
                    name,
                    step["index"],
                    "sealed primary",
                )
            else:
                assert (
                    step["before"]["transfer"]["installed"]
                    and not step["before"]["transfer"]["paused"]
                ), (name, step["index"], "standby readiness")
        elif event["kind"] == "installCheckpoint":
            before, after = step["before"], step["state"]
            cache = before["transfer"]["cache"]
            source, target = after["gateways"]["primary"], after["gateways"]["standby"]
            for key in ("records", "confirmed", "admission", "historyTransitions"):
                assert source[key] == target[key] == cache[key], (name, step["index"], key)
            assert not any(gateway == "primary" for gateway, _epoch in pending.values()), (
                name,
                step["index"],
                "pending primary ticket",
            )
            assert after["transfer"]["primarySealed"], (name, step["index"], "source seal")


def report_case(binary, path, value, expected, name):
    path.write_text(json.dumps(value))
    code = (0 if expected["compliant"] else 1) if expected["supported"] else 2
    report = json.loads(common.invoke(binary, path, code))
    common.same_fields(reference.projection(report), expected, name)
    oracle = reference.replay(value)
    common.same_fields(report["initial"], oracle["initial"], name + ".initial")
    common.same_fields(report["steps"], oracle["steps"], name + ".steps")
    common.same_fields(report["final"], oracle["final"], name + ".final")
    common.same_fields(
        report["applicationAssurance"],
        common.expected_assurance(oracle),
        name + ".applicationAssurance",
    )
    common.same_fields(
        report["transferAssurance"], expected_transfer(oracle), name + ".transferAssurance"
    )
    assert report["scope"] == common.SCOPE and report["assumptions"] and report["sources"], name
    assert report["inputEvents"] == len(value["events"]), name
    assert report["evaluatedEvents"] == len(report["steps"]), name
    assert report["inputEvents"] == report["evaluatedEvents"] + len(report["remainingEvents"]), name
    audit_transfer(report, name)


def check(binary=BINARY):
    data = reference.load_fixtures()
    with tempfile.TemporaryDirectory(prefix="netlib-campus-tcp-transfer-") as directory:
        path = Path(directory) / "input.json"
        for case in data["cases"]:
            report_case(binary, path, case["input"], case["expected"], case["id"])
        for case in data["inputErrors"]:
            path.write_text(json.dumps(case["input"]))
            result = common.invoke(binary, path, 2)
            try:
                report = json.loads(result)
            except json.JSONDecodeError:
                continue
            assert not isinstance(report, dict) or report.get("scope") != common.SCOPE, case["id"]
        for case in data["cases"]:
            value = copy.deepcopy(case["input"])
            for event in value["events"]:
                for field in ("payloadHex", "rawIPv4Hex"):
                    if field in event:
                        event[field] = event[field].upper()
            report_case(binary, path, value, case["expected"], case["id"] + " uppercase")
        legacy = json.loads(reference.base.FIXTURES.read_text())["cases"][0]
        common.report_case(
            binary, path, legacy["input"], legacy["expected"], "legacy without standby"
        )
        path.write_text(json.dumps(legacy["input"]))
        old = json.loads(common.invoke(binary, path, 0))
        assert (
            "transferAssurance" not in old
            and "gateways" not in old["final"]
            and "transfer" not in old["final"]
        )
        assert all(
            "gateway" not in service and "routeEpoch" not in service for service in old["services"]
        )
    counts = {
        "traces": len(data["cases"]),
        "inputErrors": len(data["inputErrors"]),
        "uppercase": len(data["cases"]),
        "legacy": 1,
    }
    print("Campus TCP transfer comparisons passed: " + json.dumps(counts, sort_keys=True))
    return counts


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--binary", type=Path, default=BINARY)
    check(parser.parse_args().binary)


if __name__ == "__main__":
    main()
