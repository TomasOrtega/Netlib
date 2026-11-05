"""Compare the compiled campus TCP CLI with independent constructed results.

This manual helper does not send packets or collect captures.
"""

import argparse
import copy
import json
import subprocess
import tempfile
from pathlib import Path

import campus_tcp_reference as reference

ROOT = Path(__file__).resolve().parent.parent
BINARY = ROOT / ".lake/build/bin/netlib"
SCOPE = "campus-tcp-application-path"


def invoke(binary, path, code):
    result = subprocess.run(
        [str(binary), "campus-tcp", str(path), "--json"],
        cwd=ROOT,
        check=False,
        text=True,
        capture_output=True,
    )
    assert result.returncode == code, (result.returncode, result.stdout, result.stderr)
    return result.stdout


def same_fields(actual, expected, path="report"):
    if isinstance(expected, dict):
        assert isinstance(actual, dict), (path, actual, expected)
        for field, value in expected.items():
            assert field in actual, (path, "missing", field)
            same_fields(actual[field], value, path + "." + field)
    elif isinstance(expected, list):
        assert isinstance(actual, list) and len(actual) == len(expected), (path, actual, expected)
        for index, (left, right) in enumerate(zip(actual, expected, strict=True)):
            same_fields(left, right, f"{path}[{index}]")
    else:
        assert actual == expected, (path, actual, expected)


def decision(step):
    if isinstance(step["decision"], dict):
        return step["decision"]
    for field in ("application", "startup"):
        if step.get(field) is not None:
            return step[field]["decision"]
    if not step.get("supported", True):
        return {"kind": "unsupported", "reason": step["decision"]}
    return {"kind": "accepted", "operation": step["event"]["kind"]}


def projection(report):
    return {
        **{
            key: report[key]
            for key in (
                "supported",
                "compliant",
                "evaluatedEvents",
                "final",
                "outputs",
                "services",
                "reads",
                "remainingEvents",
            )
        },
        "decisions": report.get("decisions", [decision(step) for step in report["steps"]]),
    }


def audit_bytes(report, name):
    steps = report["steps"]
    outputs = report["outputs"]
    services = report["services"]
    written = {"client": b"", "server": b""}
    emitted = {"client": b"", "server": b""}
    received = {"client": b"", "server": b""}
    read = {"client": b"", "server": b""}
    pending = {}
    next_ticket = 0
    for index, step in enumerate(steps):
        assert step["index"] == index, (name, index)
        event, verdict = step["event"], decision(step)
        assert step["supported"] == (verdict["kind"] != "unsupported"), (name, index, "supported")
        kind = event["kind"]
        if verdict["kind"] == "accepted" and kind == "write":
            written[event["actor"]] += bytes.fromhex(event["payloadHex"])
        for output in (row for row in outputs if row["index"] == index):
            packet = reference.wire.decode_packet(output["rawIPv4Hex"])
            assert packet.to_dict() == output["decoded"], (name, index, "output decoder")
            emitted[output["actor"]] += packet.segment.payload
            assert written[output["actor"]].startswith(emitted[output["actor"]]), (
                name,
                index,
                "earlier writes",
            )
        if kind == "assign" and verdict["kind"] == "accepted":
            assert outputs[event["output"]]["index"] < index, (name, index, "earlier output")
            pending[next_ticket] = event["output"]
            next_ticket += 1
        if kind == "serve" and verdict["kind"] == "accepted":
            service = next(row for row in services if row["index"] == index)
            source = outputs[pending.pop(event["ticket"])]
            assert source["id"] == service["outputID"], (name, index, "immutable source")
            assert source["rawIPv4Hex"] == service["inputHex"], (name, index, "immutable bytes")
            if service["output"] is not None:
                output = reference.wire.decode_packet(service["output"]["rawIPv4Hex"])
                source_packet = reference.wire.decode_packet(source["rawIPv4Hex"])
                assert output.to_dict() == service["output"]["decoded"], (
                    name,
                    index,
                    "service decoder",
                )
                assert output.segment.payload == source_packet.segment.payload, (
                    name,
                    index,
                    "payload",
                )
                assert output.ttl == source_packet.ttl - 1, (name, index, "TTL")
        if kind == "deliver" and verdict["kind"] == "accepted":
            service = services[event["service"]]
            assert service["index"] < index, (name, index, "earlier service")
            assert service["output"]["rawIPv4Hex"] == event["rawIPv4Hex"], (
                name,
                index,
                "actual emission",
            )
            actor = "server" if service["actor"] == "client" else "client"
            received[actor] += reference.wire.decode_packet(event["rawIPv4Hex"]).segment.payload
        if kind == "read" and verdict["kind"] == "accepted":
            actor = event["actor"]
            read[actor] += bytes.fromhex(step["readHex"])
            assert received[actor].startswith(read[actor]), (name, index, "earlier receipts")
            peer = "server" if actor == "client" else "client"
            assert written[peer].startswith(read[actor]), (name, index, "application prefix")


def expected_assurance(oracle):
    if not oracle["compliant"]:
        return {"status": "failed"}
    if oracle["final"]["passivePhase"] != "ESTABLISHED":
        return {"status": "pendingStartup"}
    totals = {
        actor: {"written": 0, "read": 0, "receives": 0, "emitted": 0}
        for actor in ("client", "server")
    }
    boundary = oracle["final"]["passiveEstablishedAt"]
    for step in oracle["steps"]:
        event, verdict = step["event"], step["decision"]
        if event["kind"] in ("write", "send", "read", "emitAck"):
            if step["index"] <= boundary:
                return {"status": "failed"}
            actor = event["actor"]
            if event["kind"] == "write" and verdict["kind"] == "accepted":
                totals[actor]["written"] += len(bytes.fromhex(event["payloadHex"]))
            totals[actor]["read"] += len(bytes.fromhex(step["readHex"]))
        if event["kind"] == "deliver" and step["before"]["passivePhase"] == "ESTABLISHED":
            service = oracle["services"][event["service"]]
            actor = "server" if service["actor"] == "client" else "client"
            totals[actor]["receives"] += 1
    for output in oracle["outputs"]:
        totals[output["actor"]]["emitted"] += len(
            reference.wire.decode_packet(output["rawIPv4Hex"]).segment.payload
        )
    if any(row["emitted"] >= reference.wire.HALF_SPACE for row in totals.values()):
        return {"status": "failed"}
    return {
        "status": "checked",
        "startupReceipts": 3,
        "clientWrittenBytes": totals["client"]["written"],
        "serverWrittenBytes": totals["server"]["written"],
        "clientReadBytes": totals["client"]["read"],
        "serverReadBytes": totals["server"]["read"],
        "clientReceives": totals["client"]["receives"],
        "serverReceives": totals["server"]["receives"],
    }


def report_case(binary, path, value, expected, name):
    path.write_text(json.dumps(value))
    code = (0 if expected["compliant"] else 1) if expected["supported"] else 2
    report = json.loads(invoke(binary, path, code))
    same_fields(projection(report), expected, name)
    oracle = reference.replay(value)
    same_fields(report["initial"], oracle["initial"], name + ".initial")
    same_fields(report["steps"], oracle["steps"], name + ".steps")
    same_fields(
        report["applicationAssurance"], expected_assurance(oracle), name + ".applicationAssurance"
    )
    assert report["scope"] == SCOPE, name
    assert report["assumptions"] and report["sources"], name
    assert report["evaluatedEvents"] == len(report["steps"]), name
    assert report["inputEvents"] == report["evaluatedEvents"] + len(report["remainingEvents"]), name
    assert [step["event"] for step in report["steps"]] == [
        reference.canonical_event(event) for event in value["events"][: report["evaluatedEvents"]]
    ], name
    audit_bytes(report, name)


def expected_projection(report):
    return {
        **{
            key: report[key]
            for key in (
                "supported",
                "compliant",
                "evaluatedEvents",
                "final",
                "outputs",
                "services",
                "reads",
                "remainingEvents",
            )
        },
        "decisions": [step["decision"] for step in report["steps"]],
    }


def native_spellings(value):
    value = copy.deepcopy(value)
    for config in value["configs"]:
        for item in config["forward"]["nftables"]:
            if "rule" not in item:
                continue
            rule = item["rule"]
            rule["expr"].insert(
                0, {"match": {"left": {"ct": {"key": "state"}}, "op": "in", "right": 79}}
            )
            for expression in rule["expr"]:
                match = expression.get("match", {})
                if match.get("left", {}).get("meta", {}).get("key") == "l4proto":
                    match["left"] = {"payload": {"protocol": "ip", "field": "protocol"}}
                    match["right"] = "tcp"
                if isinstance(match.get("right"), dict) and "prefix" in match["right"]:
                    prefix = match["right"]["prefix"]
                    match["right"] = f"{prefix['addr']}/{prefix['len']}"
    raw = bytes.fromhex(value["authentication"]["events"][1]["raw"])
    padded = raw[:16] + (8).to_bytes(2, "big") + raw[18:] + b"\x00\x01"
    value["authentication"]["events"][1]["raw"] = padded.hex()
    return value


def check(binary=BINARY):
    fixtures = json.loads(reference.FIXTURES.read_text())
    with tempfile.TemporaryDirectory(prefix="netlib-campus-tcp-") as directory:
        path = Path(directory) / "input.json"
        for case in fixtures["cases"]:
            report_case(binary, path, case["input"], case["expected"], case["id"])
        for case in fixtures["inputErrors"]:
            path.write_text(json.dumps(case["input"]))
            output = invoke(binary, path, 2)
            try:
                parsed = json.loads(output)
            except json.JSONDecodeError:
                continue
            assert not isinstance(parsed, dict) or parsed.get("scope") != SCOPE, case["id"]
        for case in fixtures["cases"]:
            value = copy.deepcopy(case["input"])
            for event in value["events"]:
                for field in ("payloadHex", "rawIPv4Hex"):
                    if field in event:
                        event[field] = event[field].upper()
            report_case(binary, path, value, case["expected"], case["id"] + " uppercase")
        case = fixtures["cases"][0]
        report_case(
            binary,
            path,
            native_spellings(case["input"]),
            case["expected"],
            "native predicate spellings and EAP padding",
        )
        stopped = next(
            case
            for case in fixtures["cases"]
            if case["id"] == "startup-copy-stops-before-application-receive"
        )
        value = copy.deepcopy(stopped["input"])
        value["events"].extend(
            [
                {"kind": "write", "actor": "client", "payloadHex": "AaBb"},
                {"kind": "deliver", "service": 0, "rawIPv4Hex": "DdEe", "policyPermitted": True},
            ]
        )
        report_case(
            binary,
            path,
            value,
            expected_projection(reference.replay(value)),
            "unread uppercase hex",
        )
        failed_installs = copy.deepcopy(fixtures["cases"][0]["input"])
        failed_installs["events"] = [
            {"kind": "install", "configuration": "permit"},
            {"kind": "installGuard", "guard": "permit"},
        ]
        report_case(
            binary,
            path,
            failed_installs,
            expected_projection(reference.replay(failed_installs)),
            "failed current install and ingress comparisons",
        )
    print(
        f"Campus TCP examples passed: {len(fixtures['cases'])} traces, {len(fixtures['inputErrors'])} input errors, {len(fixtures['cases'])} uppercase traces, 3 profile variants."
    )

    return {
        "traces": len(fixtures["cases"]),
        "errors": len(fixtures["inputErrors"]),
        "uppercase": len(fixtures["cases"]),
        "variants": 3,
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--binary", type=Path, default=BINARY)
    check(parser.parse_args().binary)


if __name__ == "__main__":
    main()
