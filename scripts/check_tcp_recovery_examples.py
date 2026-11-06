"""Compare bounded recovery with independent bytes, timing, and stream ranges.

This manual helper does not compile Lean or send packets.
"""

import argparse
import copy
import json
import subprocess
import tempfile
from pathlib import Path

import campus_tcp_recovery_reference as reference
import check_campus_tcp_examples as common
import check_campus_tcp_transfer_examples as transfer_checks

BINARY = common.BINARY


def invoke(binary, path, code, name):
    result = subprocess.run(
        [str(binary), "campus-tcp", str(path), "--json"],
        cwd=common.ROOT,
        check=False,
        text=True,
        capture_output=True,
    )
    if result.returncode != code:
        try:
            value = json.loads(result.stdout)
            last = value.get("steps", [])[-1:]
            detail = {
                "supported": value.get("supported"),
                "compliant": value.get("compliant"),
                "last": [(row["index"], row["decision"]) for row in last],
                "applicationAssurance": value.get("applicationAssurance"),
                "transferAssurance": value.get("transferAssurance"),
            }
        except (json.JSONDecodeError, AttributeError):
            detail = result.stdout[:1000]
        raise AssertionError((name, "exit", result.returncode, code, detail, result.stderr[:1000]))
    return result.stdout


def expected_assurance(oracle):
    if not oracle["compliant"]:
        return {"status": "failed"}
    if oracle["final"]["passivePhase"] != "ESTABLISHED":
        return {"status": "pendingStartup"}
    totals = {
        actor: {"written": 0, "read": 0, "receives": 0, "unique": 0}
        for actor in ("client", "server")
    }
    boundary = oracle["final"]["passiveEstablishedAt"]
    for step in oracle["steps"]:
        event, verdict = step["event"], step["decision"]
        if event["kind"] in ("write", "send", "read", "emitAck", *reference.EVENTS):
            if step["index"] <= boundary:
                return {"status": "failed"}
            actor = event["actor"]
            if verdict["kind"] == "accepted":
                if event["kind"] == "write":
                    totals[actor]["written"] += len(bytes.fromhex(event["payloadHex"]))
                if event["kind"] == "send":
                    totals[actor]["unique"] += event["count"]
            totals[actor]["read"] += len(bytes.fromhex(step["readHex"]))
        if event["kind"] == "deliver" and step["before"]["passivePhase"] == "ESTABLISHED":
            service = oracle["services"][event["service"]]
            actor = "server" if service["actor"] == "client" else "client"
            totals[actor]["receives"] += 1
    if any(row["unique"] >= reference.wire.HALF_SPACE for row in totals.values()):
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


def audit(report, name):
    common.audit_custody(report, name)
    written, stream, received, read = (
        {actor: b"" for actor in ("client", "server")} for _ in range(4)
    )
    offsets = {actor: 0 for actor in stream}
    originals, pending = {}, {}
    next_ticket = 0
    for step in report["steps"]:
        index, event, verdict = step["index"], step["event"], step["decision"]
        kind = event["kind"]
        actor = event.get("actor")
        accepted = verdict["kind"] == "accepted"
        if accepted and kind == "write":
            written[actor] += bytes.fromhex(event["payloadHex"])
        if accepted and kind == "enableRecovery":
            offsets[actor] = len(stream[actor])
        for output in (row for row in report["outputs"] if row["index"] == index):
            actor = output["actor"]
            packet = reference.wire.decode_packet(output["rawIPv4Hex"])
            assert packet.to_dict() == output["decoded"], (name, index, "output decoder")
            payload = packet.segment.payload
            attempt = output.get("attempt")
            if attempt is None:
                stream[actor] += payload
            else:
                before = step["before"][actor]
                recovery = before["recovery"]
                assert attempt["clockMillis"] == recovery["now"], (name, index, "local clock")
                assert attempt["count"] == len(payload), (name, index, "attempt count")
                start = offsets[actor] + attempt["start"]
                if attempt["kind"] == "original":
                    assert start == len(stream[actor]), (name, index, "new range")
                    originals[actor, attempt["originalID"]] = (start, payload, index)
                    stream[actor] += payload
                elif attempt["kind"] == "retry":
                    origin, original, earlier = originals[actor, attempt["originalID"]]
                    assert earlier < index and origin <= start, (name, index, "earlier original")
                    assert original[start - origin : start - origin + len(payload)] == payload, (
                        name,
                        index,
                        "original slice",
                    )
                    assert stream[actor][start : start + len(payload)] == payload, (
                        name,
                        index,
                        "stream slice",
                    )
                    assert packet.segment.sequence == before["core"]["sendUna"], (
                        name,
                        index,
                        "retry sequence",
                    )
                    assert step["state"][actor]["core"] == before["core"], (
                        name,
                        index,
                        "unique retry state",
                    )
                    assert step["state"][actor]["pendingHex"] == before["pendingHex"], (
                        name,
                        index,
                        "pending retry state",
                    )
                else:
                    assert (
                        attempt["kind"] == "ack" and not payload and attempt["originalID"] is None
                    )
            assert written[actor].startswith(stream[actor]), (name, index, "earlier writes")
        if kind == "assign" and accepted:
            produced = report["outputs"][event["output"]]
            assert produced["index"] < index
            transfer = step["before"].get("transfer")
            assert transfer is None or not transfer["paused"]
            pending[next_ticket] = (
                produced,
                "primary" if transfer is None else transfer["owners"][produced["actor"]],
                0 if transfer is None else transfer["routeEpoch"],
            )
            next_ticket += 1
        if kind == "serve" and step["supported"]:
            produced, gateway, epoch = pending.pop(event["ticket"])
            service = step["service"]
            assert (service.get("gateway", "primary"), service.get("routeEpoch", 0)) == (
                gateway,
                epoch,
            )
            assert (
                service["outputID"] == produced["id"]
                and service["inputHex"] == produced["rawIPv4Hex"]
            )
            if service["output"] is not None:
                output = reference.wire.decode_packet(service["output"]["rawIPv4Hex"])
                source = reference.wire.decode_packet(produced["rawIPv4Hex"])
                assert output.to_dict() == service["output"]["decoded"]
                assert (
                    output.segment.payload,
                    output.segment.sequence,
                    output.segment.options,
                ) == (source.segment.payload, source.segment.sequence, source.segment.options)
                assert output.ttl == source.ttl - 1
            if gateway == "primary" and "transfer" in step["before"]:
                assert not step["before"]["transfer"]["primarySealed"]
        if kind == "deliver":
            service = report["services"][event["service"]]
            assert service["index"] < index and service["output"] is not None
            assert event["rawIPv4Hex"] == service["output"]["rawIPv4Hex"]
            actor = "server" if service["actor"] == "client" else "client"
            if accepted:
                payload = reference.wire.decode_packet(event["rawIPv4Hex"]).segment.payload
                received[actor] += payload
        if kind == "read" and accepted:
            actor = event["actor"]
            read[actor] += bytes.fromhex(step["readHex"])
            assert received[actor].startswith(read[actor]), (name, index, "earlier receipts")
            peer = "server" if actor == "client" else "client"
            assert written[peer].startswith(read[actor]), (name, index, "read prefix")
        if kind == "timeout" and not accepted:
            assert step["state"][event["actor"]] == step["before"][event["actor"]]


def report_case(binary, path, value, expected, name):
    path.write_text(json.dumps(value))
    code = (0 if expected["compliant"] else 1) if expected["supported"] else 2
    report = json.loads(invoke(binary, path, code, name))
    oracle = reference.replay(value)
    common.same_fields(reference.projection(report), expected, name)
    for key in ("initial", "steps", "final", "outputs", "services", "reads", "remainingEvents"):
        common.same_fields(report[key], oracle[key], name + "." + key)
    common.same_fields(
        report["applicationAssurance"], expected_assurance(oracle), name + ".applicationAssurance"
    )
    if "standby" in value:
        common.same_fields(
            report["transferAssurance"],
            transfer_checks.expected_transfer(oracle),
            name + ".transferAssurance",
        )
    else:
        assert "transferAssurance" not in report
    assert report["scope"] == common.SCOPE and report["assumptions"] and report["sources"]
    assert report["inputEvents"] == len(value["events"])
    assert report["evaluatedEvents"] == len(report["steps"])
    assert report["inputEvents"] == report["evaluatedEvents"] + len(report["remainingEvents"])
    audit(report, name)


def check(binary=BINARY):
    data = reference.load_fixtures()
    with tempfile.TemporaryDirectory(prefix="netlib-tcp-recovery-") as directory:
        path = Path(directory) / "input.json"
        for case in data["cases"]:
            oracle = reference.replay(case["input"])
            assert reference.projection(oracle) == case["expected"], case["id"]
            report_case(binary, path, case["input"], case["expected"], case["id"])
        for case in data["inputErrors"]:
            path.write_text(json.dumps(case["input"]))
            output = invoke(binary, path, 2, case["id"])
            try:
                parsed = json.loads(output)
            except json.JSONDecodeError:
                continue
            assert not isinstance(parsed, dict) or parsed.get("scope") != common.SCOPE, case["id"]
        value = copy.deepcopy(data["input"])
        for event in value["events"]:
            for key in ("payloadHex", "rawIPv4Hex"):
                if key in event:
                    event[key] = event[key].upper()
        report_case(binary, path, value, data["cases"][0]["expected"], "uppercase recovery")
    counts = {"traces": len(data["cases"]), "inputErrors": len(data["inputErrors"]), "uppercase": 1}
    print("TCP recovery comparisons passed: " + json.dumps(counts, sort_keys=True))
    return counts


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--binary", type=Path, default=BINARY)
    check(parser.parse_args().binary)


if __name__ == "__main__":
    main()
