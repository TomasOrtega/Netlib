"""Compare ACK reactions with independent packets, windows, and causal history.

This manual helper does not compile Lean or send packets.
"""

import argparse
import copy
import json
import tempfile
from pathlib import Path

import campus_tcp_ack_reference as reference
import check_campus_tcp_examples as common
import check_campus_tcp_transfer_examples as transfer_checks
import check_tcp_recovery_examples as recovery_checks

BINARY = common.BINARY


def expected_ack(oracle):
    endpoints = {actor: oracle["final"][actor] for actor in ("client", "server")}
    if not any(state is not None and "ackReaction" in state for state in endpoints.values()):
        return None
    value = {"scope": "local-ack-generation"}
    if not oracle["compliant"]:
        return {**value, "status": "failed"}
    pending = 0
    for actor, state in endpoints.items():
        work = None if state is None or "ackReaction" not in state else state["ackReaction"]["work"]
        value[actor + "Enabled"] = work is not None
        value[actor + "Causes"] = 0 if work is None else work["nextID"]
        value[actor + "Discharges"] = 0 if work is None else len(work["completed"])
        value[actor + "Pending"] = 0 if work is None else len(work["pending"])
        pending += value[actor + "Pending"]
    return {**value, "status": "pending" if pending else "checked"}


def check_ack_assurance(report, oracle, name):
    expected = expected_ack(oracle)
    if expected is None:
        assert "ackAssurance" not in report, (name, "disabled ACK assurance")
        return
    assert "ackAssurance" in report, (name, "missing ackAssurance")
    actual = report["ackAssurance"]
    keys = set(expected) | ({"reason"} if expected["status"] == "failed" else set())
    assert isinstance(actual, dict) and set(actual) == keys, (name, "ACK assurance fields", actual)
    for key, value in expected.items():
        assert type(actual[key]) is type(value) and actual[key] == value, (
            name,
            "ackAssurance." + key,
            actual[key],
            value,
        )
    if expected["status"] == "failed":
        assert isinstance(actual["reason"], str) and actual["reason"].strip(), (
            name,
            "ACK failure diagnostic",
        )


def candidate(endpoint, reaction):
    free = endpoint["core"]["capacity"] - len(bytes.fromhex(endpoint["core"]["receivedHex"]))
    width = reaction["advertisement"]["edge"] - reaction["advertisement"]["frontier"]
    threshold = min((endpoint["core"]["capacity"] + 1) // 2, endpoint["effectiveMSS"])
    return free if free - width >= threshold else width


def audit(report, name):
    recovery_checks.audit(report, name)
    issued = {actor: {} for actor in ("client", "server")}
    retired = {actor: set() for actor in issued}
    transport_started = {actor: False for actor in issued}
    offers = {}
    for output in report["outputs"]:
        packet = reference.wire.decode_packet(output["rawIPv4Hex"])
        if packet.segment.flags & 2:
            values = packet.segment.to_dict()["mssValues"]
            assert len(values) <= 1, (name, "startup receive offer")
            offers[output["actor"]] = (
                {"kind": "present", "value": values[0]} if values else {"kind": "absent"}
            )
    for step in report["steps"]:
        index, event, decision = step["index"], step["event"], step["decision"]
        operation = event["kind"]
        accepted = decision["kind"] == "accepted"
        receiving = None
        if operation == "deliver" and step["before"]["passivePhase"] == "ESTABLISHED":
            service = report["services"][event["service"]]
            receiving = "server" if service["actor"] == "client" else "client"
        for actor in issued:
            before, after = step["before"][actor], step["state"][actor]
            previous = None if before is None else before.get("ackReaction")
            current = None if after is None else after.get("ackReaction")
            if previous is None:
                if current is not None:
                    assert operation == "enableAck" and event["actor"] == actor and accepted
                    assert not transport_started[actor], (name, index, "historical activation")
                    assert after["localReceiveMSS"] == offers[actor], (name, index, "own offer")
                    assert current["rmss"] == offers[actor].get("value", 536)
                    assert current["origin"] == after["core"]["receiveNext"]
                    assert current["advertisement"]["frontier"] == 0
                    assert current["advertisement"]["edge"] == after["core"]["capacity"]
                continue
            assert current is not None, (name, index, "persistent activation")
            for endpoint, reaction in ((before, previous), (after, current)):
                advertisement = reaction["advertisement"]
                free = endpoint["core"]["capacity"] - len(
                    bytes.fromhex(endpoint["core"]["receivedHex"])
                )
                assert advertisement["free"] == free
                assert 0 <= advertisement["window"] <= free
                assert advertisement["window"] == advertisement["edge"] - advertisement["frontier"]
                assert advertisement["candidate"] == candidate(endpoint, reaction)
                assert (
                    reaction["origin"] + advertisement["frontier"]
                ) % reference.MODULUS == endpoint["core"]["receiveNext"]
                work = reaction["work"]
                assert work["credit"] == len(work["pending"])
                assert work["pendingDue"] == min(
                    (row["due"] for row in work["pending"]), default=None
                )
            old_work, work = previous["work"], current["work"]
            now = before["recovery"]["now"]
            cause_kind = None
            received = 0
            if receiving == actor:
                packet = reference.wire.decode_packet(event["rawIPv4Hex"])
                if accepted and packet.segment.payload:
                    cause_kind = "data"
                    received = len(packet.segment.payload)
                elif decision == {"kind": "reject", "reason": "input.sequence"}:
                    cause_kind = "sequence"
            if operation == "read" and event["actor"] == actor and accepted:
                if candidate(after, current) > candidate(before, previous):
                    cause_kind = "window"
            assert work["nextID"] == old_work["nextID"] + (cause_kind is not None), (
                name,
                index,
                "actual cause",
            )
            assert (
                current["advertisement"]["frontier"]
                == previous["advertisement"]["frontier"] + received
            )
            if cause_kind is not None:
                cause = next(row for row in work["pending"] if row["id"] == old_work["nextID"])
                demand = cause["demand"]
                assert cause["id"] not in issued[actor]
                assert demand["kind"] == cause_kind and demand["bytes"] == received
                assert demand["position"] == current["advertisement"]["frontier"]
                assert demand["cursor"] == after["core"]["receiveNext"]
                assert cause["issuedAt"] == now
                immediate = (
                    cause_kind != "data"
                    or previous["fullSegments"] + (received >= previous["rmss"]) >= 2
                    or previous["dataBytes"] + received >= 2 * previous["rmss"]
                )
                assert cause["due"] == now + (0 if immediate else 499)
                if cause_kind == "window":
                    assert demand["minimumEdge"] == demand["position"] + candidate(after, current)
                else:
                    assert demand["minimumEdge"] == 0
                issued[actor][cause["id"]] = (index, cause)
            outputs = [
                row for row in report["outputs"] if row["index"] == index and row["actor"] == actor
            ]
            assert len(outputs) <= 1
            if outputs:
                output = reference.wire.decode_packet(outputs[0]["rawIPv4Hex"])
                assert output.segment.acknowledgment == before["core"]["receiveNext"]
                assert output.segment.window == candidate(before, previous)
                assert (
                    current["advertisement"]["edge"]
                    == previous["advertisement"]["frontier"] + output.segment.window
                )
                assert (current["fullSegments"], current["dataBytes"]) == (0, 0)
                if old_work["pending"]:
                    assert work["nextDischarge"] == old_work["nextDischarge"] + 1
                    completion = work["completed"][-1]
                    assert completion["causes"] == old_work["pending"]
                    assert completion["time"] == now
                    assert completion["output"] == {
                        "cursor": output.segment.acknowledgment,
                        "position": previous["advertisement"]["frontier"],
                        "window": output.segment.window,
                    }
                    assert work["pending"] == []
                    for cause in completion["causes"]:
                        earlier, actual = issued[actor][cause["id"]]
                        assert earlier < index and cause == actual, (name, index, "earlier issuer")
                        assert cause["id"] not in retired[actor], (name, index, "one discharge")
                        assert cause["issuedAt"] <= now <= cause["due"], (
                            name,
                            index,
                            "same-clock deadline",
                        )
                        assert cause["demand"]["position"] <= completion["output"]["position"]
                        assert (
                            cause["demand"]["minimumEdge"]
                            <= completion["output"]["position"] + output.segment.window
                        )
                        retired[actor].add(cause["id"])
                else:
                    assert outputs[0]["kind"] in ("send", "retry"), (
                        name,
                        index,
                        "no spare pure response",
                    )
                    assert work["completed"] == old_work["completed"]
            else:
                assert current["advertisement"]["edge"] == previous["advertisement"]["edge"]
                assert work["completed"] == old_work["completed"]
            if operation == "advanceClock" and event["actor"] == actor and accepted:
                assert old_work["pendingDue"] is None or event["millis"] <= old_work["pendingDue"]
        if operation == "send" and step["before"]["passivePhase"] == "ESTABLISHED":
            transport_started[event["actor"]] = True
        if receiving is not None:
            transport_started[receiving] = True


def report_case(binary, path, value, expected, name):
    path.write_text(json.dumps(value))
    code = (0 if expected["compliant"] else 1) if expected["supported"] else 2
    report = json.loads(recovery_checks.invoke(binary, path, code, name))
    oracle = reference.replay(value)
    common.same_fields(reference.projection(report), expected, name)
    for key in ("initial", "steps", "final", "outputs", "services", "reads", "remainingEvents"):
        common.same_fields(report[key], oracle[key], name + "." + key)
    common.same_fields(
        report["applicationAssurance"],
        recovery_checks.expected_assurance(oracle),
        name + ".applicationAssurance",
    )
    if "standby" in value:
        common.same_fields(
            report["transferAssurance"],
            transfer_checks.expected_transfer(oracle),
            name + ".transferAssurance",
        )
    else:
        assert "transferAssurance" not in report
    check_ack_assurance(report, oracle, name)
    assert report["scope"] == common.SCOPE and report["assumptions"] and report["sources"]
    assert report["inputEvents"] == len(value["events"])
    assert report["evaluatedEvents"] == len(report["steps"])
    assert report["inputEvents"] == report["evaluatedEvents"] + len(report["remainingEvents"])
    audit(report, name)


def check(binary=BINARY):
    data = reference.load_fixtures()
    with tempfile.TemporaryDirectory(prefix="netlib-tcp-ack-") as directory:
        path = Path(directory) / "input.json"
        for case in data["cases"]:
            oracle = reference.replay(case["input"])
            assert reference.projection(oracle) == case["expected"], case["id"]
            report_case(binary, path, case["input"], case["expected"], case["id"])
        for case in data["inputErrors"]:
            path.write_text(json.dumps(case["input"]))
            output = recovery_checks.invoke(binary, path, 2, case["id"])
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
        report_case(binary, path, value, data["cases"][0]["expected"], "uppercase ACK")
    counts = {"traces": len(data["cases"]), "inputErrors": len(data["inputErrors"]), "uppercase": 1}
    print("TCP ACK comparisons passed: " + json.dumps(counts, sort_keys=True))
    return counts


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--binary", type=Path, default=BINARY)
    check(parser.parse_args().binary)


if __name__ == "__main__":
    main()
