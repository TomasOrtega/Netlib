"""Compare receive-gap packets, storage, origins, clocks, and campus execution.

This manual helper does not compile Lean or send packets.
"""

import argparse
import copy
import json
import subprocess
import tempfile
from dataclasses import replace
from pathlib import Path

import campus_tcp_gap_reference as reference
import check_campus_tcp_examples as common
import check_campus_tcp_transfer_examples as transfer_checks
import check_tcp_ack_examples as ack_checks
import check_tcp_mss_examples as mss_checks
import check_tcp_recovery_examples as recovery_checks

BINARY = common.BINARY
ACTORS = ("client", "server")
RUN_FIELDS = {"position", "end", "receiptID", "payloadHex", "header", "segment", "receivedAt"}
STORE_FIELDS = {"frontier", "nextID", "heldBytes", "reservationFree", "physicalFree", "held"}
FRAME_FIELDS = {"receiptID", "novelBytes", "releasedHex", "releasedRuns", "headers", "failure"}


def exact(actual, expected, path):
    assert type(actual) is type(expected), (path, type(actual), type(expected))
    if isinstance(expected, dict):
        assert set(actual) == set(expected), (path, set(actual), set(expected))
        for key in expected:
            exact(actual[key], expected[key], path + "." + key)
    elif isinstance(expected, list):
        assert len(actual) == len(expected), (path, len(actual), len(expected))
        for index, (left, right) in enumerate(zip(actual, expected, strict=True)):
            exact(left, right, f"{path}[{index}]")
    else:
        assert actual == expected, (path, actual, expected)


def check_run(run, name):
    assert set(run) == RUN_FIELDS, (name, "run fields")
    for key in ("position", "end", "receiptID", "receivedAt"):
        assert type(run[key]) is int and run[key] >= 0, (name, key)
    payload = bytes.fromhex(run["payloadHex"])
    assert payload and run["end"] == run["position"] + len(payload), (name, "run length")
    assert run["segment"]["payloadHex"] == run["payloadHex"]


def check_endpoint(endpoint, name):
    if endpoint is None or "receiveStore" not in endpoint:
        return
    store = endpoint["receiveStore"]
    assert set(store) == STORE_FIELDS, (name, "store fields")
    for key in STORE_FIELDS - {"held"}:
        assert type(store[key]) is int and store[key] >= 0, (name, key)
    unread = len(bytes.fromhex(endpoint["core"]["receivedHex"]))
    capacity = endpoint["core"]["capacity"]
    assert store["reservationFree"] == capacity - unread
    assert store["physicalFree"] == capacity - unread - store["heldBytes"]
    assert store["heldBytes"] == sum(len(bytes.fromhex(run["payloadHex"])) for run in store["held"])
    previous = store["frontier"]
    for run in store["held"]:
        check_run(run, name)
        assert previous <= run["position"] and store["frontier"] < run["position"]
        assert run["receiptID"] < store["nextID"]
        previous = run["end"]
    assert len({run["receiptID"] for run in store["held"]}) == len(store["held"])
    if "ackReaction" in endpoint:
        advertisement = endpoint["ackReaction"]["advertisement"]
        assert set(advertisement) == {
            "frontier",
            "edge",
            "window",
            "candidate",
            "threshold",
            "reservationFree",
            "physicalFree",
        }
        assert advertisement["frontier"] == store["frontier"]
        assert advertisement["reservationFree"] == store["reservationFree"]
        assert advertisement["physicalFree"] == store["physicalFree"]
        assert advertisement["window"] == advertisement["edge"] - advertisement["frontier"]
        assert advertisement["window"] <= store["reservationFree"]
        assert all(run["end"] <= advertisement["edge"] for run in store["held"])
        reduction = store["reservationFree"] - advertisement["window"]
        selected = (
            store["reservationFree"]
            if reduction >= advertisement["threshold"]
            else advertisement["window"]
        )
        assert advertisement["candidate"] == selected


def check_frame(frame, before, name):
    assert set(frame) == FRAME_FIELDS, (name, "reassembly fields")
    assert frame["receiptID"] is None or (
        type(frame["receiptID"]) is int and frame["receiptID"] >= 0
    )
    assert type(frame["novelBytes"]) is int and frame["novelBytes"] >= 0
    for run in frame["releasedRuns"]:
        check_run(run, name)
    assert frame["releasedHex"] == "".join(run["payloadHex"] for run in frame["releasedRuns"])
    for header in frame["headers"]:
        assert set(header) == {
            "receiptID",
            "receivedAt",
            "acknowledged",
            "beforeSendUna",
            "afterSendUna",
        }
        assert all(type(value) is int and value >= 0 for value in header.values())
    failure = frame["failure"]
    if failure is not None:
        assert set(failure) == {"source", "check", "receipt", "beforeHeader", "reason"}
        assert failure["check"] in ("header", "recovery")
        assert failure["source"] in ("queued", "current")
        assert set(failure["reason"]) == {"kind", "reason"}
        assert failure["reason"]["kind"] in ("reject", "unsupported")
        check_run(failure["receipt"], name)
        next_id = before.get("receiveStore", {}).get("nextID", 0)
        assert (failure["receipt"]["receiptID"] < next_id) == (failure["source"] == "queued")
        assert frame["receiptID"] is None and frame["novelBytes"] == 0
        assert not frame["releasedRuns"] and not frame["headers"] and frame["releasedHex"] == ""


def audit_header_timers(before, after, headers, clocks, retried, actor, name):
    if "recovery" not in before:
        return
    old, current = before["recovery"], after["recovery"]
    entries = copy.deepcopy(old["outstanding"])
    sample = old["lastSample"]
    for header in headers:
        remaining, retired, count = [], [], header["acknowledged"]
        for entry in entries:
            key = actor, entry["id"]
            assert entry["sentAt"] == clocks[key], (name, "original send clock")
            assert entry["retried"] == (key in retried), (name, "actual retry ambiguity")
            removed = min(count, entry["count"])
            count -= removed
            if removed:
                assert entry["sentAt"] <= header["receivedAt"] <= old["now"], (
                    name,
                    "ACK receipt follows every touched original send",
                )
            if removed == entry["count"]:
                retired.append(entry)
            else:
                remaining.append(
                    {**entry, "start": entry["start"] + removed, "count": entry["count"] - removed}
                )
        assert count == 0
        if retired and not any(entry["retried"] for entry in retired):
            first = retired[0]
            sample = {
                "id": first["id"],
                "sentAt": first["sentAt"],
                "acknowledgedAt": header["receivedAt"],
            }
        entries = remaining
    assert current["outstanding"] == entries, (name, "header retirement")
    assert current["lastSample"] == sample, (name, "actual ACK receipt clock")
    assert current["now"] == old["now"]
    if any(header["acknowledged"] for header in headers):
        assert current["deadline"] == (old["now"] + current["rto"] if entries else None)


def audit(report, name):
    common.audit_custody(report, name)
    written, stream = ({actor: b"" for actor in ACTORS} for _ in range(2))
    writes = {actor: [] for actor in ACTORS}
    unread = {actor: [] for actor in ACTORS}
    receipts = {actor: {} for actor in ACTORS}
    next_id = {actor: 0 for actor in ACTORS}
    receive_origin, send_origin, offset = {}, {}, {actor: 0 for actor in ACTORS}
    originals, ranges, pending, clocks, retried = {}, {}, {}, {}, set()
    issued = {actor: {} for actor in ACTORS}
    discharged = {actor: set() for actor in ACTORS}
    next_ticket = 0
    for step in report["steps"]:
        index, event, decision = step["index"], step["event"], step["decision"]
        operation = event["kind"]
        accepted = decision["kind"] == "accepted"
        for actor in ACTORS:
            for key in ("before", "state"):
                endpoint = step[key][actor]
                check_endpoint(endpoint, name)
                if endpoint is not None and actor not in receive_origin:
                    receive_origin[actor] = endpoint["core"]["receiveNext"]
                    send_origin[actor] = endpoint["core"]["sendUna"]
                    assert endpoint["core"]["receivedHex"] == ""
        if operation == "write" and accepted:
            actor = event["actor"]
            data = bytes.fromhex(event["payloadHex"])
            writes[actor].append((len(written[actor]), len(written[actor]) + len(data), index))
            written[actor] += data
        if operation == "enableRecovery" and accepted:
            offset[event["actor"]] = len(stream[event["actor"]])
        for output in (row for row in report["outputs"] if row["index"] == index):
            actor = output["actor"]
            packet = reference.wire.decode_packet(output["rawIPv4Hex"])
            exact(packet.to_dict(), output["decoded"], name + ".output")
            payload = packet.segment.payload
            attempt = output.get("attempt")
            if attempt is not None:
                assert attempt["clockMillis"] == step["before"][actor]["recovery"]["now"]
                assert attempt["count"] == len(payload)
            if not payload:
                continue
            if attempt is None or attempt["kind"] == "original":
                start = len(stream[actor])
                original_stamp = index
                if attempt is not None:
                    assert start == offset[actor] + attempt["start"]
                    originals[actor, attempt["originalID"]] = (start, payload, index)
                    clocks[actor, attempt["originalID"]] = attempt["clockMillis"]
                stream[actor] += payload
            else:
                assert attempt["kind"] == "retry"
                retried.add((actor, attempt["originalID"]))
                start = offset[actor] + attempt["start"]
                origin, old_payload, original_stamp = originals[actor, attempt["originalID"]]
                assert original_stamp < index and origin <= start
                assert old_payload[start - origin : start - origin + len(payload)] == payload
                assert step["state"][actor]["core"] == step["before"][actor]["core"]
                assert step["state"][actor]["pendingHex"] == step["before"][actor]["pendingHex"]
            assert written[actor].startswith(stream[actor])
            assert written[actor][start : start + len(payload)] == payload
            assert packet.segment.sequence == (send_origin[actor] + start) % reference.MODULUS
            ranges[output["id"]] = (start, original_stamp, index)
        if operation == "assign" and accepted:
            output = report["outputs"][event["output"]]
            assert output["index"] < index
            transfer = step["before"].get("transfer")
            assert transfer is None or not transfer["paused"]
            pending[next_ticket] = (
                output,
                index,
                "primary" if transfer is None else transfer["owners"][output["actor"]],
                0 if transfer is None else transfer["routeEpoch"],
            )
            next_ticket += 1
        if operation == "serve" and step["supported"]:
            output, assigned, gateway, epoch = pending.pop(event["ticket"])
            service = step["service"]
            assert (
                service["outputID"] == output["id"] and service["inputHex"] == output["rawIPv4Hex"]
            )
            assert (
                service.get("gateway", "primary") == gateway
                and service.get("routeEpoch", 0) == epoch
            )
            assert output["index"] < assigned < index
            if service["output"] is not None:
                source = reference.wire.decode_packet(output["rawIPv4Hex"])
                forwarded = reference.wire.decode_packet(service["output"]["rawIPv4Hex"])
                assert (
                    forwarded.segment.payload,
                    forwarded.segment.sequence,
                    forwarded.segment.options,
                ) == (source.segment.payload, source.segment.sequence, source.segment.options)
                assert forwarded.ttl == source.ttl - 1
        receiver = None
        if operation == "deliver":
            service = report["services"][event["service"]]
            assert service["index"] < index and service["output"] is not None
            assert event["rawIPv4Hex"] == service["output"]["rawIPv4Hex"]
            if step["before"]["passivePhase"] == "ESTABLISHED" and service["sourceKind"] in (
                "send",
                "retry",
                "emitAck",
                "dispatchAck",
            ):
                receiver = "server" if service["actor"] == "client" else "client"
                packet = reference.wire.decode_packet(event["rawIPv4Hex"])
                payload = packet.segment.payload
                frame = step.get("reassembly")
                if frame is not None:
                    check_frame(frame, step["before"][receiver], name)
                if accepted and payload:
                    identity = next_id[receiver]
                    next_id[receiver] += 1
                    position = reference.signed_distance(
                        receive_origin[receiver], packet.segment.sequence
                    )
                    clock = step["before"][receiver].get("recovery", {}).get("now", 0)
                    segment = packet.segment.to_dict()
                    segment.update(
                        sourcePort=packet.header.source_port,
                        destinationPort=packet.header.destination_port,
                    )
                    run = {
                        "position": position,
                        "end": position + len(payload),
                        "receiptID": identity,
                        "payloadHex": payload.hex(),
                        "header": packet.header.to_dict(),
                        "segment": segment,
                        "receivedAt": clock,
                    }
                    receipts[receiver][identity] = (
                        run,
                        index,
                        service["outputID"],
                        service.get("gateway", "primary"),
                    )
                    if frame is not None:
                        assert frame["receiptID"] == identity
                        released = frame["releasedRuns"]
                    else:
                        released = [run]
                    for run in released:
                        original, received, output_id, gateway = receipts[receiver][
                            run["receiptID"]
                        ]
                        exact(run, original, name + ".released origin")
                        assert received <= index
                        start, original_stamp, attempt_stamp = ranges[output_id]
                        assert original_stamp <= attempt_stamp < received <= index
                        for at, value in enumerate(bytes.fromhex(run["payloadHex"])):
                            unread[receiver].append(
                                (
                                    value,
                                    start + at,
                                    original_stamp,
                                    attempt_stamp,
                                    received,
                                    index,
                                    gateway,
                                )
                            )
                if frame is not None:
                    assert frame["receiptID"] is not None or not (accepted and payload)
                    if frame["failure"] is not None:
                        old, current = step["before"][receiver], step["state"][receiver]
                        for key in old.keys() - {"ackReaction"}:
                            assert current[key] == old[key], (name, "no partial release")
                        if frame["failure"]["source"] == "queued":
                            assert current == old
                    if frame["headers"]:
                        assert [row["receiptID"] for row in frame["headers"]] == [
                            row["receiptID"] for row in frame["releasedRuns"]
                        ]
                        assert (
                            sum(row["acknowledged"] for row in frame["headers"])
                            == decision["acknowledged"]
                        )
                        core = reference.wire.State.from_dict(step["before"][receiver]["core"])
                        for header, run in zip(
                            frame["headers"], frame["releasedRuns"], strict=True
                        ):
                            segment = run["segment"]
                            count = reference.wire.acknowledged_count(
                                core, segment["acknowledgment"]
                            )
                            assert count is not None and count == header["acknowledged"]
                            assert (
                                segment["flags"] & 16 and segment["sequence"] == core.receive_next
                            )
                            assert run["header"] == core.inbound.to_dict()
                            assert header["beforeSendUna"] == core.send_una
                            data = bytes.fromhex(run["payloadHex"])
                            core = replace(
                                core,
                                receive_next=(core.receive_next + len(data)) % reference.MODULUS,
                                received=core.received + data,
                                send_una=(core.send_una + count) % reference.MODULUS,
                                sent=core.sent[count:],
                            )
                            assert header["afterSendUna"] == core.send_una
                        exact(
                            step["state"][receiver]["core"], core.to_dict(), name + ".released core"
                        )
                        audit_header_timers(
                            step["before"][receiver],
                            step["state"][receiver],
                            frame["headers"],
                            clocks,
                            retried,
                            receiver,
                            name,
                        )
                    elif accepted and payload:
                        assert step["state"][receiver]["core"] == step["before"][receiver]["core"]
                        if "recovery" in step["before"][receiver]:
                            assert (
                                step["state"][receiver]["recovery"]
                                == step["before"][receiver]["recovery"]
                            )
                if "receiveStore" in step["state"][receiver]:
                    store = step["state"][receiver]["receiveStore"]
                    assert store["nextID"] == next_id[receiver]
                    for run in store["held"]:
                        exact(run, receipts[receiver][run["receiptID"]][0], name + ".held origin")
                assert (
                    bytes(cell[0] for cell in unread[receiver]).hex()
                    == step["state"][receiver]["core"]["receivedHex"]
                )
        if operation == "read" and accepted:
            actor = event["actor"]
            count = event["count"]
            selected = unread[actor][:count]
            del unread[actor][:count]
            assert bytes(cell[0] for cell in selected).hex() == step["readHex"]
            peer = "server" if actor == "client" else "client"
            for value, position, original_stamp, attempt_stamp, received, released, _ in selected:
                assert written[peer][position] == value
                writer = next(
                    stamp for start, end, stamp in writes[peer] if start <= position < end
                )
                assert writer < original_stamp <= attempt_stamp < received <= released < index
        for actor in ACTORS:
            before, after = step["before"][actor], step["state"][actor]
            if before is None or after is None or "ackReaction" not in before:
                continue
            old, current = before["ackReaction"], after["ackReaction"]
            old_work, work = old["work"], current["work"]
            now = before["recovery"]["now"]
            if work["nextID"] > old_work["nextID"]:
                assert work["nextID"] == old_work["nextID"] + 1
                cause = next(row for row in work["pending"] if row["id"] == old_work["nextID"])
                assert cause["issuedAt"] == now and cause["due"] - now in (0, 499)
                assert (operation == "read" and event["actor"] == actor) or receiver == actor
                if operation == "read":
                    assert accepted and event["count"] > 0
                    assert cause["demand"]["kind"] == "window" and cause["due"] == now
                    assert current["advertisement"]["candidate"] > old["advertisement"]["candidate"]
                elif receiver == actor and accepted:
                    assert cause["demand"]["bytes"] == decision["received"]
                    assert cause["demand"]["kind"] == "data"
                    assert cause["demand"]["position"] == current["advertisement"]["frontier"]
                    assert cause["demand"]["cursor"] == after["core"]["receiveNext"]
                    if packet.segment.sequence != before["core"]["receiveNext"] or before.get(
                        "receiveStore", {}
                    ).get("held"):
                        assert cause["due"] == now
                else:
                    assert decision == {"kind": "reject", "reason": "input.sequence"}
                    assert cause["demand"]["kind"] == "sequence" and cause["demand"]["bytes"] == 0
                    assert cause["due"] == now
                issued[actor][cause["id"]] = (index, cause)
            if len(work["completed"]) > len(old_work["completed"]):
                assert len(work["completed"]) == len(old_work["completed"]) + 1
                output = next(
                    row
                    for row in report["outputs"]
                    if row["index"] == index and row["actor"] == actor
                )
                packet_output = reference.wire.decode_packet(output["rawIPv4Hex"])
                group = work["completed"][-1]
                assert group["time"] == now
                assert [row["id"] for row in group["causes"]] == [
                    row["id"] for row in old_work["pending"]
                ]
                assert group["output"]["cursor"] == packet_output.segment.acknowledgment
                assert group["output"]["window"] == packet_output.segment.window
                for cause in group["causes"]:
                    stamp, actual = issued[actor][cause["id"]]
                    exact(cause, actual, name + ".cause")
                    assert stamp < index and cause["issuedAt"] <= now <= cause["due"]
                    assert now - cause["issuedAt"] < 500 and cause["id"] not in discharged[actor]
                    demand, response = cause["demand"], group["output"]
                    assert demand["position"] <= response["position"]
                    assert (
                        demand["cursor"] + response["position"] - demand["position"]
                    ) % reference.MODULUS == packet_output.segment.acknowledgment
                    assert (
                        demand["minimumEdge"] <= response["position"] + packet_output.segment.window
                    )
                    discharged[actor].add(cause["id"])


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
    ack_checks.check_ack_assurance(report, oracle, name)
    check_gap_assurance(report, oracle, name)
    audit(report, name)
    return report


def check_gap_assurance(report, oracle, name):
    expected = reference.receive_gap_assurance(oracle)
    if expected is None:
        assert "receiveGapAssurance" not in report, (name, "unexpected receiveGapAssurance")
    else:
        assert "receiveGapAssurance" in report, (name, "missing receiveGapAssurance")
        exact(report["receiveGapAssurance"], expected, name + ".receiveGapAssurance")


def legacy_absence(binary, path):
    families = {
        "campus": reference.recovery.base.load("fixtures")["cases"],
        "transfer": reference.recovery.transfer.load_fixtures()["cases"],
        "mss": mss_checks.load_fixtures()["campus"],
        "recovery": reference.recovery.load_fixtures()["cases"],
        "ack": reference.ack.load_fixtures()["cases"],
    }
    count = 0
    for family, cases in families.items():
        for case in cases:
            name = family + "." + case["id"]
            oracle = reference.replay(case["input"])
            assert reference.receive_gap_assurance(oracle) is None, (name, "legacy gap")
            expected = case["expected"]
            code = (0 if expected["compliant"] else 1) if expected["supported"] else 2
            path.write_text(json.dumps(case["input"]))
            report = json.loads(recovery_checks.invoke(binary, path, code, name))
            check_gap_assurance(report, oracle, name)
            count += 1
    return count


def input_error(binary, path, value, name, command="campus-tcp"):
    path.write_text(json.dumps(value))
    result = subprocess.run(
        [str(binary), command, str(path), "--json"],
        cwd=common.ROOT,
        text=True,
        capture_output=True,
        check=False,
    )
    assert result.returncode == 2, (name, result.returncode, result.stdout, result.stderr)
    try:
        parsed = json.loads(result.stdout)
    except json.JSONDecodeError:
        return
    scope = common.SCOPE if command == "campus-tcp" else "tcp-application-projection"
    assert not isinstance(parsed, dict) or parsed.get("scope") != scope, (
        name,
        "expected input error, received a profile stop",
    )


def check_deferred_clock_input(data):
    case = next(
        case
        for case in data["cases"]
        if case["id"] == "queued-header-retains-original-receipt-clock"
    )
    canonical = json.loads((reference.DIRECTORY / "deferred-clock.json").read_text())
    exact(canonical, case["input"], "canonical deferred-clock input")


def check(binary=BINARY):
    data = reference.load_fixtures()
    check_deferred_clock_input(data)
    with tempfile.TemporaryDirectory(prefix="netlib-tcp-gaps-") as directory:
        path = Path(directory) / "input.json"
        for case in data["cases"]:
            oracle = reference.replay(case["input"])
            exact(reference.projection(oracle), case["expected"], case["id"] + ".frozen oracle")
            report_case(binary, path, case["input"], case["expected"], case["id"])
        for case in data["inputErrors"]:
            input_error(binary, path, case["input"], case["id"])
        for case in data["endpointCases"]:
            exact(
                reference.raw_replay(case["input"]), case["expected"], case["id"] + ".frozen oracle"
            )
            path.write_text(json.dumps(case["input"]))
            result = subprocess.run(
                [str(binary), "tcp-endpoint", str(path), "--json"],
                cwd=common.ROOT,
                text=True,
                capture_output=True,
                check=False,
            )
            assert result.returncode == (0 if case["expected"]["supported"] else 2), (
                case["id"],
                result.stdout,
                result.stderr,
            )
            observed = json.loads(result.stdout)
            common.same_fields(observed, case["expected"], case["id"])
            for step in observed["steps"]:
                for key in ("before", "state"):
                    check_endpoint(step[key], case["id"])
                if "reassembly" in step:
                    check_frame(step["reassembly"], step["before"], case["id"])
        for case in data["endpointInputErrors"]:
            input_error(binary, path, case["input"], case["id"], "tcp-endpoint")
        upper = copy.deepcopy(data["input"])
        for event in upper["events"]:
            for key in ("rawIPv4Hex", "payloadHex"):
                if key in event:
                    event[key] = event[key].upper()
        report_case(binary, path, upper, data["cases"][0]["expected"], "uppercase receive gaps")
        no_gap_legacy = legacy_absence(binary, path)
    counts = {
        key: len(data[key])
        for key in ("cases", "inputErrors", "endpointCases", "endpointInputErrors")
    }
    counts["uppercase"] = 1
    counts["noGapLegacy"] = no_gap_legacy
    print("TCP receive-gap comparisons passed: " + json.dumps(counts, sort_keys=True))
    return counts


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--binary", type=Path, default=BINARY)
    check(parser.parse_args().binary)


if __name__ == "__main__":
    main()
