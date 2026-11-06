"""Compare sparse gateway coverage, current headers, and actual campus byte sources.

Raw admission checks assume the declared mapping and fixed permit pipeline.
They do not establish endpoint writes, authentication, or physical packet delivery.
This helper does not compile Lean or send packets.
"""

import argparse
import copy
import json
import subprocess
import tempfile
from pathlib import Path

import campus_tcp_sparse_reference as reference
import check_campus_tcp_examples as common
import check_campus_tcp_transfer_examples as transfer_checks
import check_tcp_ack_examples as ack_checks
import check_tcp_gap_examples as gap_checks
import check_tcp_recovery_examples as recovery_checks

BINARY = common.BINARY
exact = gap_checks.exact
COVERAGE_FIELDS = {"highEnd", "uniqueBytes", "nextID", "runs"}
RUN_FIELDS = {"position", "end", "sourceID", "observationIndex", "payloadHex"}
LANE_FIELDS = {
    "base",
    "observed",
    "acknowledged",
    "peerWindow",
    "windowSequence",
    "windowAcknowledgment",
}
RAW_FIELDS = {
    "scope",
    "supported",
    "inputPackets",
    "evaluatedPackets",
    "initial",
    "steps",
    "final",
    "remainingPacketsHex",
    "assumptions",
}


def audit_admission(admission, name):
    packets = admission["sourcePackets"]
    assert admission["observations"] == len(packets)
    if admission["phase"] != "data":
        return
    directions = ("original", "reply")
    bases = {direction: admission[direction]["base"] for direction in directions}
    assert len(packets) >= 3
    decoded = [reference.wire.decode_packet(row["rawIPv4Hex"]) for row in packets]
    windows = {
        "original": [
            decoded[1].segment.window,
            decoded[1].segment.sequence,
            decoded[1].segment.acknowledgment,
        ],
        "reply": [
            decoded[2].segment.window,
            decoded[2].segment.sequence,
            decoded[2].segment.acknowledgment,
        ],
    }
    cells, originals = ({direction: {} for direction in directions} for _ in range(2))
    acknowledged = {direction: 0 for direction in directions}

    def frontier(direction):
        cursor = 0
        while cursor in cells[direction]:
            cursor += 1
        return cursor

    def high_end(direction):
        return max(cells[direction], default=-1) + 1

    for observation, (source, packet) in enumerate(zip(packets, decoded, strict=True)):
        exact(packet.header.to_dict(), source["header"], name + ".observation header")
        common.same_fields(
            source["segment"], packet.to_dict()["segment"], name + ".observation segment"
        )
        exact(source["entry"], admission["entry"], name + ".entry source")
        direction = source["direction"]
        assert direction in directions
        if observation < 3:
            continue
        peer = "reply" if direction == "original" else "original"
        segment = packet.segment
        assert segment.flags in (16, 24) and not segment.options
        start = (segment.sequence - bases[direction]) % reference.wire.MODULUS
        ack = (segment.acknowledgment - bases[peer]) % reference.wire.MODULUS
        assert ack <= frontier(peer) and acknowledged[peer] <= ack + 65535
        end = start + len(segment.payload)
        assert start < reference.wire.HALF_SPACE
        if segment.payload:
            existing = [position for position in range(start, end) if position in cells[direction]]
            if existing:
                assert len(existing) == len(segment.payload)
                owners = {cells[direction][position][1] for position in existing}
                assert len(owners) == 1
                source_id = next(iter(owners))
                original = originals[direction][source_id]
                offset = start - original["position"]
                original_payload = bytes.fromhex(original["payloadHex"])
                assert segment.payload == original_payload[offset : offset + len(segment.payload)]
            else:
                assert end <= acknowledged[direction] + windows[direction][0]
                source_id = len(originals[direction])
                originals[direction][source_id] = {
                    "position": start,
                    "end": end,
                    "sourceID": source_id,
                    "observationIndex": observation,
                    "payloadHex": segment.payload.hex(),
                }
                for index, byte in enumerate(segment.payload):
                    cells[direction][start + index] = (byte, source_id, index)
        else:
            assert start <= high_end(direction)
        old_window, old_sequence, old_ack = windows[peer]
        sequence_age = reference.base.endpoint.signed_offset(old_sequence, segment.sequence)
        ack_age = reference.base.endpoint.signed_offset(old_ack, segment.acknowledgment)
        if ack >= acknowledged[peer] and (sequence_age > 0 or sequence_age == 0 and ack_age >= 0):
            windows[peer] = [segment.window, segment.sequence, segment.acknowledgment]
        acknowledged[peer] = max(acknowledged[peer], ack)
        assert high_end(direction) + 2 < reference.wire.HALF_SPACE
        assert high_end(direction) - acknowledged[direction] <= 65535
        assert old_window >= 0
    for direction in directions:
        lane = admission[direction]
        assert set(lane) in (LANE_FIELDS, LANE_FIELDS | {"coverage"}), (name, "lane fields")
        for key in LANE_FIELDS:
            assert type(lane[key]) is int and lane[key] >= 0, (name, key)
        assert lane["observed"] == frontier(direction)
        assert lane["acknowledged"] == acknowledged[direction]
        assert [
            lane["peerWindow"],
            lane["windowSequence"],
            lane["windowAcknowledgment"],
        ] == windows[direction]
        runs = sorted(originals[direction].values(), key=lambda run: run["position"])
        ids = [run["sourceID"] for run in runs]
        sparse = frontier(direction) != high_end(direction) or ids != sorted(ids)
        if sparse:
            assert "coverage" in lane, (name, "missing sparse coverage")
            coverage = lane["coverage"]
            assert set(coverage) == COVERAGE_FIELDS
            for run in coverage["runs"]:
                assert set(run) == RUN_FIELDS
            expected = {
                "highEnd": high_end(direction),
                "uniqueBytes": len(cells[direction]),
                "nextID": len(runs),
                "runs": runs,
            }
            exact(coverage, expected, name + ".actual first sources")
        else:
            assert "coverage" not in lane, (name, "unexpected sparse coverage")


def audit_campus(report, name):
    gap_checks.audit(report, name)
    for step in report["steps"]:
        for key in ("before", "state"):
            state = step[key]
            for gateway in state.get("gateways", {}).values():
                audit_admission(gateway["admission"], name)
            cache = state.get("transfer", {}).get("cache")
            if cache is not None:
                audit_admission(cache["admission"], name)
        service = step.get("service")
        if service is not None and "gateways" in step["state"]:
            owner = service.get("gateway", "primary")
            before = step["before"]["gateways"][owner]
            after = step["state"]["gateways"][owner]
            if service["disposition"] == "earlyDrop":
                exact(after, before, name + ".current early denial")
            else:
                old = before["admission"]["sourcePackets"]
                current = after["admission"]["sourcePackets"]
                assert len(current) == len(old) + 1
                exact(current[:-1], old, name + ".first observation history")
                assert current[-1]["rawIPv4Hex"] == service["inputHex"]
        if step["event"]["kind"] == "installCheckpoint" and step["decision"]["kind"] == "accepted":
            primary = step["before"]["gateways"]["primary"]
            standby = step["state"]["gateways"]["standby"]
            for key in ("records", "confirmed", "admission", "historyTransitions"):
                exact(standby[key], primary[key], name + ".exact sparse image")
            for actor in ("client", "server"):
                exact(step["state"][actor], step["before"][actor], name + ".host stays local")


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
    common.same_fields(
        report["transferAssurance"],
        transfer_checks.expected_transfer(oracle),
        name + ".transferAssurance",
    )
    ack_checks.check_ack_assurance(report, oracle, name)
    gap_checks.check_gap_assurance(report, oracle, name)
    check_sparse_assurance(report, oracle, name)
    audit_campus(report, name)


def check_sparse_assurance(report, oracle, name):
    expected = reference.sparse_assurance(oracle)
    if expected is None:
        assert "sparseAssurance" not in report, (name, "unexpected sparseAssurance")
    else:
        assert "sparseAssurance" in report, (name, "missing sparseAssurance")
        exact(report["sparseAssurance"], expected, name + ".sparseAssurance")


def legacy_absence(binary, path):
    families = {
        "campus": reference.base.load("fixtures")["cases"],
        "transfer": reference.transfer.load_fixtures()["cases"],
        "mss": gap_checks.mss_checks.load_fixtures()["campus"],
        "recovery": reference.gaps.recovery.load_fixtures()["cases"],
        "ack": reference.gaps.ack.load_fixtures()["cases"],
        "gaps": reference.gaps.load_fixtures()["cases"],
    }
    count = 0
    for family, cases in families.items():
        for case in cases:
            name = family + "." + case["id"]
            oracle = reference.replay(case["input"])
            assert reference.sparse_assurance(oracle) is None
            expected = case["expected"]
            code = (0 if expected["compliant"] else 1) if expected["supported"] else 2
            path.write_text(json.dumps(case["input"]))
            report = json.loads(recovery_checks.invoke(binary, path, code, name))
            check_sparse_assurance(report, oracle, name)
            count += 1
    return count


def check_raw(report, expected, name):
    assert set(report) == RAW_FIELDS
    exact(report, expected, name)
    for state in [
        report["initial"],
        report["final"],
        *(step[key] for step in report["steps"] for key in ("before", "after")),
    ]:
        assert set(state) == {"tracker", "admission"}
        audit_admission(state["admission"], name)
    for step in report["steps"]:
        assert set(step) == {"index", "decoded", "before", "decision", "outputHex", "after"}
        if step["decision"]["kind"] == "unsupported":
            exact(step["after"], step["before"], name + ".no partial admission")


def check(binary=BINARY):
    data = reference.load_fixtures()
    for filename, case in zip(
        ("trace.json", "reverse.json", "wrap.json"), data["cases"][:3], strict=True
    ):
        exact(
            json.loads((reference.DIRECTORY / filename).read_text()),
            case["input"],
            filename + ".canonical input",
        )
    with tempfile.TemporaryDirectory(prefix="netlib-tcp-sparse-") as directory:
        path = Path(directory) / "input.json"
        for case in data["cases"]:
            exact(
                reference.projection(reference.replay(case["input"])),
                case["expected"],
                case["id"] + ".frozen oracle",
            )
            report_case(binary, path, case["input"], case["expected"], case["id"])
        for case in data["inputErrors"]:
            gap_checks.input_error(binary, path, case["input"], case["id"])
        for case in data["admissionCases"]:
            expected = reference.raw_replay(case["input"])
            exact(expected, case["expected"], case["id"] + ".frozen oracle")
            path.write_text(json.dumps(case["input"]))
            result = subprocess.run(
                [str(binary), "tcp-admission", str(path), "--json"],
                cwd=common.ROOT,
                text=True,
                capture_output=True,
                check=False,
            )
            assert result.returncode == (0 if expected["supported"] else 2), (
                case["id"],
                result.returncode,
                result.stderr,
            )
            check_raw(json.loads(result.stdout), expected, case["id"])
        for case in data["admissionInputErrors"]:
            gap_checks.input_error(binary, path, case["input"], case["id"], "tcp-admission")
        upper = copy.deepcopy(data["input"])
        for event in upper["events"]:
            for key in ("rawIPv4Hex", "payloadHex"):
                if key in event:
                    event[key] = event[key].upper()
        report_case(binary, path, upper, data["cases"][0]["expected"], "uppercase sparse packets")
        no_sparse_legacy = legacy_absence(binary, path)
    counts = {
        key: len(data[key])
        for key in ("cases", "inputErrors", "admissionCases", "admissionInputErrors")
    }
    counts["uppercase"] = 1
    counts["noSparseLegacy"] = no_sparse_legacy
    print("TCP sparse admission comparisons passed: " + json.dumps(counts, sort_keys=True))
    return counts


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--binary", type=Path, default=BINARY)
    check(parser.parse_args().binary)


if __name__ == "__main__":
    main()
