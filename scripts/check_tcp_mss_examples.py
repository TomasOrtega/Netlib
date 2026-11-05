"""Compare directional MSS through startup, gateway service, and planned transfer.

All expected bytes come from independent static Python calculations.
The helper does not compile Lean or send packets.
"""

import argparse
import copy
import json
import tempfile
from pathlib import Path

import campus_tcp_transfer_reference as transfer
import check_campus_tcp_transfer_examples as campus_checks
import check_tcp_handshake_examples as startup_checks
import tcp_handshake_reference as handshake

BINARY = startup_checks.BINARY
DIRECTORY = startup_checks.ROOT / "examples/tcp-mss"


def load_fixtures():
    data = json.loads((DIRECTORY / "fixtures.json").read_text())
    assert data["schema"] == 1
    for case in data["campus"] + data["campusErrors"]:
        value = copy.deepcopy(data["campusInput"])
        for replacement in case["replacements"]:
            target = value
            for key in replacement["path"][:-1]:
                target = target[key]
            target[replacement["path"][-1]] = replacement["value"]
        case["input"] = value
    return data


def check_static(data=None):
    data = load_fixtures() if data is None else data
    for case in data["handshakes"]:
        assert handshake.replay(case["input"]) == case["expected"], case["id"]
    for case in data["handshakeErrors"]:
        try:
            handshake.replay(case["input"])
        except ValueError:
            pass
        else:
            raise AssertionError(case["id"])
    for case in data["campus"]:
        report = transfer.replay(case["input"])
        assert transfer.projection(report) == case["expected"], case["id"]
    trace = json.loads((DIRECTORY / "trace.json").read_text())
    assert trace == data["campusInput"]
    report = transfer.replay(trace)
    assert report["supported"] and report["compliant"]
    assert [(row["actor"], len(row["readHex"]) // 2) for row in report["reads"]] == [
        ("server", 1600),
        ("client", 2401),
    ]
    installed = report["steps"][43]["state"]["gateways"]["standby"]["admission"]
    assert installed["reply"]["observed"] == 1201
    assert installed["reply"]["acknowledged"] == 0
    assert (installed["originalMSS"], installed["replyMSS"]) == (800, 1200)
    assert (
        report["steps"][50]["state"]["gateways"]["standby"]["admission"]["reply"]["acknowledged"]
        == 1201
    )
    assert report["services"][-1]["disposition"] == "earlyDrop"
    return {key: len(data[key]) for key in ("handshakes", "handshakeErrors", "campus")}


def check(binary=BINARY):
    data = load_fixtures()
    counts = check_static(data)
    with tempfile.TemporaryDirectory(prefix="netlib-tcp-mss-") as directory:
        path = Path(directory) / "input.json"
        for case in data["handshakes"]:
            startup_checks.report_case(binary, path, case["input"], case["expected"], case["id"])
        for case in data["handshakeErrors"]:
            startup_checks.error_text(binary, path, json.dumps(case["input"]), case["id"])
        for case in data["campus"]:
            campus_checks.report_case(binary, path, case["input"], case["expected"], case["id"])
        for case in data["campusErrors"]:
            path.write_text(json.dumps(case["input"]))
            output = campus_checks.common.invoke(binary, path, 2)
            try:
                parsed = json.loads(output)
            except json.JSONDecodeError:
                continue
            assert not isinstance(parsed, dict) or parsed.get("scope") != campus_checks.common.SCOPE
        value = copy.deepcopy(data["campusInput"])
        for event in value["events"]:
            for field in ("payloadHex", "rawIPv4Hex"):
                if field in event:
                    event[field] = event[field].upper()
        campus_checks.report_case(
            binary, path, value, data["campus"][0]["expected"], "uppercase MSS bytes"
        )
    counts["uppercase"] = 1
    counts["campusErrors"] = len(data["campusErrors"])
    print("Directional MSS comparisons passed: " + json.dumps(counts, sort_keys=True))
    return counts


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--binary", type=Path, default=BINARY)
    check(parser.parse_args().binary)


if __name__ == "__main__":
    main()
