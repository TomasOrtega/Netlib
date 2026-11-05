"""Compare the compiled TCP receive CLI with independent static results.

This manual helper does not send packets or collect captures.
"""

import argparse
import copy
import json
import subprocess
import tempfile
from pathlib import Path

import tcp_receive_reference as reference

ROOT = Path(__file__).resolve().parent.parent
BINARY = ROOT / ".lake/build/bin/netlib"
SCOPE = "tcp-established-receive-projection"


def invoke(binary, path, code):
    result = subprocess.run(
        [str(binary), "tcp-receive", str(path), "--json"],
        cwd=ROOT,
        check=False,
        text=True,
        capture_output=True,
    )
    assert result.returncode == code, (result.returncode, result.stdout, result.stderr)
    return result.stdout


def write(path, value):
    path.write_text(json.dumps(value))
    return path


def compare_report(observed, expected, name):
    for field, value in expected.items():
        assert observed[field] == value, (name, field, observed[field], value)
    assert observed["assumptions"], name
    assert observed["scope"] == SCOPE and observed["finalStateValid"], name
    assert observed["evaluatedPackets"] == len(observed["steps"]), name
    assert observed["inputPackets"] == observed["evaluatedPackets"] + len(
        observed["remainingPacketsHex"]
    ), name
    unsupported = [
        step["index"] for step in observed["steps"] if step["decision"]["kind"] == "unsupported"
    ]
    if observed["supported"]:
        assert not unsupported and not observed["remainingPacketsHex"], name
    else:
        assert unsupported == [observed["evaluatedPackets"] - 1], name
    before = observed["seed"]
    for index, step in enumerate(observed["steps"]):
        assert step["index"] == index and step["before"] == before, (name, index)
        assert reference.decode_packet(step["rawIPv4Hex"]).to_dict() == step["decoded"], (
            name,
            index,
        )
        before = step["state"]
    assert before == observed["final"], name


def report_case(binary, path, value, expected, name):
    code = 0 if expected["supported"] else 2
    observed = json.loads(invoke(binary, write(path, value), code))
    compare_report(observed, expected, name)


def error_case(binary, path, value, name):
    error_text(binary, path, json.dumps(value), name)


def error_text(binary, path, text, name):
    path.write_text(text)
    output = invoke(binary, path, 2)
    try:
        parsed = json.loads(output)
    except json.JSONDecodeError:
        return
    assert not isinstance(parsed, dict) or parsed.get("scope") != SCOPE, name


def invalid_inputs(binary, path, value):
    rows = []

    def changed(name, section, field, replacement):
        row = copy.deepcopy(value)
        target = (
            row
            if section == "root"
            else row["seed"]
            if section == "seed"
            else row["seed"]["inbound"]
        )
        target[field] = replacement
        rows.append((name, row))

    changed("schema-version", "root", "schema", 2)
    changed("schema-type", "root", "schema", "1")
    changed("unknown-root-field", "root", "header", {})
    changed("packet-array-type", "root", "packetsHex", "")
    changed("packet-element-type", "root", "packetsHex", [0])
    for name, raw in (
        ("odd-hex", "0"),
        ("nonhex", "gg"),
        ("hex-separator", "00 00"),
        ("short-ip", "00"),
        ("empty-ip", ""),
    ):
        changed(name, "root", "packetsHex", [raw])
    changed("unknown-seed-field", "seed", "window", 6)
    changed("negative-capacity", "seed", "capacity", -1)
    changed("large-capacity", "seed", "capacity", 65536)
    changed("buffer-above-capacity", "seed", "capacity", 1)
    changed("receive-word-range", "seed", "receiveNext", 1 << 32)
    changed("send-una-word-range", "seed", "sendUna", 1 << 32)
    changed("send-next-word-range", "seed", "sendNext", 1 << 32)
    changed("negative-sequence", "seed", "receiveNext", -1)
    changed("send-cursor-relation", "seed", "sendNext", 1007)
    changed("received-hex", "seed", "receivedHex", "0")
    changed("sent-hex", "seed", "sentHex", "gg")
    changed("seed-source", "inbound", "source", "192.000.2.1")
    changed("seed-destination", "inbound", "destination", "2001:db8::1")
    changed("seed-protocol", "inbound", "protocol", 17)
    changed("source-port-range", "inbound", "sourcePort", 65536)
    changed("destination-port-range", "inbound", "destinationPort", -1)
    missing = copy.deepcopy(value)
    del missing["packetsHex"]
    rows.append(("missing-packets", missing))
    missing = copy.deepcopy(value)
    del missing["seed"]["sentHex"]
    rows.append(("missing-seed-field", missing))
    raw = bytes.fromhex(value["packetsHex"][0])
    ip = bytearray(raw)
    ip[10] ^= 1
    changed("bad-ipv4-checksum", "root", "packetsHex", [ip.hex()])
    tcp = bytearray(raw)
    tcp[-1] ^= 1
    changed("bad-tcp-checksum", "root", "packetsHex", [tcp.hex()])
    header = reference.Header.from_dict(value["seed"]["inbound"])
    malformed = reference.fixture_packet(
        header, reference.Segment(100, 1000, options=bytes.fromhex("02030000"))
    )
    changed("malformed-mss", "root", "packetsHex", [malformed.hex()])
    for name, row in rows:
        error_case(binary, path, row, name)
    text = json.dumps(value)
    error_text(binary, path, text.replace('"schema": 1', '"schema": 1.0', 1), "decimal-schema")
    error_text(
        binary,
        path,
        text.replace('"schema": 1', '"schema": 1, "schema": 1', 1),
        "duplicate-schema",
    )
    error_text(
        binary,
        path,
        text.replace('"capacity": 8', '"capacity": 8, "capacity": 8', 1),
        "duplicate-capacity",
    )
    return len(rows) + 3


def stop_inputs(binary, path, fixtures):
    excluded = next(case for case in fixtures["cases"] if case["name"] == "zero-window-reset-data")
    value = {
        "schema": 1,
        "seed": excluded["seed"],
        "packetsHex": [excluded["rawIPv4Hex"], "00"],
    }
    report_case(
        binary,
        path,
        value,
        reference.replay(value["seed"], value["packetsHex"]),
        "unread-transport-suffix",
    )
    malformed_hex = {**value, "packetsHex": [excluded["rawIPv4Hex"], "0"]}
    error_case(binary, path, malformed_hex, "unread-hex-syntax")
    rejected = next(case for case in fixtures["cases"] if case["name"] == "ack-beyond-next")
    value = {
        "schema": 1,
        "seed": rejected["seed"],
        "packetsHex": [rejected["rawIPv4Hex"], "00"],
    }
    error_case(binary, path, value, "rejection-does-not-stop-decode")
    return 3


def check(binary=BINARY):
    fixtures = reference.load_fixtures()
    reference.check_fixtures(fixtures)
    counts = {"receive": 0, "invalidSeeds": 0, "traces": 0}
    with tempfile.TemporaryDirectory(prefix="netlib-static-tcp-receive-") as directory:
        path = Path(directory) / "input.json"
        for case in fixtures["cases"]:
            value = {
                "schema": 1,
                "seed": case["seed"],
                "packetsHex": [case["rawIPv4Hex"]],
            }
            if case["coreOnly"]:
                error_case(binary, path, value, case["name"])
                counts["invalidSeeds"] += 1
            else:
                expected = reference.replay(value["seed"], value["packetsHex"])
                report_case(binary, path, value, expected, case["name"])
                counts["receive"] += 1
        for trace in fixtures["traces"]:
            report_case(binary, path, trace["input"], trace["expected"], trace["name"])
            counts["traces"] += 1
        ordinary = next(case for case in fixtures["cases"] if case["name"] == "ack-duplicate")
        value = {
            "schema": 1,
            "seed": ordinary["seed"],
            "packetsHex": [ordinary["rawIPv4Hex"]],
        }
        counts["invalidInputs"] = invalid_inputs(binary, path, value)
        counts["stopBoundaries"] = stop_inputs(binary, path, fixtures)
    guide = json.loads((ROOT / "examples/tcp-receive/trace.json").read_text())
    assert guide == next(
        trace["input"] for trace in fixtures["traces"] if trace["name"] == "ack-prefix-and-data"
    )
    return counts


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--binary", type=Path, default=BINARY)
    arguments = parser.parse_args()
    print(
        json.dumps(
            {"scope": "static receive projection only", **check(arguments.binary)},
            sort_keys=True,
        )
    )


if __name__ == "__main__":
    main()
