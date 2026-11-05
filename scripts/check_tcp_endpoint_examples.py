"""Compare the compiled TCP application CLI with independent static results.

This manual helper does not send packets or collect captures.
"""

import argparse
import copy
import json
import subprocess
import tempfile
from dataclasses import replace
from pathlib import Path

import tcp_endpoint_reference as reference
import tcp_receive_reference as wire

ROOT = Path(__file__).resolve().parent.parent
BINARY = ROOT / ".lake/build/bin/netlib"
SCOPE = "tcp-application-projection"


def invoke(binary, path, code):
    result = subprocess.run(
        [str(binary), "tcp-endpoint", str(path), "--json"],
        cwd=ROOT,
        check=False,
        text=True,
        capture_output=True,
    )
    assert result.returncode == code, (result.returncode, result.stdout, result.stderr)
    return result.stdout


def compare_report(observed, expected, name):
    for field, value in expected.items():
        assert observed[field] == value, (name, field, observed[field], value)
    assert observed["scope"] == SCOPE and observed["finalStateValid"], name
    assert observed["assumptions"] and observed["sources"], name
    assert observed["evaluatedEvents"] == len(observed["steps"]), name
    assert observed["inputEvents"] == observed["evaluatedEvents"] + len(
        observed["remainingEvents"]
    ), name
    unsupported = [
        step["index"] for step in observed["steps"] if step["decision"]["kind"] == "unsupported"
    ]
    if observed["supported"]:
        assert not unsupported and not observed["remainingEvents"], name
    else:
        assert unsupported == [observed["evaluatedEvents"] - 1], name
    before = observed["seed"]
    for index, step in enumerate(observed["steps"]):
        assert step["index"] == index and step["before"] == before, (name, index)
        if step["event"]["kind"] == "receive":
            assert (
                wire.decode_packet(step["event"]["rawIPv4Hex"]).to_dict() == step["decodedInput"]
            ), (
                name,
                index,
            )
        else:
            assert step["decodedInput"] is None, (name, index)
        if step["output"] is not None:
            assert (
                wire.decode_packet(step["output"]["rawIPv4Hex"]).to_dict()
                == step["output"]["decoded"]
            ), (
                name,
                index,
            )
            assert step["decision"]["kind"] == "accepted", (name, index)
            assert step["decision"]["operation"] in ("send", "emitAck"), (name, index)
        before = step["state"]
    assert before == observed["final"], name


def report_case(binary, path, value, expected, name):
    path.write_text(json.dumps(value))
    code = 0 if expected["supported"] else 2
    observed = json.loads(invoke(binary, path, code))
    compare_report(observed, expected, name)


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

    def changed(name, keys, replacement):
        row = copy.deepcopy(value)
        target = row
        for key in keys[:-1]:
            target = target[key]
        target[keys[-1]] = replacement
        rows.append((name, row))

    changed("schema-version", ["schema"], 2)
    changed("schema-type", ["schema"], "1")
    changed("unknown-root-field", ["extra"], 0)
    changed("unknown-seed-field", ["seed", "extra"], 0)
    changed("unknown-core-field", ["seed", "core", "window"], 8)
    changed("unknown-tuple-field", ["seed", "core", "inbound", "extra"], 0)
    changed("events-type", ["events"], {})
    changed("event-type", ["events"], [0])
    changed("event-kind-type", ["events"], [{"kind": 0}])
    changed("event-kind-unknown", ["events"], [{"kind": "connect"}])
    changed("write-extra-field", ["events"], [{"kind": "write", "payloadHex": "", "extra": 0}])
    changed("read-extra-field", ["events"], [{"kind": "read", "count": 0, "extra": 0}])
    changed("send-missing-policy", ["events"], [{"kind": "send", "count": 1}])
    changed("send-policy-type", ["events"], [{"kind": "send", "count": 1, "policyPermitted": 1}])
    changed("ack-policy-type", ["events"], [{"kind": "emitAck", "policyPermitted": "true"}])
    changed(
        "send-negative-count", ["events"], [{"kind": "send", "count": -1, "policyPermitted": True}]
    )
    changed("read-negative-count", ["events"], [{"kind": "read", "count": -1}])
    changed("read-count-type", ["events"], [{"kind": "read", "count": "1"}])
    for name, text in (("odd", "0"), ("nonhex", "gg"), ("separator", "00 00")):
        changed("write-" + name, ["events"], [{"kind": "write", "payloadHex": text}])
        changed("receive-" + name, ["events"], [{"kind": "receive", "rawIPv4Hex": text}])
        changed("pending-" + name, ["seed", "pendingHex"], text)
    changed("write-hex-type", ["events"], [{"kind": "write", "payloadHex": 0}])
    changed("receive-hex-type", ["events"], [{"kind": "receive", "rawIPv4Hex": 0}])
    for field in ("sendWL1", "sendWL2"):
        changed(field + "-overflow", ["seed", field], 1 << 32)
        changed(field + "-negative", ["seed", field], -1)
    for field in ("receiveNext", "sendUna", "sendNext"):
        changed(field + "-overflow", ["seed", "core", field], 1 << 32)
    for field in ("pendingLimit", "sendWindow", "effectiveMSS", "ipSendLimit"):
        changed(field + "-negative", ["seed", field], -1)
    changed("pending-limit-overflow", ["seed", "pendingLimit"], 65536)
    changed("pending-storage-over-limit", ["seed", "pendingHex"], bytes(9).hex())
    changed("peer-window-overflow", ["seed", "sendWindow"], 65536)
    changed("zero-mss", ["seed", "effectiveMSS"], 0)
    changed("mss-ip-limit", ["seed", "effectiveMSS"], 537)
    changed("ip-limit-overflow", ["seed", "ipSendLimit"], 65536)
    changed("send-cursor-relation", ["seed", "core", "sendNext"], 1001)
    changed("local-capacity-overflow", ["seed", "core", "capacity"], 65536)
    changed("local-storage-over-capacity", ["seed", "core", "receivedHex"], bytes(9).hex())
    changed("wrong-protocol", ["seed", "core", "inbound", "protocol"], 17)
    changed("port-overflow", ["seed", "core", "inbound", "sourcePort"], 65536)
    changed("invalid-address", ["seed", "core", "inbound", "source"], "192.0.2.256")
    changed("empty-ip", ["events"], [{"kind": "receive", "rawIPv4Hex": ""}])
    changed("short-ip", ["events"], [{"kind": "receive", "rawIPv4Hex": "00"}])
    received = next(event for event in value["events"] if event["kind"] == "receive")
    raw = bytearray.fromhex(received["rawIPv4Hex"])
    raw[-1] ^= 1
    changed("invalid-tcp-checksum", ["events"], [{"kind": "receive", "rawIPv4Hex": raw.hex()}])
    raw = bytearray.fromhex(received["rawIPv4Hex"])
    raw[8] ^= 1
    changed("invalid-ip-checksum", ["events"], [{"kind": "receive", "rawIPv4Hex": raw.hex()}])
    for name, row in rows:
        error_text(binary, path, json.dumps(row), name)
    text = json.dumps(value)
    error_text(
        binary,
        path,
        text.replace('"schema": 1', '"schema": 1, "schema": 1'),
        "duplicate-root-field",
    )
    error_text(
        binary,
        path,
        text.replace('"pendingLimit": 8', '"pendingLimit": 8, "pendingLimit": 8'),
        "duplicate-seed-field",
    )
    error_text(
        binary,
        path,
        text.replace('"kind": "write"', '"kind": "write", "kind": "write"', 1),
        "duplicate-event-field",
    )
    return len(rows) + 3


def canonical_inputs(binary, path, data):
    received = next(case for case in data["cases"] if case["name"] == "old-ack-data")
    value = {
        "schema": 1,
        "seed": received["seed"],
        "events": [
            {"kind": "write", "payloadHex": "A1B2"},
            {"kind": "receive", "rawIPv4Hex": received["event"]["rawIPv4Hex"].upper()},
        ],
    }
    expected = reference.replay(value["seed"], value["events"])
    assert expected["steps"][0]["event"]["payloadHex"] == "a1b2"
    assert expected["steps"][1]["event"]["rawIPv4Hex"] == received["event"]["rawIPv4Hex"]
    report_case(binary, path, value, expected, "uppercase-processed-events")
    reset = next(case for case in data["cases"] if case["name"] == "scope-reset")
    value = {
        "schema": 1,
        "seed": reset["seed"],
        "events": [
            {"kind": "receive", "rawIPv4Hex": reset["event"]["rawIPv4Hex"].upper()},
            {"kind": "receive", "rawIPv4Hex": "ABCD"},
            {"kind": "write", "payloadHex": "A1B2"},
        ],
    }
    expected = reference.replay(value["seed"], value["events"])
    assert expected["remainingEvents"] == [
        {"kind": "receive", "rawIPv4Hex": "abcd"},
        {"kind": "write", "payloadHex": "a1b2"},
    ]
    report_case(binary, path, value, expected, "uppercase-unread-events")
    return 2


def check(binary=BINARY):
    data = reference.load_fixtures()
    reference.check_fixtures(data)
    counts = {
        "events": 0,
        "window": 0,
        "traces": 0,
        "stops": 0,
        "invalid": 0,
        "invalidSeeds": 0,
        "canonical": 0,
    }
    with tempfile.TemporaryDirectory(prefix="netlib-tcp-endpoint-") as directory:
        path = Path(directory) / "input.json"
        for case in data["cases"]:
            value = {"schema": 1, "seed": case["seed"], "events": [case["event"]]}
            if case["coreOnly"]:
                error_text(binary, path, json.dumps(value), case["name"])
                counts["invalidSeeds"] += 1
                continue
            expected = reference.replay(value["seed"], value["events"])
            assert expected["steps"][0]["decision"] == case["expected"]["decision"]
            report_case(binary, path, value, expected, case["name"])
            counts["events"] += 1
        for case in data["windowCases"]:
            packet = wire.decode_packet(case["rawIPv4Hex"])
            seed = reference.State.from_dict(case["seed"])
            seed = replace(seed, core=replace(seed.core, receive_next=packet.segment.sequence))
            value = {
                "schema": 1,
                "seed": seed.seed_dict(),
                "events": [{"kind": "receive", "rawIPv4Hex": case["rawIPv4Hex"]}],
            }
            expected = reference.replay(value["seed"], value["events"])
            updated = expected["final"]["sendWindow"] != seed.send_window
            assert updated == case["eligible"], case["name"]
            report_case(binary, path, value, expected, case["name"])
            counts["window"] += 1
        for trace in data["traces"]:
            report_case(binary, path, trace["input"], trace["expected"], trace["name"])
            counts["traces"] += 1
            counts["stops"] += not trace["expected"]["supported"]
        value = data["traces"][0]["input"]
        counts["invalid"] = invalid_inputs(binary, path, value)
        counts["canonical"] = canonical_inputs(binary, path, data)
        empty = {"schema": 1, "seed": value["seed"], "events": []}
        report_case(binary, path, empty, reference.replay(empty["seed"], []), "empty-replay")
        path.write_text(json.dumps(value))
        human = subprocess.run(
            [str(binary), "tcp-endpoint", str(path)],
            cwd=ROOT,
            check=False,
            text=True,
            capture_output=True,
        )
        assert human.returncode == 0 and human.stdout.startswith(
            "TCP APPLICATION PROFILE SUPPORTED\n"
        ), human
    print("TCP application CLI comparisons passed: " + json.dumps(counts, sort_keys=True))
    return counts


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--binary", type=Path, default=BINARY)
    check(parser.parse_args().binary)


if __name__ == "__main__":
    main()
