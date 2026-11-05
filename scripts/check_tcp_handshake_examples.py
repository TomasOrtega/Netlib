"""Compare the compiled startup CLI with independent static TCP results.

This manual helper does not send packets or collect captures.
"""

import argparse
import copy
import json
import subprocess
import tempfile
from pathlib import Path

import tcp_handshake_reference as reference
import tcp_receive_reference as wire

ROOT = Path(__file__).resolve().parent.parent
BINARY = ROOT / ".lake/build/bin/netlib"
SCOPE = "tcp-startup-projection"


def invoke(binary, path, code):
    result = subprocess.run(
        [str(binary), "tcp-handshake", str(path), "--json"],
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
    assert observed["scope"] == SCOPE, name
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
    before = observed["initial"]
    for index, step in enumerate(observed["steps"]):
        assert step["index"] == index and step["before"] == before, (name, index)
        event = step["event"]
        if step["decodedInput"] is not None:
            packet = wire.decode_packet(event["rawIPv4Hex"])
            assert packet.to_dict() == step["decodedInput"], (name, index)
        if step["output"] is not None:
            output = step["output"]
            assert wire.decode_packet(output["rawIPv4Hex"]).to_dict() == output["decoded"], (
                name,
                index,
            )
            assert step["decision"]["kind"] == "accepted", (name, index)
            assert event["kind"] in ("activeOpen", "listenSyn", "synSentSynAck"), (name, index)
        if step["delivery"] is not None:
            delivery = step["delivery"]
            assert 0 <= delivery["sourceIndex"] < index, (name, index)
            source = observed["steps"][delivery["sourceIndex"]]["output"]
            assert source is not None, (name, index)
            if delivery["path"] == "rewrite":
                packet = wire.decode_packet(event["rawIPv4Hex"])
                source = reference.rewrite_output(source, packet.header, packet.ttl)
            else:
                assert delivery["path"] == "direct", (name, index)
            assert event["rawIPv4Hex"] == source["rawIPv4Hex"], (name, index)
        if step["decision"]["kind"] != "accepted":
            assert step["state"] == before, (name, index)
            assert step["output"] is None and step["delivery"] is None, (name, index)
        for role in ("active", "passive"):
            seed = step["state"][role + "Seed"]
            if seed is not None:
                assert reference.application.State.from_dict(seed).valid, (name, index, role)
                assert step["state"][role + "Phase"] == "ESTABLISHED", (name, index, role)
                assert step["state"][role + "EstablishedAt"] <= index, (name, index, role)
        before = step["state"]
    assert before == observed["final"], name
    assert observed["exchangeComplete"] == (observed["final"]["passivePhase"] == "ESTABLISHED"), (
        name
    )
    if observed["exchangeComplete"]:
        final = observed["final"]
        assert final["activeEstablishedAt"] < final["passiveEstablishedAt"], name
        assert (
            final["activeSeed"]["core"]["receiveNext"] == final["passiveSeed"]["core"]["sendNext"]
        ), name
        assert (
            final["passiveSeed"]["core"]["receiveNext"] == final["activeSeed"]["core"]["sendNext"]
        ), name


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

    for name, replacement in (("version", 2), ("type", "1"), ("bool", True), ("negative", -1)):
        changed("schema-" + name, ["schema"], replacement)
    changed("unknown-root-field", ["seed"], {})
    changed("supplied-active-state", ["activeSeed"], {})
    changed("supplied-final-state", ["final"], {})
    for role in ("active", "passive"):
        changed(role + "-unknown-field", [role, "effectiveMSS"], 536)
        changed(role + "-unknown-socket-field", [role, "socket", "extra"], 0)
        changed(role + "-large-capacity", [role, "capacity"], 65536)
        changed(role + "-negative-capacity", [role, "capacity"], -1)
        changed(role + "-large-pending", [role, "pendingLimit"], 65536)
        changed(role + "-negative-pending", [role, "pendingLimit"], -1)
        changed(role + "-zero-data-limit", [role, "ipSendLimit"], 40)
        changed(role + "-ip-limit-overflow", [role, "ipSendLimit"], 65536)
        changed(role + "-iss-overflow", [role, "iss"], 1 << 32)
        changed(role + "-iss-negative", [role, "iss"], -1)
        changed(role + "-iss-type", [role, "iss"], "1")
        changed(role + "-address-invalid", [role, "socket", "address"], "192.0.2.256")
        changed(role + "-port-overflow", [role, "socket", "port"], 65536)
        changed(role + "-port-negative", [role, "socket", "port"], -1)
    changed("events-type", ["events"], {})
    changed("event-type", ["events"], [0])
    changed("event-kind-type", ["events", 0, "kind"], 0)
    changed("event-kind-unknown", ["events", 0, "kind"], "open")
    changed("open-extra-field", ["events", 0, "output"], {})
    changed("remote-extra-field", ["events", 0, "remote", "extra"], 0)
    changed("remote-port-overflow", ["events", 0, "remote", "port"], 65536)
    changed("remote-address-invalid", ["events", 0, "remote", "address"], "192.0.2.256")
    for index in (0, 1, 2):
        changed("policy-type-" + str(index), ["events", index, "policyPermitted"], 1)
    for index in (1, 2, 3):
        changed("raw-type-" + str(index), ["events", index, "rawIPv4Hex"], 0)
        changed("path-unknown-" + str(index), ["events", index, "path"], "packet")
        changed("path-type-" + str(index), ["events", index, "path"], 0)
        changed("supplied-source-" + str(index), ["events", index, "sourceIndex"], 0)
        for label, text in (("odd", "0"), ("nonhex", "gg"), ("separator", "00 00")):
            changed("hex-" + str(index) + "-" + label, ["events", index, "rawIPv4Hex"], text)
    changed("final-ack-policy-field", ["events", 3, "policyPermitted"], True)
    for name, keys in (
        ("missing-active", ["active"]),
        ("missing-events", ["events"]),
        ("missing-local-socket", ["active", "socket"]),
        ("missing-remote", ["events", 0, "remote"]),
        ("missing-path", ["events", 1, "path"]),
        ("missing-output-policy", ["events", 2, "policyPermitted"]),
    ):
        row = copy.deepcopy(value)
        target = row
        for key in keys[:-1]:
            target = target[key]
        del target[keys[-1]]
        rows.append((name, row))
    for name, row in rows:
        error_text(binary, path, json.dumps(row), name)
    text = json.dumps(value)
    mutations = (
        ("duplicate-root-field", text.replace('"schema": 1', '"schema": 1, "schema": 1')),
        ("duplicate-local-field", text.replace('"capacity": 8', '"capacity": 8, "capacity": 8', 1)),
        (
            "duplicate-event-field",
            text.replace('"kind": "activeOpen"', '"kind": "activeOpen", "kind": "activeOpen"', 1),
        ),
        ("decimal-schema", text.replace('"schema": 1', '"schema": 1.0')),
        ("decimal-iss", text.replace('"iss": 1000', '"iss": 1000.0')),
    )
    for name, mutated in mutations:
        error_text(binary, path, mutated, name)
    return len(rows) + len(mutations)


def check(binary=BINARY):
    data = reference.load_fixtures()
    reference.check_fixtures(data)
    counts = {"traces": 0, "complete": 0, "stops": 0, "errors": 0, "invalid": 0}
    with tempfile.TemporaryDirectory(prefix="netlib-tcp-handshake-") as directory:
        path = Path(directory) / "input.json"
        for case in data["traces"]:
            report_case(binary, path, case["input"], case["expected"], case["name"])
            counts["traces"] += 1
            counts["complete"] += case["expected"]["exchangeComplete"]
            counts["stops"] += not case["expected"]["supported"]
        for case in data["errorCases"]:
            error_text(binary, path, json.dumps(case["input"]), case["name"])
            counts["errors"] += 1
        counts["invalid"] = invalid_inputs(binary, path, data["traces"][0]["input"])
        path.write_text(json.dumps(data["traces"][0]["input"]))
        human = subprocess.run(
            [str(binary), "tcp-handshake", str(path)],
            cwd=ROOT,
            check=False,
            text=True,
            capture_output=True,
        )
        assert human.returncode == 0 and human.stdout.startswith(
            "TCP STARTUP PROFILE SUPPORTED\n"
        ), human
    print("TCP startup CLI comparisons passed: " + json.dumps(counts, sort_keys=True))
    return counts


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--binary", type=Path, default=BINARY)
    check(parser.parse_args().binary)


if __name__ == "__main__":
    main()
