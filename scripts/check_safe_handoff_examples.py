"""Compare the compiled outstanding-ticket replay with frozen native evidence."""

import copy
import hashlib
import json
import tempfile
from pathlib import Path

from build_safe_handoff_examples import OUTPUTS, build
from check_cli import ROOT, invoke

DIRECTORY = ROOT / "examples/safe-handoff"
PROJECTION_SOURCES = {
    "scripts/build_replication_examples.py",
    "scripts/build_safe_handoff_examples.py",
    "scripts/test_build_safe_handoff_examples.py",
    "scripts/check_safe_handoff_examples.py",
    "docs/SAFE_HANDOFF.md",
    "docs/research/SAFE_GATEWAY_HANDOFF.md",
}


def provenance_checks():
    path = DIRECTORY / "capture-provenance.json"
    provenance = json.loads(path.read_text())
    assert set(provenance["artifactSHA256"]) == {
        artifact.relative_to(DIRECTORY).as_posix()
        for artifact in (DIRECTORY / "native").rglob("*")
        if artifact.is_file()
    }
    for relative, digest in provenance["artifactSHA256"].items():
        assert hashlib.sha256((DIRECTORY / relative).read_bytes()).hexdigest() == digest, relative
    required = PROJECTION_SOURCES | {
        artifact.relative_to(ROOT).as_posix()
        for artifact in DIRECTORY.iterdir()
        if artifact.is_file() and artifact != path
    }
    assert set(provenance["projectionSHA256"]) == required
    for group in ["producerSourceSHA256", "verifierSHA256", "recipeSHA256", "projectionSHA256"]:
        assert provenance[group], group
        for relative, digest in provenance[group].items():
            assert hashlib.sha256((ROOT / relative).read_bytes()).hexdigest() == digest, relative


def native_checks():
    values = build()
    for name, value in zip(OUTPUTS, values, strict=True):
        assert value == json.loads((DIRECTORY / f"{name}.json").read_text()), name
    evidence, replay = values
    assert (
        evidence["packetCount"],
        evidence["snapshotCount"],
        evidence["frameCount"],
        evidence["nflogCount"],
        evidence["syncFrameCount"],
    ) == (7, 84, 26, 27, 30)
    assert evidence["queuePendingCounts"] == [1, 1, 1, 1, 0, 1, 1, 0]
    report = json.loads(invoke("wire-safe-handoff", DIRECTORY / "replay.json", "--json"))
    assert report["compliant"] and report["scope"] == "inflight-safe-gateway-handoff"
    assert report["assumptions"] and report["eventCount"] == len(replay["events"]) == 20
    final = report["final"]
    assert len(final["primary"]) == len(final["standby"]) == 1
    assert not final["primary"][0]["seenReply"] and final["standby"][0]["seenReply"]
    assert (
        final["completedIDs"] == [1, 2, 0, 3, 4, 5]
        and final["pending"] == []
        and final["nextID"] == 6
    )
    assert final["owners"] == {"client": "standby", "server": "standby"} and final["fenced"] == [
        "primary"
    ]
    assert final["configurations"] == {"primary": "initial-primary", "standby": "install-permit"}
    assert final["outstanding"] == {"primary": 0, "standby": 0}
    assigned, retired, outputs = [], [], []
    observed = 0
    for index, (event, finding) in enumerate(
        zip(replay["events"], report["findings"], strict=True)
    ):
        assert finding["source"] == f"/events/{index}" and finding["type"] == event["type"]
        assert finding["matched"] and finding["stateMatched"]
        assert finding["primaryObserved"] == (event["states"]["primary"] is not None)
        assert finding["standbyObserved"] == (event["states"]["standby"] is not None)
        observed += finding["primaryObserved"] + finding["standbyObserved"]
        assert finding["expectedState"]["epoch"] == index + 1
        if finding["admitted"]:
            ticket = finding["admitted"]
            assert ticket["id"] == event["observedID"] and ticket["rawIPv4"] == event["rawIPv4"]
            assert ticket["routeEpoch"] == index
            assigned.append(ticket["id"])
        if finding["served"]:
            retired.append(finding["served"]["ticket"]["id"])
        if finding["expected"]:
            outputs.append(finding["expected"])
            assert (finding["expected"]["output"] is not None) == (
                event["observed"]["output"] is not None
            )
    assert observed == 32 and assigned == list(range(6)) and retired == [1, 2, 0, 3, 4, 5]
    assert sum(row["output"] is not None for row in outputs) == 6
    old = next(
        row for row in report["findings"] if row["served"] and row["served"]["ticket"]["id"] == 0
    )
    assert old["served"]["ticket"]["gateway"] == "primary"
    assert old["expectedState"]["owners"] == {"client": "standby", "server": "standby"}
    denied = next(
        row for row in report["findings"] if row["served"] and row["served"]["ticket"]["id"] == 3
    )
    assert denied["served"]["configuration"] == "install-deny"
    assert (
        denied["expected"]["classification"] == "established"
        and denied["expected"]["disposition"] == "forwardDrop"
    )
    return replay, report


def mutation_checks(replay, baseline):
    count = 0
    with tempfile.TemporaryDirectory(prefix="netlib-safe-handoff-oracle-") as temporary:
        path = Path(temporary) / "changed.json"

        def changed(document, code, *, unchanged=True):
            nonlocal count
            path.write_text(json.dumps(document))
            result = invoke("wire-safe-handoff", path, "--json", code=code)
            count += 1
            if code != 2:
                report = json.loads(result)
                assert not report["compliant"]
                if unchanged:
                    assert report["final"] == baseline["final"]
                return report
            return None

        def locate(kind, *, id=None):
            return next(
                index
                for index, row in enumerate(replay["events"])
                if row["type"] == kind and (id is None or row.get("id") == id)
            )

        old = locate("serve", id=0)
        fence = locate("fence")
        commit = locate("commit")
        first_handoff = locate("handoff")
        denied = locate("serve", id=3)
        changed_input = next(
            row["rawIPv4"]
            for row in replay["events"]
            if row["type"] == "admit" and row["observedID"] == 1
        )
        altered = copy.deepcopy(replay)
        operation = altered["events"].pop(fence)
        altered["events"].insert(old, operation)
        changed(altered, 2)
        altered = copy.deepcopy(replay)
        operation = altered["events"].pop(first_handoff)
        altered["events"].insert(commit, operation)
        changed(altered, 2)
        altered = copy.deepcopy(replay)
        server_route = next(
            i
            for i, row in enumerate(altered["events"])
            if row["type"] == "handoff" and row["leg"] == "server"
        )
        altered["events"].pop(server_route)
        changed(altered, 2)
        altered = copy.deepcopy(replay)
        altered["events"][old]["id"] = 1
        changed(altered, 2)
        altered = copy.deepcopy(replay)
        altered["events"][old]["id"] = 99
        changed(altered, 2)
        altered = copy.deepcopy(replay)
        altered["events"][old]["rawIPv4"] = changed_input
        changed(altered, 1)
        altered = copy.deepcopy(replay)
        source = next(
            row for row in altered["events"] if row["type"] == "admit" and row["observedID"] == 0
        )
        source["rawIPv4"] = changed_input
        report = changed(altered, 1)
        assert report["findings"][old]["served"]["ticket"]["rawIPv4"] == changed_input
        altered = copy.deepcopy(replay)
        source = next(row for row in altered["events"] if row["type"] == "admit")
        source["observedID"] = 99
        changed(altered, 1)
        altered = copy.deepcopy(replay)
        altered["events"][commit]["states"]["standby"]["entries"] = []
        changed(altered, 1)
        altered = copy.deepcopy(replay)
        altered["events"][1]["cache"] = []
        changed(altered, 1)
        altered = copy.deepcopy(replay)
        altered["events"][1]["cache"][0]["sourceNAT"]["port"] = 40001
        changed(altered, 1)
        altered = copy.deepcopy(replay)
        policy = next(
            row
            for row in altered["events"]
            if row["type"] == "install" and row["config"] == "install-deny"
        )
        policy["config"] = "initial-standby"
        report = changed(altered, 1)
        assert report["findings"][denied]["expected"]["output"] is not None
        altered = copy.deepcopy(replay)
        altered["events"][old]["observed"]["output"] = None
        changed(altered, 1)
        altered = copy.deepcopy(replay)
        altered["events"][old]["observed"]["output"] = altered["events"][-1]["observed"]["output"]
        changed(altered, 1)
        altered = copy.deepcopy(replay)
        altered["initial"] = altered["events"][commit]["states"]
        changed(altered, 2)
        altered = copy.deepcopy(replay)
        altered["events"][commit]["timeout"] = 0
        changed(altered, 2)
        altered = copy.deepcopy(replay)
        altered["events"][commit]["timeout"] = 2**32
        changed(altered, 2)
        altered = copy.deepcopy(replay)
        raw = bytearray.fromhex(altered["events"][0]["rawIPv4"])
        raw[10] ^= 1
        altered["events"][0]["rawIPv4"] = raw.hex()
        changed(altered, 2)
        altered = copy.deepcopy(replay)
        altered["events"][0]["zone"] = 1
        changed(altered, 2)
        altered = copy.deepcopy(replay)
        altered["initialConfigs"]["primary"] = "unknown"
        changed(altered, 2)
        altered = copy.deepcopy(replay)
        altered["events"][1]["key"]["sourcePort"] = 41001
        changed(altered, 2)
        altered = copy.deepcopy(replay)
        altered["events"].pop(1)
        changed(altered, 2)
    return count


def check():
    provenance_checks()
    replay, report = native_checks()
    count = mutation_checks(replay, report)
    print(
        f"Safe handoff CLI checks passed: 20 operations, six outstanding tickets, and {count} negative mutations."
    )


if __name__ == "__main__":
    check()
