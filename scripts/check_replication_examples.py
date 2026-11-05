"""Compare the compiled handoff replay with frozen native projections and corruptions."""

import copy
import hashlib
import json
import tempfile
from pathlib import Path

from build_replication_examples import OUTPUTS, build
from check_cli import ROOT, invoke

DIRECTORY = ROOT / "examples/replication"
PROJECTION_SOURCES = {
    "scripts/build_replication_examples.py",
    "scripts/test_build_replication_examples.py",
    "scripts/check_replication_examples.py",
    "docs/STATEFUL_FAILOVER.md",
    "docs/research/NATIVE_STATEFUL_FAILOVER.md",
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
    evidence, replay = build()
    for name, value in zip(OUTPUTS, (evidence, replay), strict=True):
        assert value == json.loads((DIRECTORY / f"{name}.json").read_text()), name
    assert (
        evidence["packetCount"],
        evidence["snapshotCount"],
        evidence["nflogCount"],
        evidence["syncFrameCount"],
    ) == (6, 56, 16, 12)
    report = json.loads(invoke("wire-failover", DIRECTORY / "replay.json", "--json"))
    assert report["compliant"] and report["scope"] == "ordered-native-stateful-failover"
    assert report["assumptions"] and report["eventCount"] == len(replay["events"]) == 11
    final = report["final"]
    assert len(final["primary"]) == len(final["standby"]) == 1
    assert not final["primary"][0]["seenReply"] and final["standby"][0]["seenReply"]
    assert final["owners"] == {"client": "standby", "server": "standby"}
    assert final["fenced"] == ["primary"] and final["epoch"] == 11
    assert final["cacheSourceEpoch"] == 1 and not final["cache"][0]["seenReply"]
    packets = []
    for index, (event, finding) in enumerate(
        zip(replay["events"], report["findings"], strict=True)
    ):
        assert finding["source"] == f"/events/{index}"
        assert finding["matched"] and finding["stateMatched"]
        assert finding["primaryObserved"] and finding["standbyObserved"]
        assert finding["cacheObserved"] == (index == 1)
        assert finding["expectedState"]["epoch"] == index + 1
        if index >= 1:
            assert finding["expectedState"]["cacheSourceEpoch"] == 1
        assert len(finding["expectedState"]["standby"]) == int(index >= 6)
        if event["type"] == "packet":
            expected = finding["expected"]
            assert (expected["output"] is not None) == (event["observed"]["output"] is not None)
            packets.append(expected)
        else:
            assert finding["expected"] is None
    assert [row["classification"] for row in packets] == [
        "new",
        "new",
        "established",
        "established",
        "established",
        "established",
    ]
    assert [row["disposition"] for row in packets] == [
        "forwarded",
        "routeDrop",
        "forwardDrop",
        "forwarded",
        "forwarded",
        "forwarded",
    ]
    return replay, report


def mutation_checks(replay, baseline):
    count = 0
    with tempfile.TemporaryDirectory(prefix="netlib-replication-oracle-") as temporary:
        path = Path(temporary) / "changed.json"

        def changed(document, code, *, unchanged=True):
            nonlocal count
            path.write_text(json.dumps(document))
            result = invoke("wire-failover", path, "--json", code=code)
            count += 1
            if code != 2:
                report = json.loads(result)
                assert not report["compliant"]
                if unchanged:
                    assert report["final"] == baseline["final"]
                return report
            return None

        altered = copy.deepcopy(replay)
        altered["events"][0]["observed"]["output"] = None
        changed(altered, 1)
        altered = copy.deepcopy(replay)
        altered["events"][0]["observed"]["output"] = altered["events"][-1]["observed"]["output"]
        changed(altered, 1)
        altered = copy.deepcopy(replay)
        altered["events"][6]["states"]["standby"]["entries"] = []
        changed(altered, 1)
        altered = copy.deepcopy(replay)
        altered["events"][1]["cache"] = []
        changed(altered, 1)
        altered = copy.deepcopy(replay)
        altered["events"][1]["cache"][0]["sourceNAT"]["port"] = 40001
        changed(altered, 1)
        altered = copy.deepcopy(replay)
        altered["events"][7]["states"]["standby"]["entries"][0]["status"] &= ~2
        changed(altered, 1)
        altered = copy.deepcopy(replay)
        altered["events"][1]["key"]["sourcePort"] = 41001
        changed(altered, 2)
        altered = copy.deepcopy(replay)
        altered["events"].pop(1)
        changed(altered, 2)
        altered = copy.deepcopy(replay)
        altered["events"][6]["timeout"] = 0
        changed(altered, 2)
        altered = copy.deepcopy(replay)
        altered["initial"] = altered["events"][6]["states"]
        changed(altered, 2)
        altered = copy.deepcopy(replay)
        altered["events"][5]["gateway"] = "primary"
        changed(altered, 2)
        altered = copy.deepcopy(replay)
        altered["events"][3]["gateway"] = "primary"
        altered["events"][5]["gateway"] = "primary"
        changed(altered, 2)
        altered = copy.deepcopy(replay)
        altered["events"].insert(7, copy.deepcopy(altered["events"][6]))
        changed(altered, 2)
        altered = copy.deepcopy(replay)
        raw = bytearray.fromhex(altered["events"][0]["rawIPv4"])
        raw[10] ^= 1
        altered["events"][0]["rawIPv4"] = raw.hex()
        changed(altered, 2)
        altered = copy.deepcopy(replay)
        altered["events"][0]["config"] = "unknown"
        changed(altered, 2)
        altered = copy.deepcopy(replay)
        altered["events"][0]["zone"] = 1
        changed(altered, 2)
        altered = copy.deepcopy(replay)
        altered["events"].pop(3)
        changed(altered, 2)
        altered = copy.deepcopy(replay)
        permit = next(row for row in altered["configs"] if row["id"] == "permitted")
        denied = next(row for row in altered["configs"] if row["id"] == "denied")
        denied["forward"] = copy.deepcopy(permit["forward"])
        changed(altered, 1)
    return count


def check():
    provenance_checks()
    replay, report = native_checks()
    count = mutation_checks(replay, report)
    print(
        f"Native failover CLI checks passed: 11 operations, six datagrams, and {count} negative CLI mutations."
    )


if __name__ == "__main__":
    check()
