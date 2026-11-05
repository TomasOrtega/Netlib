"""Compare compiled ingress and timeout checks with frozen native projections."""

import copy
import hashlib
import json
import tempfile
from pathlib import Path

from build_reassembly_examples import OUTPUTS, build
from check_cli import ROOT, invoke

DIRECTORY = ROOT / "examples/reassembly"
PROJECTION_SOURCES = {
    "scripts/build_admission_examples.py",
    "scripts/build_reassembly_examples.py",
    "scripts/test_build_reassembly_examples.py",
    "scripts/check_reassembly_examples.py",
    "scripts/check_reassembly_native_examples.py",
    "scripts/reassembly_reference.py",
    "docs/REASSEMBLY.md",
    "docs/research/IPV4_INPUT_REASSEMBLY.md",
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
    for group in [
        "producerSourceSHA256",
        "verifierSHA256",
        "recipeSHA256",
        "projectionSHA256",
    ]:
        assert provenance[group], group
        for relative, digest in provenance[group].items():
            assert hashlib.sha256((ROOT / relative).read_bytes()).hexdigest() == digest, relative


def native_checks():
    projections = build()
    for name, value in zip(OUTPUTS, projections, strict=True):
        assert value == json.loads((DIRECTORY / f"{name}.json").read_text()), name
    evidence, _, session, replay, controls = projections
    assert (
        evidence["eventCount"],
        evidence["fragmentCount"],
        evidence["nflogCount"],
        evidence["frameCount"],
        evidence["stateObservationCount"],
        evidence["timeoutEmissionCount"],
    ) == (82, 79, 107, 266, 73, 2)
    assert len(session["snapshots"]) == 4
    ingress = json.loads(invoke("wire-reassembly", DIRECTORY / "replay.json", "--json"))
    timeout = json.loads(invoke("wire-reassembly-timeouts", DIRECTORY / "timeout.json", "--json"))
    assert ingress["compliant"] and timeout["compliant"]
    assert ingress["eventCount"] == timeout["eventCount"] == len(replay["events"]) == 82
    assert ingress["scope"] == "ipv4-ingress-reassembly-forwarding" and ingress["assumptions"]
    assert timeout["scope"] == "ipv4-reassembly-timeout-controls" and timeout["assumptions"]
    assert ingress["final"] == timeout["final"] and len(ingress["final"]) == 3
    assert ingress["pendingQueues"] == timeout["pendingQueues"] == 0
    assert sum(finding["stateObserved"] for finding in ingress["findings"]) == 73
    assert sum(finding["reassembled"] is not None for finding in ingress["findings"]) == 22
    previous = []
    outcomes = {}
    for index, (event, finding, control) in enumerate(
        zip(replay["events"], ingress["findings"], timeout["findings"], strict=True)
    ):
        assert finding["source"] == f"/events/{index}"
        assert control["source"] == f"/controls/{index}"
        assert finding["matched"] and finding["stateMatched"] and control["matched"]
        assert finding["stateObserved"] == (event["state"] is not None)
        assert finding["expectedState"] == control["expectedState"]
        assert finding["pendingQueues"] == control["pendingQueues"]
        if event["type"] == "fragment":
            assert (finding["reassembled"] is not None) == (
                event["observed"]["reassembled"] is not None
            )
            if finding["expected"] is None:
                assert finding["expectedState"] == previous
                assert event["observed"]["forwarded"] == []
            else:
                expected = finding["expected"]
                assert (expected["output"] is not None) == bool(event["observed"]["forwarded"])
                outcomes[expected["disposition"]] = outcomes.get(expected["disposition"], 0) + 1
                if expected["output"]:
                    assert expected["output"]["ttl"] + 1 == finding["reassembled"]["ttl"]
                    assert expected["fragmentSizeCap"] <= expected["routeMTU"]
                    if expected["reassembled"]:
                        assert expected["fragmentSizeCap"] <= expected["maxSize"]
        previous = finding["expectedState"]
    assert outcomes["forwarded"] > 0 and outcomes["forwardDrop"] > 0
    sent = [
        finding
        for row in timeout["findings"]
        for finding in row["expired"]
        if finding["disposition"] == "sent"
    ]
    assert len(sent) == 2 and {finding["user"] for finding in sent} == {2, 12}
    for finding in sent:
        assert finding["classification"] == "invalid"
        assert finding["output"]["wireLength"] == 576
        assert len(bytes.fromhex(finding["output"]["quoteHex"])) == 548
        assert finding["output"]["wireLength"] <= finding["output"]["returnMTU"]
    assert sum(len(row["observed"]) for row in controls["controls"]) == 2
    assert json.loads(invoke("eap", DIRECTORY / "authentication.json", "--json"))["compliant"]
    identity = json.loads(invoke("session-firewall", DIRECTORY / "session.json", "--json"))
    assert identity["compliant"] and identity["authenticationMatches"]
    return replay, controls, ingress, timeout


def mutation_checks(replay, controls, ingress, timeout):
    count = 0
    with tempfile.TemporaryDirectory(prefix="netlib-reassembly-native-oracle-") as temporary:
        path = Path(temporary) / "changed.json"

        def changed(command, document, code):
            nonlocal count
            path.write_text(json.dumps(document))
            value = invoke(command, path, "--json", code=code)
            count += 1
            return json.loads(value) if code != 2 else None

        complete = next(
            index
            for index, event in enumerate(replay["events"])
            if event["type"] == "fragment" and event["observed"]["forwarded"]
        )
        altered = copy.deepcopy(replay)
        altered["events"][complete]["observed"]["forwarded"] = []
        report = changed("wire-reassembly", altered, 1)
        assert report["final"] == ingress["final"] and report["pendingQueues"] == 0
        assert [i for i, row in enumerate(report["findings"]) if not row["matched"]] == [complete]
        altered = copy.deepcopy(replay)
        altered["events"][complete]["observed"]["reassembled"] = None
        report = changed("wire-reassembly", altered, 1)
        assert report["final"] == ingress["final"]
        observed_state = next(
            index
            for index, event in enumerate(replay["events"])
            if event["state"] and event["state"]["entries"]
        )
        altered = copy.deepcopy(replay)
        altered["events"][observed_state]["state"]["entries"] = []
        report = changed("wire-reassembly", altered, 1)
        assert not report["findings"][observed_state]["stateMatched"]
        assert report["final"] == ingress["final"]
        emission = next(index for index, row in enumerate(controls["controls"]) if row["observed"])
        altered = copy.deepcopy(controls)
        altered["controls"][emission]["observed"] = []
        report = changed("wire-reassembly-timeouts", altered, 1)
        assert report["final"] == timeout["final"] and report["pendingQueues"] == 0
        assert [i for i, row in enumerate(report["findings"]) if not row["matched"]] == [emission]
        altered = copy.deepcopy(controls)
        allocation = altered["controls"][emission]["identifications"][0]
        allocation["identification"] = (allocation["identification"] + 1) % 65536
        report = changed("wire-reassembly-timeouts", altered, 1)
        assert report["final"] == timeout["final"]
        altered = copy.deepcopy(controls)
        altered["controls"][emission]["identifications"] = []
        changed("wire-reassembly-timeouts", altered, 2)
        altered = copy.deepcopy(controls)
        altered["controls"][emission]["identifications"] *= 2
        changed("wire-reassembly-timeouts", altered, 2)
        altered = copy.deepcopy(controls)
        altered["controls"][emission]["event"] += 1
        changed("wire-reassembly-timeouts", altered, 2)
    return count


def check():
    provenance_checks()
    replay, controls, ingress, timeout = native_checks()
    count = mutation_checks(replay, controls, ingress, timeout)
    print(
        f"Native reassembly CLI checks passed: 82 events, 73 table observations, "
        f"two timeout errors, and {count} negative CLI mutations."
    )


if __name__ == "__main__":
    check()
