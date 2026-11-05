"""Compare the joint Lean deployment replay with frozen native evidence."""

import copy
import hashlib
import json
import tempfile
from pathlib import Path

from build_campus_examples import OUTPUTS, build
from check_cli import ROOT, invoke

DIRECTORY = ROOT / "examples/campus"
PROJECTION_SOURCES = {
    "scripts/build_replication_examples.py",
    "scripts/build_campus_examples.py",
    "scripts/test_build_campus_examples.py",
    "scripts/check_campus_examples.py",
    "docs/CAMPUS_DEPLOYMENT.md",
    "docs/research/CAMPUS_DEPLOYMENT.md",
}


def provenance_checks():
    path = DIRECTORY / "capture-provenance.json"
    provenance = json.loads(path.read_text())
    assert set(provenance["artifactSHA256"]) == {
        item.relative_to(DIRECTORY).as_posix()
        for item in (DIRECTORY / "native").rglob("*")
        if item.is_file()
    }
    for relative, digest in provenance["artifactSHA256"].items():
        assert hashlib.sha256((DIRECTORY / relative).read_bytes()).hexdigest() == digest, relative
    required = PROJECTION_SOURCES | {
        item.relative_to(ROOT).as_posix()
        for item in DIRECTORY.iterdir()
        if item.is_file() and item != path
    }
    assert set(provenance["projectionSHA256"]) == required
    for group in ("producerSourceSHA256", "verifierSHA256", "recipeSHA256", "projectionSHA256"):
        assert provenance[group], group
        for relative, digest in provenance[group].items():
            assert hashlib.sha256((ROOT / relative).read_bytes()).hexdigest() == digest, relative


def native_checks():
    values = build()
    for name, value in zip(OUTPUTS, values, strict=True):
        assert value == json.loads((DIRECTORY / f"{name}.json").read_text()), name
    evidence, bundle = values
    assert (
        evidence["packetCount"],
        evidence["snapshotCount"],
        evidence["frameCount"],
        evidence["nflogCount"],
        evidence["syncFrameCount"],
        evidence["eapEvidence"]["frameCount"],
    ) == (8, 88, 28, 30, 26, 18)
    report = json.loads(invoke("campus-deployment", DIRECTORY / "bundle.json", "--json"))
    assert (
        report["compliant"]
        and report["complete"]
        and report["scope"] == "checked-wired-campus-deployment"
    )
    assert report["eventCount"] == len(bundle["timeline"]) == 45
    assert len(bundle["authentication"]["events"]) == 21 and len(bundle["handoff"]["events"]) == 23
    assert report["assumptions"] and all(row["equivalent"] for row in report["initialPolicies"])
    final = report["final"]
    assert (final["authenticationConsumed"], final["networkConsumed"]) == (21, 23)
    assert final["withdrawn"] and not final["authorized"] and not final["applicationPermitted"]
    assert final["pendingIDs"] == [] and final["completedIDs"] == [1, 2, 0, 3, 4, 5, 6]
    assert final["archivedPrimary"] == final["primarySnapshot"] and final["archivedPrimary"]
    assert final["owners"] == {"client": "standby", "server": "standby"}
    assert final["configurations"] == {
        "primary": "install-primary-permit",
        "standby": "install-standby-deny",
    }
    forwarded, denied, retired = [], [], []
    for index, row in enumerate(report["findings"]):
        assert row["source"] == f"/timeline/{index}"
        assert row["matched"] and row["topologyMatched"] and row["applicationMatched"]
        if row["policy"]:
            policy = row["policy"]
            assert policy["equivalent"]
            assert policy["afterAuthentication"] == row["before"]["authenticationConsumed"]
            assert policy["afterAuthentication"] == (
                21 if policy["configuration"].endswith("deny") else 19
            )
        if row.get("servedID") is not None:
            retired.append(row["servedID"])
        if row["expected"]:
            (forwarded if row["expected"]["output"] else denied).append(row)
    assert retired == [1, 2, 0, 3, 4, 5, 6] and len(forwarded) == 6 and len(denied) == 2
    old = next(row for row in report["findings"] if row.get("servedID") == 0)
    assert old["assignedGateway"] == "primary" and old["before"]["owners"] == final["owners"]
    assert not old["before"]["withdrawn"]
    assert all(
        row["before"]["withdrawn"] and row["expected"]["disposition"] == "forwardDrop"
        for row in denied
    )
    return bundle, report


def mutation_checks(bundle, baseline):
    count = 0
    with tempfile.TemporaryDirectory(prefix="netlib-campus-oracle-") as temporary:
        path = Path(temporary) / "changed.json"

        def changed(document, code, *, same_final=True):
            nonlocal count
            path.write_text(json.dumps(document))
            output = invoke("campus-deployment", path, "--json", code=code)
            count += 1
            if code != 2:
                result = json.loads(output)
                assert not result["compliant"]
                if same_final:
                    assert result["final"] == baseline["final"]
                return result
            return None

        def network_index(kind, **fields):
            return next(
                i
                for i, event in enumerate(bundle["handoff"]["events"])
                if event["type"] == kind
                and all(event.get(key) == value for key, value in fields.items())
            )

        def timeline_index(network):
            return next(
                i
                for i, row in enumerate(bundle["timeline"])
                if row == {"type": "network", "event": network}
            )

        auth = [i for i, row in enumerate(bundle["timeline"]) if row["type"] == "authentication"]
        net = [i for i, row in enumerate(bundle["timeline"]) if row["type"] == "network"]
        withdrawal = next(
            i for i, row in enumerate(bundle["timeline"]) if row["type"] == "withdraw"
        )
        for position, reference in ((auth[1], 0), (auth[0], 1), (net[1], 0), (net[0], 1)):
            document = copy.deepcopy(bundle)
            document["timeline"][position]["event"] = reference
            changed(document, 2)
        document = copy.deepcopy(bundle)
        document["timeline"].pop(auth[-1])
        result = changed(document, 1, same_final=False)
        assert not result["complete"] and result["final"]["authenticationConsumed"] == 20
        document = copy.deepcopy(bundle)
        document["timeline"].pop(net[-1])
        result = changed(document, 1, same_final=False)
        assert not result["complete"] and result["final"]["pendingIDs"] == [6]
        document = copy.deepcopy(bundle)
        document["timeline"].insert(withdrawal + 1, {"type": "withdraw"})
        changed(document, 2)
        document = copy.deepcopy(bundle)
        operation = document["timeline"].pop(withdrawal)
        document["timeline"].insert(timeline_index(network_index("serve", id=0)), operation)
        changed(document, 2)
        document = copy.deepcopy(bundle)
        after = next(
            row["event"]
            for row in document["timeline"][withdrawal + 1 :]
            if row["type"] == "network"
        )
        last_a = next(
            event["states"]["primary"]
            for event in reversed(document["handoff"]["events"][:after])
            if event["states"]["primary"] is not None
        )
        document["handoff"]["events"][after]["states"]["primary"] = last_a
        changed(document, 2)
        for gateway, config in (
            ("primary", "install-primary-permit"),
            ("standby", "install-standby-permit"),
        ):
            document = copy.deepcopy(bundle)
            document["handoff"]["initialConfigs"][gateway] = config
            result = changed(document, 1)
            assert not all(row["equivalent"] for row in result["initialPolicies"])
            assert result["complete"] and all(row["matched"] for row in result["findings"])
        document = copy.deepcopy(bundle)
        document["authentication"]["context"]["consumer"] = "mallory@campus.example.test"
        changed(document, 1, same_final=False)
        document = copy.deepcopy(bundle)
        credential = next(
            row for row in document["authentication"]["events"] if row["type"] == "install"
        )
        credential["credential"]["subject"] = "mallory@campus.example.test"
        changed(document, 1, same_final=False)
        document = copy.deepcopy(bundle)
        document["application"]["operation"] = "different"
        changed(document, 2)
        document = copy.deepcopy(bundle)
        document["intent"]["requirements"][0]["scope"]["operation"] = "different"
        changed(document, 2)
        document = copy.deepcopy(bundle)
        for requirement in document["intent"]["requirements"]:
            requirement["match"]["sourcePorts"] = {"first": 1, "last": 1}
        result = changed(document, 1)
        assert any(not row["applicationMatched"] for row in result["findings"])
        document = copy.deepcopy(bundle)
        document["intent"]["requirements"] = [
            row for row in document["intent"]["requirements"] if row["id"] != "REPLY"
        ]
        for config in document["handoff"]["configs"]:
            config["forward"]["nftables"] = [
                row
                for row in config["forward"]["nftables"]
                if row.get("rule", {}).get("comment") != "REPLY"
            ]
        reply_ids = {
            event["observedID"]
            for event in document["handoff"]["events"]
            if event["type"] == "admit" and event["direction"] == "reply"
        }
        for event in document["handoff"]["events"]:
            if event["type"] == "serve" and event["id"] in reply_ids:
                event["observed"]["disposition"] = "forwardDrop"
                event["observed"]["output"] = None
        result = changed(document, 1)
        assert result["complete"] and all(row["equivalent"] for row in result["initialPolicies"])
        assert all(row["matched"] and row["topologyMatched"] for row in result["findings"])
        assert any(not row["applicationMatched"] for row in result["findings"])
        document = copy.deepcopy(bundle)
        for routing in document["handoff"]["routing"].values():
            for binding in routing["bindings"]:
                if binding["nextNode"] == "server":
                    binding["nextNode"] = "management"
        result = changed(document, 1)
        assert any(not row["topologyMatched"] for row in result["findings"])
        document = copy.deepcopy(bundle)
        install = next(
            event
            for event in document["handoff"]["events"]
            if event.get("config") == "install-standby-deny"
        )
        install["config"] = "install-standby-permit"
        stale = changed(document, 1, same_final=False)
        templates = {}
        for event in bundle["handoff"]["events"]:
            if event["type"] == "serve" and event["observed"]["output"]:
                templates[event["id"]] = event["observed"]["output"][:28]
        for row in stale["findings"]:
            if row.get("servedID") in (5, 6):
                event = document["handoff"]["events"][row["event"]]
                event["observed"]["disposition"] = "forwarded"
                event["observed"]["output"] = (
                    templates[3 if row["servedID"] == 5 else 4]
                    + row["expected"]["output"]["rawIPv4"]
                )
        result = changed(document, 1, same_final=False)
        for row in result["findings"]:
            if row.get("servedID") in (5, 6):
                assert (
                    row["packetMatched"]
                    and row["tablesMatched"]
                    and not row["policy"]["equivalent"]
                )
                assert row["before"]["authenticationConsumed"] == 21 and row["expected"]["output"]
        assert result["final"]["standby"] == baseline["final"]["standby"]
        document = copy.deepcopy(bundle)
        old = network_index("serve", id=0)
        document["handoff"]["events"][old]["observed"]["output"] = None
        changed(document, 1)
        document = copy.deepcopy(bundle)
        document["handoff"]["events"][old]["rawIPv4"] = next(
            event["rawIPv4"]
            for event in bundle["handoff"]["events"]
            if event.get("observedID") == 1
        )
        changed(document, 1)
        document = copy.deepcopy(bundle)
        document["handoff"]["events"][old]["id"] = 1
        changed(document, 2)
        document = copy.deepcopy(bundle)
        document["handoff"]["initial"] = {}
        changed(document, 2)
        document = copy.deepcopy(bundle)
        document["timeline"].pop(withdrawal)
        changed(document, 2)
        path.write_text(json.dumps(bundle))
        invoke("campus-deployment", path, "--budget", "0", "--json", code=2)
        count += 1
    return count


def check():
    provenance_checks()
    bundle, report = native_checks()
    count = mutation_checks(bundle, report)
    print(
        f"Campus CLI checks passed: 45 joint operations, 21 authentication observations, seven tickets, and {count} negative mutations."
    )


if __name__ == "__main__":
    check()
