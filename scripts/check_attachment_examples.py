"""Compare compiled attachment replay with frozen evidence and contradictions."""

import argparse
import copy
import hashlib
import json
import tempfile
from pathlib import Path

from build_attachment_bundle import DIRECTORY, OUTPUTS, build
from check_cli import ROOT, invoke

PROJECTION_SOURCES = {
    "scripts/build_replication_examples.py",
    "scripts/build_attachment_bundle.py",
    "scripts/test_build_attachment_bundle.py",
    "scripts/check_attachment_examples.py",
    "docs/INGRESS_ATTACHMENTS.md",
    "docs/research/INGRESS_ATTACHMENTS.md",
}


def provenance_checks(directory):
    path = directory / "capture-provenance.json"
    provenance = json.loads(path.read_text())
    assert set(provenance["artifactSHA256"]) == {
        item.relative_to(directory).as_posix()
        for item in (directory / "native").rglob("*")
        if item.is_file()
    }
    for relative, digest in provenance["artifactSHA256"].items():
        assert hashlib.sha256((directory / relative).read_bytes()).hexdigest() == digest, relative
    required = PROJECTION_SOURCES | {
        item.relative_to(ROOT).as_posix()
        for item in directory.iterdir()
        if item.is_file() and item != path
    }
    assert set(provenance["projectionSHA256"]) == required
    for group in ("producerSourceSHA256", "verifierSHA256", "recipeSHA256", "projectionSHA256"):
        assert provenance[group], group
        for relative, digest in provenance[group].items():
            assert hashlib.sha256((ROOT / relative).read_bytes()).hexdigest() == digest, relative


def native_checks(directory):
    values = build(directory)
    for name, value in zip(OUTPUTS, values, strict=True):
        assert value == json.loads((directory / f"{name}.json").read_text()), name
    evidence, _ = values
    bundle = json.loads((directory / "bundle.json").read_text())
    assert (
        evidence["packetCount"],
        evidence["snapshotCount"],
        evidence["frameCount"],
        evidence["nflogCount"],
        evidence["syncFrameCount"],
    ) == (15, 142, 44, 51, 54)
    report = json.loads(invoke("attachment-campus", directory / "bundle.json", "--json"))
    assert report["compliant"] and report["complete"]
    assert report["scope"] == "checked-interface-bound-campus-suffix" and report["assumptions"]
    assert report["eventCount"] == len(bundle["timeline"]) == 62
    assert len(bundle["authentication"]["events"]) == 21 and len(bundle["handoff"]["events"]) == 23
    assert all(row["matched"] for row in report["findings"])
    final = report["final"]
    assert final["guardedSuffix"] and final["resetObserved"] and final["withdrawn"]
    assert not final["authorized"] and not final["applicationPermitted"]
    assert final["pendingIDs"] == [] and final["completedIDs"] == [1, 2, 0, 3, 4, 5, 6]
    assert final["archivedPrimary"] == final["primarySnapshot"] and final["archivedPrimary"]
    owners = final["historicalOwners"]
    assert owners["primary"] == owners["standby"]
    assert owners["primary"]["origin"]["afterAuthentication"] == 19
    assert owners["primary"]["origin"]["principal"] == report["subject"]
    outputs = [row for row in report["findings"] if row.get("expected")]
    assert len(outputs) == 7 and all(row["expected"]["output"] for row in outputs)
    unsafe = [row for row in outputs if not row["before"]["guardedSuffix"]]
    assert len(unsafe) == 1 and not unsafe[0]["guard"]["equivalent"]
    rejected = [
        row for row in report["findings"] if (row.get("guard") or {}).get("actualAllowed") is False
    ]
    assert len(rejected) == 8
    for row in rejected:
        assert row["before"]["guardedSuffix"] and row["guard"]["equivalent"]
        assert not row["ordinaryExecuted"] and row["expected"] is None
        assert row["before"]["primarySnapshot"] == row["after"]["primarySnapshot"]
        assert row["before"]["standby"] == row["after"]["standby"]
    retired = [row for row in rejected if row["type"] == "earlyRejectedServe"]
    assert [row["retiredID"] for row in retired] == [5, 6]
    assert all(row["before"]["withdrawn"] and not row["before"]["authorized"] for row in retired)
    return bundle, report


def mutation_checks(bundle, baseline):
    count = 0
    with tempfile.TemporaryDirectory(prefix="netlib-attachment-cli-") as temporary:
        path = Path(temporary) / "changed.json"

        def changed(document, code, *, same_final=True):
            nonlocal count
            path.write_text(json.dumps(document))
            output = invoke("attachment-campus", path, "--json", code=code)
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
                index
                for index, row in enumerate(bundle["handoff"]["events"])
                if row["type"] == kind
                and all(row.get(key) == value for key, value in fields.items())
            )

        serves = [row for row in bundle["handoff"]["events"] if row["type"] == "serve"]
        for field, value in (("classification", "established"), ("fresh", False)):
            document = copy.deepcopy(bundle)
            document["handoff"]["events"][network_index("serve", id=5)]["observed"][field] = value
            result = changed(document, 1)
            assert (
                next(row for row in result["findings"] if row.get("retiredID") == 5)["expected"]
                is None
            )

        document = copy.deepcopy(bundle)
        document["handoff"]["events"][network_index("serve", id=5)]["rawIPv4"] = serves[0][
            "rawIPv4"
        ]
        result = changed(document, 1)
        assert (
            next(row for row in result["findings"] if row.get("retiredID") == 5)["ordinaryExecuted"]
            is False
        )

        document = copy.deepcopy(bundle)
        first_probe = next(row for row in document["timeline"] if row["type"] == "probe")
        first_probe["guard"] = False
        result = changed(document, 1)
        assert next(row for row in result["findings"] if row["type"] == "probe")["expected"][
            "output"
        ]

        document = copy.deepcopy(bundle)
        deny = next(
            index
            for index, row in enumerate(document["timeline"])
            if row["type"] == "installGuard" and row["guard"].endswith("deny")
        )
        document["timeline"].pop(deny)
        result = changed(document, 1)
        stale = [
            row
            for row in result["findings"]
            if row["before"]["guardedSuffix"]
            and row.get("guard")
            and not row["guard"]["equivalent"]
        ]
        assert len(stale) == 2 and all(row["ordinaryExecuted"] for row in stale)
        assert all(row["guard"]["actualAllowed"] and row["expected"]["output"] for row in stale)

        document = copy.deepcopy(bundle)
        document["timeline"] = [row for row in document["timeline"] if row["type"] != "protect"]
        result = changed(document, 1, same_final=False)
        assert not result["complete"] and not result["final"]["guardedSuffix"]

        for kind in ("reset", "authentication"):
            document = copy.deepcopy(bundle)
            position = next(
                index for index, row in enumerate(document["timeline"]) if row["type"] == kind
            )
            document["timeline"].pop(position)
            changed(document, 2)

        document = copy.deepcopy(bundle)
        document["attachments"][1]["id"] = document["attachments"][0]["id"]
        changed(document, 2)
        document = copy.deepcopy(bundle)
        document["live"].append(document["live"][0])
        changed(document, 2)
        document = copy.deepcopy(bundle)
        document["timeline"][0]["invented"] = True
        changed(document, 2)
        document = copy.deepcopy(bundle)
        document["guards"][0]["namespace"]["birth"] += 1
        changed(document, 2)
        path.write_text(json.dumps(bundle))
        invoke("attachment-campus", path, "--budget", "0", code=2)
        invoke("attachment-campus", path, "--budget", "invalid", code=2)
    return count


def check(directory=DIRECTORY, *, provenance=True):
    directory = Path(directory)
    if provenance:
        provenance_checks(directory)
    bundle, report = native_checks(directory)
    count = mutation_checks(bundle, report)
    print(f"Checked attachment replay, eight early drops, and {count} CLI contradictions.")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("directory", nargs="?", type=Path, default=DIRECTORY)
    parser.add_argument("--skip-provenance", action="store_true")
    arguments = parser.parse_args()
    check(arguments.directory, provenance=not arguments.skip_provenance)


if __name__ == "__main__":
    main()
