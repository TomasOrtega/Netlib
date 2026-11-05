"""Check the compiled standards and data-plane commands locally."""

import json
import tempfile
from pathlib import Path

from check_cli import ROOT, invoke


def catalogue(report):
    assert report["findings"]
    for finding in report["findings"]:
        assert finding["id"] and finding["statement"] and finding["applicability"]
        assert set(finding["source"]) == {"document", "version", "clause", "url"}
        assert all(finding["source"].values())
        assert finding["status"] in {
            "satisfied",
            "violated",
            "unsupported",
            "missing evidence",
            "not applicable",
        }


def traffic_checks():
    config = ROOT / "examples/dataplane/secure.json"
    selection = ROOT / "examples/traffic/https.json"
    for query in ["AVAILABLE", "IDENTITY", "GATEWAY"]:
        report = json.loads(invoke("traffic", config, query, selection, "--json"))
        assert report["compliant"] and report["scope"] == "all-selected-packets"
        assert report["partitionCells"] > 0 and report["evidence"]
    report = json.loads(
        invoke("traffic", config, "AVAILABLE", ROOT / "examples/traffic/all.json", "--json", code=1)
    )
    assert not report["compliant"]
    for query in ["IDENTITY", "GATEWAY"]:
        report = json.loads(
            invoke(
                "traffic",
                ROOT / "examples/dataplane/bypass.json",
                query,
                selection,
                "--json",
                code=1,
            )
        )
        assert not report["compliant"]
    invoke("traffic", config, "AVAILABLE", selection, "--budget", "0", code=2)
    invoke("traffic", config, "AVAILABLE", selection, "--budget", "invalid", code=2)
    invoke("traffic", config, "UNKNOWN", selection, code=2)
    with tempfile.TemporaryDirectory(prefix="netlib-traffic-") as directory:
        path = Path(directory) / "model.json"
        model = json.loads(config.read_text())
        deny = {
            "match": {
                **json.loads(selection.read_text()),
                "sourcePorts": {"first": 50001, "last": 50001},
            },
            "action": "deny",
        }
        model["links"][1]["acl"].insert(0, deny)
        path.write_text(json.dumps(model))
        assert json.loads(invoke("dataplane", path, "--json"))["compliant"]
        report = json.loads(invoke("traffic", path, "AVAILABLE", selection, "--json", code=1))
        assert not report["compliant"]
        assert any("50001" in line for line in report["evidence"])
        invalid = Path(directory) / "invalid.json"
        invalid.write_text(json.dumps({**json.loads(selection.read_text()), "ignored": True}))
        invoke("traffic", config, "AVAILABLE", invalid, code=2)


def main():
    traffic_checks()
    count = 0
    for path in sorted((ROOT / "examples/dataplane").glob("*.json")):
        passed = path.stem == "secure"
        report = json.loads(invoke("dataplane", path, "--json", code=0 if passed else 1))
        assert report["compliant"] == passed
        assert len(report["requirements"]) >= 3
        assert all(r["evidence"] and r["pairs"] > 0 for r in report["requirements"])
        count += 1
    errors = {"invalid-clock", "unsupported-revocation"}
    for path in sorted((ROOT / "examples/5g").glob("*.json")):
        passed = path.stem in {"secure", "correct-denial"}
        code = 2 if path.stem in errors else 0 if passed else 1
        output = invoke("fiveg", path, "--json", code=code)
        if code != 2:
            report = json.loads(output)
            catalogue(report)
            assert report["compliant"] == passed
        count += 1
    for path in sorted((ROOT / "examples/wifi").glob("*.conf")):
        passed = path.stem == "secure"
        code = 2 if path.stem in {"duplicate", "unsupported"} else 0 if passed else 1
        output = invoke("wifi", path, "--json", code=code)
        if code != 2:
            report = json.loads(output)
            catalogue(report)
            assert report["compliant"] == passed
        count += 1
    for path in sorted((ROOT / "examples/wifi").glob("*.json")):
        passed = path.stem == "deployment"
        code = 2 if path.stem in {"binding-mismatch", "missing-obligation"} else 0 if passed else 1
        output = invoke("wifi", "examples/wifi/secure.conf", path, "--json", code=code)
        if code != 2:
            report = json.loads(output)
            catalogue(report)
            assert report["compliant"] == passed
            assert any(f["id"] == "WIFI-MANAGEMENT" for f in report["findings"])
        count += 1
    for command in ["wifi-coverage", "fiveg-coverage"]:
        report = json.loads(invoke(command, "--json", code=1))
        catalogue(report)
        assert not report["complete"] and not report["compliant"]
    with tempfile.TemporaryDirectory(prefix="netlib-policy-") as directory:
        policy = Path(directory) / "large.netlib"
        goals = Path(directory) / "goals.netlib"
        policy.write_text(
            "\n".join(
                f"R{i}: node:a must traverse group:g{i} before node:b for tls." for i in range(40)
            )
            + "\n"
        )
        goals.write_text("G: node:a must traverse group:g0 before node:b for tls.\n")
        output = invoke("analyze", policy, goals, "--budget", "100000")
        assert "CONSISTENT" in output and "Missing explicit goals: 0" in output
        invoke("analyze", policy, "--budget", "0", code=2)
        invoke("analyze", policy, goals, "--budget", "1", code=2)
        invoke("analyze", policy, "--budget", "invalid", code=2)
    print(f"Profile CLI checks passed for {count} fixtures and both coverage reports.")


if __name__ == "__main__":
    main()
