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


def main():
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
