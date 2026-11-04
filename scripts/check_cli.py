"""Exercise the compiled CLI and compare it with an independent graph oracle."""

import json
import random
import subprocess
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
BINARY = ROOT / ".lake/build/bin/netlib"


def invoke(*args, code=0):
    result = subprocess.run(
        [str(BINARY), *map(str, args)], cwd=ROOT, text=True, capture_output=True
    )
    assert result.returncode == code, (args, result.returncode, result.stdout, result.stderr)
    return result.stdout


def closure(nodes, links, service, removed=frozenset()):
    # Floyd-Warshall is independent of the checker's path/cut search.
    reachable = {(a, a) for a in nodes if a not in removed}
    reachable.update(
        (link["from"], link["to"])
        for link in links
        if link["enabled"]
        and link["service"] in (service, "*")
        and link["from"] not in removed
        and link["to"] not in removed
    )
    for k in nodes:
        for a in nodes:
            for b in nodes:
                if (a, k) in reachable and (k, b) in reachable:
                    reachable.add((a, b))
    return reachable


def main():
    invoke("demo")
    secure = json.loads(
        invoke("check", "examples/secure.json", "examples/requirements.netlib", "--json")
    )
    assert secure["compliant"] and all(r["passed"] for r in secure["requirements"])
    bypass = json.loads(
        invoke("check", "examples/bypass.json", "examples/requirements.netlib", "--json", code=1)
    )
    assert [r["id"] for r in bypass["requirements"] if not r["passed"]] == ["INNER", "OUTER"]
    assert any("path red -> black" in e for f in bypass["observations"] for e in f["evidence"])
    invoke("analyze", "examples/requirements.netlib", "examples/goals.netlib")
    incomplete = invoke("analyze", "examples/incomplete.netlib", "examples/goals.netlib", code=1)
    assert "Missing explicit goals: 1" in incomplete and "G_OUTER" in incomplete
    inconsistent = invoke("analyze", "examples/contradictory.netlib", code=1)
    assert "INCONSISTENT" in inconsistent and "does not assess its goals" in inconsistent
    redundant = invoke("analyze", "examples/redundant.netlib")
    assert "Redundant requirements under fixed domain laws: FIRST" in redundant
    formal = invoke("formalize", "examples/requirements.netlib")
    assert "line 2" in formal and "source:" in formal
    invoke("check", "nonexistent-config.json", "examples/requirements.netlib", code=2)
    invoke("unknown-command", code=2)

    rng = random.Random(2713)
    comparisons = 0
    with tempfile.TemporaryDirectory(prefix="netlib-cli-") as directory:
        config_path = Path(directory) / "config.json"
        policy_path = Path(directory) / "policy.netlib"
        for _ in range(12):
            nodes = [f"n{i}" for i in range(5)]
            links = [
                {
                    "from": a,
                    "to": b,
                    "service": rng.choice(["tls", "ssh", "*"]),
                    "enabled": rng.random() < 0.8,
                }
                for a in nodes
                for b in nodes
                if rng.random() < 0.3
            ]
            gateways = set(rng.sample(nodes, 2))
            config_path.write_text(
                json.dumps(
                    {
                        "devices": [{"id": a, "zone": "all", "role": "device"} for a in nodes],
                        "links": links,
                        "groups": [{"name": "g", "members": sorted(gateways)}],
                    }
                )
            )
            requirements = []
            expected = []
            for service in ["tls", "ssh"]:
                reachable = closure(nodes, links, service)
                bypasses = closure(nodes, links, service, gateways)
                for a in nodes:
                    for b in nodes:
                        for clause, passed in [
                            (f"node:{a} must reach node:{b} for {service}.", (a, b) in reachable),
                            (
                                f"node:{a} must be isolated from node:{b} for {service}.",
                                (a, b) not in reachable,
                            ),
                            (
                                f"node:{a} must traverse group:g before node:{b} for {service}.",
                                (a, b) not in bypasses,
                            ),
                        ]:
                            requirements.append(f"R{len(requirements)}: {clause}")
                            expected.append(passed)
            policy_path.write_text("\n".join(requirements) + "\n")
            report = json.loads(invoke("check", config_path, policy_path, "--json", code=1))
            actual = [r["passed"] for r in report["requirements"]]
            assert actual == expected, [
                (r, a, e) for r, a, e in zip(requirements, actual, expected) if a != e
            ]
            comparisons += len(expected)
        policy_path.write_text("R: node:missing must reach node:n0 for tls.\n")
        invoke("check", config_path, policy_path, code=2)
        config_path.write_text('{"devices": [], "links": [], "groups": []}')
        invoke("check", config_path, policy_path, code=2)
    print(f"CLI checks passed; {comparisons} observations matched the graph oracle.")


if __name__ == "__main__":
    main()
