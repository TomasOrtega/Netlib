"""Check the compiled standards and data-plane commands locally."""

import hashlib
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


def linux_checks():
    directory = ROOT / "examples/linux"
    for name in ["deployment", "deny-first", "route-drop", "bypass", "management-leak"]:
        passed = name == "deployment"
        result = json.loads(
            invoke("linux", directory / f"{name}.json", "--json", code=0 if passed else 1)
        )
        assert result["report"]["compliant"] == passed
        assert result["scope"] == "main-table-ipv4-transit" and result["assumptions"]
        assert len(result["routers"]) == 4
        gateway = next(r for r in result["routers"] if r["node"] == "gateway")
        assert gateway["routes"] and gateway["firewallRules"]
        assert gateway["routes"][0]["source"] == "/routers/1/routes/0"
        assert gateway["firewallRules"][0]["source"].startswith("/routers/1/nftables/nftables/")
        assert gateway["firewallRules"][0]["expressionIndices"]
    for name, query, code in [
        ("deployment", "AVAILABLE", 0),
        ("deployment", "IDENTITY", 0),
        ("deployment", "GATEWAY", 0),
        ("bypass", "IDENTITY", 1),
        ("bypass", "GATEWAY", 1),
        ("route-drop", "AVAILABLE", 1),
    ]:
        result = json.loads(
            invoke(
                "linux-traffic",
                directory / f"{name}.json",
                query,
                directory / "https-class.json",
                "--json",
                code=code,
            )
        )
        assert result["report"]["compliant"] == (code == 0)
        assert result["report"]["scope"] == "all-selected-packets"
    invoke(
        "linux-traffic",
        directory / "deployment.json",
        "AVAILABLE",
        directory / "https-class.json",
        "--budget",
        "0",
        code=2,
    )
    invoke("compile-acl", directory / "conflicting-intent.json", code=1)
    invoke("compile-acl", directory / "intent.json", "--budget", "0", code=2)
    invoke("compile-acl", directory / "intent.json", "--budget", "invalid", code=2)
    generated = json.loads(invoke("compile-acl", directory / "intent.json"))
    assert generated["nftables"][0]["metainfo"]["version"] == "1.1.3"
    assert generated["nftables"][3]["rule"]["comment"] == "HTTPS"
    captured = json.loads(invoke("compile-acl", directory / "captured-compiler-intent.json"))
    assert captured == json.loads((directory / "captured-compiler-input.json").read_text())
    with tempfile.TemporaryDirectory(prefix="netlib-linux-") as temporary:
        path = Path(temporary) / "deployment.json"
        bundle = json.loads((directory / "deployment.json").read_text())
        bundle["routers"][1]["nftables"] = generated
        path.write_text(json.dumps(bundle))
        assert json.loads(invoke("linux", path, "--json"))["report"]["compliant"]
        assert json.loads(
            invoke("linux-traffic", path, "AVAILABLE", directory / "https-class.json", "--json")
        )["report"]["compliant"]
        bundle["intent"]["links"] = []
        path.write_text(json.dumps(bundle))
        invoke("linux", path, code=2)
        invalid = Path(temporary) / "intent.json"
        policy = json.loads((directory / "intent.json").read_text())
        policy["requirements"][0]["match"]["protocol"] = None
        invalid.write_text(json.dumps(policy))
        invoke("compile-acl", invalid, code=2)
        invalid.write_text('{"schema":0,"schema":1,"requirements":[]}')
        invoke("compile-acl", invalid, code=2)


def stateful_checks():
    nat = ROOT / "examples/nat"
    for path in sorted(nat.glob("*.json")):
        passed = path.stem in {"secure", "udp", "alias-reuse"}
        invalid = path.stem in {"invalid-clock", "forged-authority"}
        code = 2 if invalid else 0 if passed else 1
        output = invoke("nat-trace", path, "--json", code=code)
        if not invalid:
            report = json.loads(output)
            assert report["compliant"] == passed and report["scope"] == "local-source-napt-trace"
            assert len(report["findings"]) == len(json.loads(path.read_text())["events"])
            assert all(row["source"] == f"/events/{i}" for i, row in enumerate(report["findings"]))
            assert all(row["matched"] for row in report["findings"]) == passed
    reuse = json.loads(invoke("nat-trace", nat / "alias-reuse.json", "--json"))
    assert reuse["findings"][-1]["observed"]["destination"] == "10.0.0.2"
    assert reuse["findings"][-1]["observed"]["destinationPort"] == 41000
    invoke("nat-trace", nat / "secure.json", "--budget", "0", code=2)
    transfer = ROOT / "examples/transfer"
    for path in sorted(transfer.glob("*.json")):
        passed = path.stem in {"dnat", "cycle", "mediated", "isolation"}
        report = json.loads(invoke("transfer", path, "--json", code=0 if passed else 1))
        assert report["compliant"] == passed
        assert report["scope"] == "fixed-input-header-changing-forwarding"
        assert report["stateCount"] <= 4096
        assert report["path"] is not None or report["cut"] is not None or report["endpointGateway"]
    rewritten = json.loads(invoke("transfer", transfer / "dnat.json", "--json"))
    assert rewritten["path"][0]["packet"]["destinationPort"] == 80
    assert rewritten["path"][-1]["packet"]["destinationPort"] == 443
    assert rewritten["path"][-1]["packet"]["destination"] == "198.51.100.10"
    bypass = json.loads(invoke("transfer", transfer / "gateway-bypass.json", "--json", code=1))
    assert all(state["node"] != "firewall" for state in bypass["path"])
    invoke("transfer", transfer / "dnat.json", "--budget", "0", code=2)
    invoke("transfer", transfer / "dnat.json", "--budget", "invalid", code=2)
    with tempfile.TemporaryDirectory(prefix="netlib-transfer-") as directory:
        path = Path(directory) / "invalid.json"
        model = json.loads((transfer / "dnat.json").read_text())
        model["links"][0]["rewrite"]["destination"] = "198.51.100.256"
        path.write_text(json.dumps(model))
        invoke("transfer", path, code=2)
        model = json.loads((transfer / "dnat.json").read_text())
        model["query"]["gateways"] = ["firewall"]
        path.write_text(json.dumps(model))
        invoke("transfer", path, code=2)


def conntrack_checks():
    directory = ROOT / "examples/conntrack"
    provenance = json.loads((directory / "capture-provenance.json").read_text())
    for relative, digest in provenance["files"].items():
        assert hashlib.sha256((ROOT / relative).read_bytes()).hexdigest() == digest, relative
    for name in ["conntrack.xml", "netlink.json"]:
        snapshot = directory / "native" / name
        report = json.loads(invoke("conntrack", snapshot, directory / "intent.json", "--json"))
        assert report["compliant"] and report["entryCount"] == 4
        assert report["scope"] == "reported-original-flow-policy"
        assert len({finding["source"] for finding in report["findings"]}) == 4
        assert all(finding["permittedByIntent"] for finding in report["findings"])
        denied = json.loads(
            invoke("conntrack", snapshot, directory / "tcp-only.json", "--json", code=1)
        )
        assert sum(not finding["permittedByIntent"] for finding in denied["findings"]) == 2
    invoke(
        "conntrack",
        directory / "native/netlink.json",
        directory / "intent.json",
        "--budget",
        "0",
        code=2,
    )
    invoke(
        "conntrack-map",
        directory / "native/conntrack.xml",
        "0",
        directory / "original.json",
        code=2,
    )
    invoke(
        "conntrack-map",
        directory / "native/netlink.json",
        "65536",
        directory / "original.json",
        code=2,
    )
    invoke(
        "conntrack-map",
        directory / "native/netlink.json",
        "invalid",
        directory / "original.json",
        code=2,
    )
    observations = json.loads((directory / "native/packets.json").read_text())
    assert observations["replyTupleOrigin"] == "reverse-of-observed-server-wire-tuple"
    assert observations["noReply"] == ["collision", "postrouting-drop"]
    with tempfile.TemporaryDirectory(prefix="netlib-conntrack-") as folder:
        header = Path(folder) / "header.json"
        for packet in observations["packets"]:
            for direction, output in [("original", "wire"), ("reply", "restored")]:
                header.write_text(json.dumps(packet[direction]))
                result = json.loads(
                    invoke(
                        "conntrack-map", directory / "native/netlink.json", "0", header, "--json"
                    )
                )
                assert result["associated"] and result["direction"] == direction
                assert result["output"] == packet[output] and result["nativeStatus"] is not None
        result = json.loads(
            invoke(
                "conntrack-map", directory / "native/netlink.json", "1", header, "--json", code=1
            )
        )
        assert not result["associated"] and result["output"] is None
        raw = json.loads((directory / "native/netlink.json").read_text())
        raw["entries"][0]["status"] &= ~16
        invalid = Path(folder) / "bad-status.json"
        invalid.write_text(json.dumps(raw))
        invoke("conntrack-map", invalid, "0", header, code=2)


def main():
    traffic_checks()
    linux_checks()
    stateful_checks()
    conntrack_checks()
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
    print(
        f"Profile CLI checks passed for {count} fixtures and extended packet, stateful, and conntrack commands."
    )


if __name__ == "__main__":
    main()
