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


def lifecycle_checks():
    from build_lifecycle_example import build
    from check_lifecycle_capture import selected_rule

    directory = ROOT / "examples/lifecycle"
    provenance = json.loads((directory / "capture-provenance.json").read_text())
    for relative, digest in provenance["files"].items():
        assert hashlib.sha256((ROOT / relative).read_bytes()).hexdigest() == digest, relative
    evidence, replay = build()
    assert evidence == json.loads((directory / "checked-evidence.json").read_text())
    assert replay == json.loads((directory / "replay.json").read_text())
    result = json.loads(invoke("lifecycle", directory / "replay.json", "--json"))
    assert result["compliant"] and result["eventCount"] == 10 and len(result["findings"]) == 10
    assert result["scope"] == "ordinary-forwarded-packet-lifecycle" and result["final"] == []
    assert all(finding["matched"] for finding in result["findings"])
    assert sum(finding["stateObserved"] for finding in result["findings"]) == 8
    cached = result["findings"][3]["expected"]
    assert cached["classification"] == "new" and not cached["fresh"]
    assert cached["afterDestination"]["destinationPort"] == 9000
    assert cached["afterSource"]["sourcePort"] == 40000
    seen = result["findings"][4]
    assert seen["expected"]["output"] is None and seen["expectedState"][0]["seenReply"]
    initial = directory / "native/forward-initial.json"
    established = directory / "native/forward-established-only.json"
    refined = json.loads(invoke("stateful-refines", established, initial, "--json"))
    assert refined["refines"] and refined["scope"] == "all-state-header-filter-refinement"
    cells = refined["partitionCells"]
    invoke("stateful-refines", established, initial, "--budget", str(cells))
    invoke("stateful-refines", established, initial, "--budget", str(cells - 1), code=2)
    invoke("stateful-refines", established, initial, "--budget", "invalid", code=2)
    witness = json.loads(invoke("stateful-refines", initial, established, "--json", code=1))[
        "counterexample"
    ]
    for path, expected in [(initial, "accept"), (established, "drop")]:
        document = json.loads(path.read_text())
        assert selected_rule(
            document, "netlib_filter", "forward", witness["state"], witness["packet"]
        )[1] == {expected: None}
    invoke("stateful-refines", directory / "native/late.json", initial, code=2)
    with tempfile.TemporaryDirectory(prefix="netlib-lifecycle-") as folder:
        path = Path(folder) / "changed.json"
        altered = json.loads(json.dumps(replay))
        altered["events"][3]["observed"]["fresh"] = True
        path.write_text(json.dumps(altered))
        failed = json.loads(invoke("lifecycle", path, "--json", code=1))
        assert not failed["findings"][3]["matched"] and failed["findings"][4]["matched"]
        altered = json.loads(json.dumps(replay))
        altered["events"][4]["state"]["entries"][0]["status"] &= ~2
        path.write_text(json.dumps(altered))
        failed = json.loads(invoke("lifecycle", path, "--json", code=1))
        assert not failed["findings"][4]["stateMatched"] and failed["findings"][5]["matched"]
        altered = json.loads(json.dumps(replay))
        altered["configs"][0]["late"]["nftables"][2]["chain"]["prio"] = 100
        path.write_text(json.dumps(altered))
        invoke("lifecycle", path, code=2)


def revocation_checks():
    from build_revocation_example import build
    from check_lifecycle_capture import selected_rule

    directory = ROOT / "examples/revocation"
    provenance = json.loads((directory / "capture-provenance.json").read_text())
    for relative, digest in provenance["files"].items():
        assert hashlib.sha256((ROOT / relative).read_bytes()).hexdigest() == digest, relative
    evidence, replay, forbidden, start = build()
    for name, expected in [
        ("checked-evidence", evidence),
        ("replay", replay),
        ("forbidden", forbidden),
    ]:
        assert expected == json.loads((directory / (name + ".json")).read_text())
    assert start == 3 and evidence["traceCount"] == 6 and evidence["snapshotCount"] == 7
    selection = directory / "forbidden.json"
    trace = directory / "replay.json"
    args = ["lifecycle-blocks", trace, selection]
    report = json.loads(invoke(*args, "--from", str(start), "--json"))
    assert report["compliant"] and report["barrierCertified"] and report["observationsAgree"]
    assert report["scope"] == "post-cutover-output-exclusion" and len(report["barriers"]) == 3
    findings = report["replay"]["findings"]
    assert len(findings) == 7 and all(finding["stateObserved"] for finding in findings)
    assert findings[2]["expected"]["output"]["destinationPort"] == 9000
    assert findings[3]["expected"]["classification"] == "established"
    assert not findings[3]["expected"]["fresh"] and findings[3]["expected"]["output"] is None
    assert findings[3]["expectedState"] and not findings[4]["expectedState"]
    assert findings[6]["expected"]["afterSource"]["destinationPort"] == 9003
    cells = report["partitionCells"]
    assert cells == sum(barrier["partitionCells"] for barrier in report["barriers"])
    invoke(*args, "--from", str(start), "--budget", str(cells))
    invoke(*args, "--from", str(start), "--budget", str(cells - 1), code=2)
    for value in ["-1", "invalid", str(len(replay["events"]))]:
        invoke(*args, "--from", value, code=2)
    invoke(*args, "--budget", "invalid", code=2)
    before = json.loads(invoke(*args, "--json", code=1))
    assert before["observationsAgree"] and not before["barrierCertified"]
    with tempfile.TemporaryDirectory(prefix="netlib-revocation-") as folder:
        path = Path(folder) / "changed.json"
        altered = json.loads(json.dumps(replay))
        hidden = json.loads(json.dumps(altered["configs"][2]))
        hidden["id"] = "unsafe-hidden-context"
        hidden["late"] = altered["configs"][0]["late"]
        altered["configs"].append(hidden)
        altered["events"][5]["config"] = hidden["id"]
        path.write_text(json.dumps(altered))
        failed = json.loads(
            invoke("lifecycle-blocks", path, selection, "--from", str(start), "--json", code=1)
        )
        assert failed["observationsAgree"] and not failed["barrierCertified"]
        unsafe = next(barrier for barrier in failed["barriers"] if not barrier["blocks"])
        witness = unsafe["counterexample"]
        assert witness["packet"]["destination"] == "198.51.100.2"
        assert witness["packet"]["protocol"] == 17
        chain = next(item["chain"] for item in hidden["late"]["nftables"] if "chain" in item)
        assert selected_rule(
            hidden["late"], chain["table"], chain["name"], witness["state"], witness["packet"]
        )[1] == {"accept": None}
        altered = json.loads(json.dumps(replay))
        altered["events"][0]["observed"]["fresh"] = False
        path.write_text(json.dumps(altered))
        failed = json.loads(
            invoke("lifecycle-blocks", path, selection, "--from", str(start), "--json", code=1)
        )
        assert failed["barrierCertified"] and not failed["observationsAgree"]
        assert failed["replay"]["findings"][3]["matched"]
        altered = json.loads(json.dumps(replay))
        altered["events"][3]["observed"]["output"] = altered["events"][2]["observed"]["output"]
        path.write_text(json.dumps(altered))
        failed = json.loads(
            invoke("lifecycle-blocks", path, selection, "--from", str(start), "--json", code=1)
        )
        assert failed["barrierCertified"] and not failed["observationsAgree"]
        altered = json.loads(json.dumps(replay))
        altered["events"] = altered["events"][:5]
        path.write_text(json.dumps(altered))
        invoke("lifecycle-blocks", path, selection, "--from", "4", code=2)
        malformed = Path(folder) / "selection.json"
        malformed.write_text(json.dumps({**forbidden, "ignored": True}))
        invoke("lifecycle-blocks", trace, malformed, "--from", str(start), code=2)


def buffered_checks():
    from build_drain_example import build

    directory = ROOT / "examples/drain"
    provenance = json.loads((directory / "capture-provenance.json").read_text())
    for relative, digest in provenance["files"].items():
        assert hashlib.sha256((ROOT / relative).read_bytes()).hexdigest() == digest, relative
    evidence, replay, forbidden, start, drained_at = build()
    for name, expected in [
        ("checked-evidence", evidence),
        ("replay", replay),
        ("forbidden", forbidden),
    ]:
        assert expected == json.loads((directory / (name + ".json")).read_text())
    assert evidence["oldReceivedAfterInstall"] and evidence["queueCounts"] == [0, 1, 1, 0]
    trace, selection = directory / "replay.json", directory / "forbidden.json"
    args = ["buffered-lifecycle", trace, selection, "--from", str(start), "--drained-at"]
    result = json.loads(invoke(*args, str(drained_at), "--json"))
    assert result["compliant"] and result["ready"] and result["observationsAgree"]
    assert result["scope"] == "buffered-cutover-delivery-exclusion" and result["barrierCertified"]
    assert result["cutoverBacklog"] == result["serviceCapacity"] == 1
    assert result["remainingOldBound"] == 0 and result["pendingAtDeliveryBoundary"] == []
    findings = result["replay"]["findings"]
    assert len(findings) == 3 and findings[0]["admitted"] == findings[2]["served"]
    assert findings[1]["admitted"] == [] and findings[1]["beforePending"] == findings[0]["admitted"]
    assert findings[1]["operation"]["expected"]["classification"] == "new"
    assert not findings[1]["operation"]["expected"]["fresh"]
    assert result["replay"]["delivered"][0]["destination"] == "198.51.100.2"
    premature = json.loads(invoke(*args, str(drained_at - 1), "--json", code=1))
    assert premature["barrierCertified"] and premature["observationsAgree"]
    assert not premature["ready"] and not premature["drainBudgetSufficient"]
    before = json.loads(
        invoke(
            "buffered-lifecycle",
            trace,
            selection,
            "--from",
            "0",
            "--drained-at",
            "3",
            "--json",
            code=1,
        )
    )
    assert before["observationsAgree"] and not before["barrierCertified"]
    cells = result["partitionCells"]
    invoke(*args, str(drained_at), "--budget", str(cells))
    invoke(*args, str(drained_at), "--budget", str(cells - 1), code=2)
    invoke(*args, str(drained_at), "--budget", "invalid", code=2)
    for boundary in ["0", "4", "-1", "invalid"]:
        invoke(*args, boundary, code=2)
    invoke("buffered-lifecycle", trace, selection, "--from", "3", "--drained-at", "3", code=2)
    invoke("buffered-lifecycle", trace, selection, "--from", "2", "--drained-at", "3", code=2)
    with tempfile.TemporaryDirectory(prefix="netlib-buffered-") as folder:
        path = Path(folder) / "changed.json"
        altered = json.loads(json.dumps(replay))
        altered["schedule"][0]["pending"] = []
        path.write_text(json.dumps(altered))
        failed = json.loads(
            invoke(
                "buffered-lifecycle",
                path,
                selection,
                "--from",
                "1",
                "--drained-at",
                "3",
                "--json",
                code=1,
            )
        )
        assert failed["ready"] and not failed["observationsAgree"]
        assert failed["replay"]["findings"][1]["matched"]
        altered = json.loads(json.dumps(replay))
        altered["schedule"][2]["served"] = []
        path.write_text(json.dumps(altered))
        failed = json.loads(
            invoke(
                "buffered-lifecycle",
                path,
                selection,
                "--from",
                "1",
                "--drained-at",
                "3",
                "--json",
                code=1,
            )
        )
        assert failed["ready"] and not failed["observationsAgree"]
        assert failed["replay"]["delivered"] == result["replay"]["delivered"]
        altered = json.loads(json.dumps(replay))
        altered["schedule"].pop(0)
        path.write_text(json.dumps(altered))
        invoke("buffered-lifecycle", path, selection, "--from", "0", "--drained-at", "2", code=2)


def eap_checks():
    from build_eap_examples import build

    directory = ROOT / "examples/eap"
    provenance = json.loads((directory / "capture-provenance.json").read_text())
    for relative, digest in provenance["artifactSHA256"].items():
        assert hashlib.sha256((directory / relative).read_bytes()).hexdigest() == digest, relative
    for group in ["verifierSHA256", "projectionSHA256"]:
        for relative, digest in provenance[group].items():
            assert hashlib.sha256((ROOT / relative).read_bytes()).hexdigest() == digest, relative
    evidence, traces = build()
    assert evidence == json.loads((directory / "checked-evidence.json").read_text())
    assert evidence["frameCount"] == 32 and evidence["outerIdentity"] != evidence["subject"]
    reports = {}
    for name, trace in traces.items():
        assert trace == json.loads((directory / (name + ".json")).read_text())
        report = json.loads(invoke("eap", directory / (name + ".json"), "--json"))
        assert (
            report["compliant"] and report["scope"] == "eap-derived-session-observation-agreement"
        )
        assert report["sources"] and report["assumptions"]
        assert not report["final"]["authorized"] and not report["final"]["sessionAuthenticated"]
        reports[name] = report
    assert reports["success"]["eventCount"] == 20 and reports["bad-server"]["eventCount"] == 16
    findings = reports["success"]["findings"]
    assert not findings[16]["expected"]["authorized"] and findings[17]["expected"]["authorized"]
    assert findings[17]["expected"]["methodEvidence"]["subject"] == evidence["subject"]
    assert (
        not findings[18]["expected"]["authorized"]
        and not findings[19]["expected"]["credentialPresent"]
    )
    assert not any(
        finding["expected"]["authorized"] for finding in reports["bad-server"]["findings"]
    )
    with tempfile.TemporaryDirectory(prefix="netlib-eap-") as folder:
        path = Path(folder) / "changed.json"
        for field, value in [
            ("round", 1),
            ("subject", evidence["outerIdentity"]),
            ("accepted", False),
            ("method", 4),
        ]:
            altered = json.loads(json.dumps(traces["success"]))
            altered["events"][17][field] = value
            path.write_text(json.dumps(altered))
            failed = json.loads(invoke("eap", path, "--json", code=1))
            assert not failed["findings"][17]["matched"]
            assert not failed["findings"][17]["expected"]["authorized"]
            assert failed["findings"][19]["matched"]
        altered = json.loads(json.dumps(traces["success"]))
        altered["events"][16]["authorized"] = True
        path.write_text(json.dumps(altered))
        failed = json.loads(invoke("eap", path, "--json", code=1))
        assert failed["findings"][17]["matched"] and failed["final"] == reports["success"]["final"]
        # Application outcomes below are synthetic model tests, not native measurements.
        altered = json.loads(json.dumps(traces["success"]))
        scope = {"resource": "application", "operation": "read"}
        credential = {
            "issuer": altered["context"]["issuer"],
            "subject": altered["context"]["consumer"],
            "audience": altered["context"]["producer"],
            "scopes": [scope],
            "expiresAt": 100,
            "integrity": True,
        }
        altered["events"][18:18] = [
            {"type": "install", "credential": credential, "authorized": None},
            {"type": "request", "scope": scope, "accepted": True, "authorized": True},
        ]
        altered["events"].append(
            {"type": "request", "scope": scope, "accepted": False, "authorized": False}
        )
        path.write_text(json.dumps(altered))
        modeled = json.loads(invoke("eap", path, "--json"))
        assert modeled["findings"][19]["expectedAccepted"]
        assert not modeled["findings"][-1]["expectedAccepted"]
        assert not modeled["final"]["credentialPresent"]
        altered["events"].append({"type": "authenticate", "success": True, "authorized": True})
        path.write_text(json.dumps(altered))
        invoke("eap", path, code=2)
        malformed = json.loads(json.dumps(traces["success"]))
        malformed["events"][1]["raw"] = "0"
        path.write_text(json.dumps(malformed))
        invoke("eap", path, code=2)
        malformed = json.loads(json.dumps(traces["success"]))
        malformed["events"].extend(
            [
                {"type": "advance", "now": 5, "authorized": None},
                {"type": "advance", "now": 4, "authorized": None},
            ]
        )
        path.write_text(json.dumps(malformed))
        invoke("eap", path, code=2)


def admission_checks():
    from build_admission_examples import build

    directory = ROOT / "examples/admission"
    provenance = json.loads((directory / "capture-provenance.json").read_text())
    assert set(provenance["artifactSHA256"]) == {
        path.relative_to(directory).as_posix()
        for path in (directory / "native").rglob("*")
        if path.is_file()
    }
    for relative, digest in provenance["artifactSHA256"].items():
        assert hashlib.sha256((directory / relative).read_bytes()).hexdigest() == digest, relative
    for group in ["verifierSHA256", "projectionSHA256"]:
        for relative, digest in provenance[group].items():
            assert hashlib.sha256((ROOT / relative).read_bytes()).hexdigest() == digest, relative
    evidence, authentication, bundle = build()
    for name, value in [
        ("checked-evidence", evidence),
        ("authentication", authentication),
        ("bundle", bundle),
    ]:
        assert value == json.loads((directory / f"{name}.json").read_text())
    assert evidence["eapFrameCount"] == 18 and evidence["frameCount"] == 7
    assert [stage["delivered"] for stage in evidence["stages"]] == [False, False, True, False]
    assert [snapshot["after"] for snapshot in bundle["snapshots"]] == [1, 18, 19, 21]
    trace = directory / "authentication.json"
    intent = directory / "requirements.json"
    report = json.loads(invoke("session-firewall", directory / "bundle.json", "--json"))
    assert report["compliant"] and report["authenticationMatches"]
    assert report["scope"] == "eap-derived-native-firewall-snapshots" and report["assumptions"]
    assert [snapshot["authorized"] for snapshot in report["snapshots"]] == [
        False,
        True,
        True,
        False,
    ]
    assert [snapshot["credentialPresent"] for snapshot in report["snapshots"]] == [
        False,
        False,
        True,
        False,
    ]
    assert all(snapshot["equivalent"] for snapshot in report["snapshots"])
    assert report["partitionCells"] == report["compilationCells"] + report["comparisonCells"]
    assert json.loads(invoke("eap", trace, "--json"))["compliant"]
    for after, policy in [(0, "deny"), (1, "deny"), (18, "deny"), (19, "permit"), (21, "deny")]:
        generated = json.loads(invoke("compile-session", trace, intent, "--after", after))
        assert generated == json.loads((directory / f"{policy}.json").read_text())
    assert json.loads(invoke("compile-session", trace, intent)) == json.loads(
        (directory / "deny.json").read_text()
    )
    invoke("compile-session", trace, intent, "--after", "22", code=2)
    invoke("compile-session", trace, intent, "--after", "invalid", code=2)
    invoke("compile-session", trace, intent, "--budget", "0", code=2)
    invoke("session-firewall", directory / "bundle.json", "--budget", report["partitionCells"])
    invoke(
        "session-firewall",
        directory / "bundle.json",
        "--budget",
        report["partitionCells"] - 1,
        code=2,
    )
    with tempfile.TemporaryDirectory(prefix="netlib-admission-") as folder:
        path = Path(folder) / "altered.json"
        altered = json.loads(json.dumps(bundle))
        firewall = altered["snapshots"][-1]["firewall"]["nftables"]
        chain = next(row["chain"] for row in firewall if "chain" in row)
        firewall.append(
            {
                "rule": {
                    "family": "ip",
                    "table": chain["table"],
                    "chain": chain["name"],
                    "handle": 999,
                    "expr": [
                        {
                            "match": {
                                "op": "in",
                                "left": {"ct": {"key": "state"}},
                                "right": ["established"],
                            }
                        },
                        {"accept": None},
                    ],
                }
            }
        )
        path.write_text(json.dumps(altered))
        failed = json.loads(invoke("session-firewall", path, "--json", code=1))
        assert failed["snapshots"][-1]["unexpectedPermit"]["state"] == "established"
        assert failed["snapshots"][-1]["missingPermit"] is None
        altered = json.loads(json.dumps(bundle))
        altered["snapshots"][2]["firewall"]["nftables"] = [
            row
            for row in altered["snapshots"][2]["firewall"]["nftables"]
            if row.get("rule", {}).get("comment") != "REPLY"
        ]
        path.write_text(json.dumps(altered))
        failed = json.loads(invoke("session-firewall", path, "--json", code=1))
        assert failed["snapshots"][2]["missingPermit"] is not None
        assert failed["snapshots"][2]["unexpectedPermit"] is None
        altered = json.loads(json.dumps(authentication))
        altered["events"][17]["subject"] = "anonymous@campus.example.test"
        path.write_text(json.dumps(altered))
        invoke("compile-session", path, intent, "--after", "19", code=1)
        altered = json.loads(json.dumps(bundle))
        altered["snapshots"][0]["after"] = 22
        path.write_text(json.dumps(altered))
        invoke("session-firewall", path, code=2)
        altered = json.loads(json.dumps(bundle))
        for row in altered["snapshots"][0]["firewall"]["nftables"]:
            if "chain" in row:
                row["chain"]["prio"] = 1
        path.write_text(json.dumps(altered))
        invoke("session-firewall", path, code=2)
        conflicting = json.loads(intent.read_text())
        conflict = json.loads(json.dumps(conflicting["requirements"][0]))
        conflict.update(id="OTHER_SCOPE", scope={"resource": "management", "operation": "use"})
        conflicting["requirements"].append(conflict)
        path.write_text(json.dumps(conflicting))
        invoke("compile-session", trace, path, "--after", "19", code=1)


def wire_checks():
    from build_wire_examples import build

    directory = ROOT / "examples/wire"
    provenance = json.loads((directory / "capture-provenance.json").read_text())
    assert set(provenance["artifactSHA256"]) == {
        path.relative_to(directory).as_posix()
        for path in (directory / "native").rglob("*")
        if path.is_file()
    }
    for relative, digest in provenance["artifactSHA256"].items():
        assert hashlib.sha256((directory / relative).read_bytes()).hexdigest() == digest, relative
    for group in ["verifierSHA256", "projectionSHA256"]:
        for relative, digest in provenance[group].items():
            assert hashlib.sha256((ROOT / relative).read_bytes()).hexdigest() == digest, relative
    evidence, authentication, bundle, frame = build()
    for name, value in [
        ("checked-evidence", evidence),
        ("authentication", authentication),
        ("bundle", bundle),
        ("frame", frame),
    ]:
        assert value == json.loads((directory / f"{name}.json").read_text())
    assert evidence["frameCount"] == 7 and evidence["probeFrameCount"] == 9
    assert evidence["eapFrameCount"] == 18
    assert [probe["forwarded"] for probe in evidence["probes"]] == [True, True, True, True, False]
    assert [probe["received"] for probe in evidence["probes"]] == [True, True, False, False, False]
    assert json.loads(invoke("session-firewall", directory / "bundle.json", "--json"))["compliant"]
    assert json.loads(
        invoke(
            "compile-session",
            directory / "authentication.json",
            directory / "requirements.json",
            "--after",
            "19",
        )
    ) == json.loads((directory / "permit.json").read_text())
    fixture = json.loads(invoke("wire", directory / "frame.json", "--json"))
    assert fixture["valid"] and fixture["scope"] == "untagged-ipv4-udp-wire-profile-1"
    assert fixture["sources"] and fixture["assumptions"] and fixture["udpChecksumVerified"]
    with tempfile.TemporaryDirectory(prefix="netlib-wire-") as folder:
        path = Path(folder) / "frame.json"
        for decoded in evidence["frames"]:
            path.write_text(json.dumps({"schema": 1, "raw": decoded["raw"]}))
            result = json.loads(invoke("wire", path, "--json"))
            assert result["header"] == decoded["header"] and result["ttl"] == decoded["ttl"]
            assert result["identification"] == decoded["ipId"]
            assert result["payloadHex"] == decoded["payloadHex"]
            assert result["ethernetPaddingHex"] == decoded["paddingHex"]
            assert result["ipv4Checksum"] == decoded["ipChecksum"]["value"]
            assert result["udpChecksum"] == decoded["udpChecksum"]["value"]
            assert result["udpChecksumVerified"]
        for probe in evidence["probes"]:
            for decoded in [probe["ingress"], *([probe["egress"]] if probe["egress"] else [])]:
                path.write_text(json.dumps({"schema": 1, "raw": decoded["raw"]}))
                output = invoke("wire", path, "--json", code=0 if decoded["valid"] else 2)
                if decoded["valid"]:
                    result = json.loads(output)
                    assert result["udpChecksumVerified"] == (
                        decoded["udpChecksum"]["status"] == "valid"
                    )
                    assert result["header"] == decoded["header"]
        # Earlier bytes retain their original offload boundary and observations.
        for line in (ROOT / "examples/admission/native/data-frames.jsonl").read_text().splitlines():
            path.write_text(json.dumps({"schema": 1, "raw": json.loads(line)["hex"]}))
            invoke("wire", path, "--json", code=2)
        path.write_text(json.dumps({**frame, "header": fixture["header"]}))
        invoke("wire", path, code=2)
        for text in [
            '{"schema":1,"schema":1,"raw":""}',
            '{"schema":2,"raw":""}',
            '{"schema":1,"raw":"0"}',
            '{"schema":1,"raw":"gg"}',
        ]:
            path.write_text(text)
            invoke("wire", path, code=2)


def wire_forwarding_checks():
    from build_wire_nat_examples import build

    directory = ROOT / "examples/wire-nat"
    provenance = json.loads((directory / "capture-provenance.json").read_text())
    assert set(provenance["artifactSHA256"]) == {
        path.relative_to(directory).as_posix()
        for path in (directory / "native").rglob("*")
        if path.is_file()
    }
    for relative, digest in provenance["artifactSHA256"].items():
        assert hashlib.sha256((directory / relative).read_bytes()).hexdigest() == digest, relative
    for group in ["verifierSHA256", "projectionSHA256"]:
        for relative, digest in provenance[group].items():
            assert hashlib.sha256((ROOT / relative).read_bytes()).hexdigest() == digest, relative
    evidence, authentication, session, replay = build()
    for name, value in [
        ("checked-evidence", evidence),
        ("authentication", authentication),
        ("session", session),
        ("replay", replay),
    ]:
        assert value == json.loads((directory / f"{name}.json").read_text())
    assert evidence["frameCount"] == 17 and evidence["udpFrameCount"] == 14
    assert evidence["icmpFrameCount"] == 3 and len(evidence["packetSamples"]) == 10
    assert replay["initial"] is not None
    report = json.loads(invoke("wire-forward", directory / "replay.json", "--json"))
    assert report["compliant"] and report["eventCount"] == 11
    assert report["scope"] == "byte-derived-ipv4-udp-tracked-forwarding" and report["assumptions"]
    assert all(
        finding["matched"] and finding["stateObserved"] and finding["stateMatched"]
        for finding in report["findings"]
    )
    assert [
        finding["expected"]["disposition"] if finding["expected"] else "erased"
        for finding in report["findings"]
    ] == [
        "forwardDrop",
        "forwardDrop",
        "forwarded",
        "ttlExpired",
        "forwarded",
        "forwardDrop",
        "erased",
        "ttlExpired",
        "ttlExpired",
        "forwarded",
        "forwarded",
    ]
    assert not report["findings"][2]["expectedState"][0]["seenReply"]
    assert report["findings"][3]["expectedState"][0]["seenReply"]
    assert report["findings"][6]["expectedState"] == []
    assert report["findings"][7]["expectedState"] == report["findings"][8]["expectedState"] == []
    assert report["findings"][9]["expected"]["output"]["ttl"] == 1
    assert report["findings"][10]["expected"]["output"]["udpChecksum"] == 0
    request = report["findings"][2]["expected"]["output"]["header"]
    assert request == {
        "source": "203.0.113.1",
        "destination": "198.51.100.2",
        "protocol": 17,
        "sourcePort": 40000,
        "destinationPort": 9000,
    }
    reply = report["findings"][4]["expected"]["output"]["header"]
    assert reply == {
        "source": "203.0.113.2",
        "destination": "192.0.2.2",
        "protocol": 17,
        "sourcePort": 8080,
        "destinationPort": 41000,
    }
    assert json.loads(invoke("session-firewall", directory / "session.json", "--json"))["compliant"]
    assert json.loads(
        invoke(
            "compile-session",
            directory / "authentication.json",
            directory / "requirements.json",
            "--after",
            "19",
        )
    ) == json.loads((directory / "permit.json").read_text())
    with tempfile.TemporaryDirectory(prefix="netlib-wire-forward-") as folder:
        path = Path(folder) / "changed.json"
        altered = json.loads(json.dumps(replay))
        altered["events"][2]["observed"]["output"] = None
        path.write_text(json.dumps(altered))
        failed = json.loads(invoke("wire-forward", path, "--json", code=1))
        assert not failed["findings"][2]["matched"] and failed["final"] == report["final"]
        altered = json.loads(json.dumps(replay))
        altered["events"][3]["state"] = altered["events"][2]["state"]
        path.write_text(json.dumps(altered))
        failed = json.loads(invoke("wire-forward", path, "--json", code=1))
        assert not failed["findings"][3]["stateMatched"]
        assert failed["findings"][4]["matched"] and failed["final"] == report["final"]
        altered = json.loads(json.dumps(replay))
        altered["events"][9]["observed"]["disposition"] = "forwardDrop"
        path.write_text(json.dumps(altered))
        failed = json.loads(invoke("wire-forward", path, "--json", code=1))
        assert not failed["findings"][9]["matched"]
        for field, value in [
            ("zone", 65536),
            ("config", "missing"),
            ("raw", "0"),
            ("packet", request),
        ]:
            altered = json.loads(json.dumps(replay))
            altered["events"][0][field] = value
            path.write_text(json.dumps(altered))
            invoke("wire-forward", path, code=2)
        altered = json.loads(json.dumps(replay))
        altered["events"] = []
        path.write_text(json.dumps(altered))
        invoke("wire-forward", path, code=2)


def mtu_boundary_checks(replay):
    import copy
    import ipaddress

    from check_wire_capture import folded_sum

    source = replay["events"][2]
    ingress = bytes.fromhex(source["raw"])
    output_link = bytes.fromhex(source["observed"]["output"][0])[:14]

    def ip_frame(header, payload, link):
        header = bytearray(header)
        header[2:4] = (20 + len(payload)).to_bytes(2, "big")
        header[10:12] = bytes(2)
        header[10:12] = (65535 - folded_sum(header)).to_bytes(2, "big")
        return (link + header + payload).hex()

    def udp_payload(header, ports, data):
        transport = ports + (8 + len(data)).to_bytes(2, "big") + bytes(2) + data
        pseudo = header[12:20] + bytes([0, 17]) + len(transport).to_bytes(2, "big")
        checksum = 65535 - folded_sum(pseudo + transport)
        return transport[:6] + (checksum or 65535).to_bytes(2, "big") + data

    with tempfile.TemporaryDirectory(prefix="netlib-mtu-boundary-") as folder:
        path = Path(folder) / "synthetic.json"
        for mtu in [68, 69, 75, 76, 77, 599, 600, 601, 607, 608, 1500]:
            limit, aligned = mtu - 20, (mtu - 20) // 8 * 8
            lengths = {limit, limit + 1, 2 * aligned, 2 * aligned + 1, 2 * aligned + limit}
            lengths.update(aligned + last for last in range(aligned + 1, limit + 1))
            lengths.update(2 * aligned + last for last in range(aligned + 1, limit + 1))
            for length in sorted(lengths):
                data = bytes((index * 37 + 9) % 256 for index in range(length - 8))
                input_header = bytearray(ingress[14:34])
                input_payload = udp_payload(input_header, ingress[34:38], data)
                incoming = ip_frame(input_header, input_payload, ingress[:14])
                translated = bytearray(input_header)
                translated[8] -= 1
                translated[12:16] = ipaddress.IPv4Address("203.0.113.1").packed
                translated[16:20] = ipaddress.IPv4Address("198.51.100.2").packed
                ports = (40000).to_bytes(2, "big") + (9000).to_bytes(2, "big")
                remaining = udp_payload(translated, ports, data)
                output, offset = [], 0
                while remaining:
                    more = len(remaining) > limit
                    size = aligned if more else len(remaining)
                    part = translated.copy()
                    part[6:8] = ((8192 if more else 0) | (offset // 8)).to_bytes(2, "big")
                    output.append(ip_frame(part, remaining[:size], output_link))
                    remaining, offset = remaining[size:], offset + size
                altered = copy.deepcopy(replay)
                altered["events"] = [copy.deepcopy(source)]
                event = altered["events"][0]
                event["raw"], event["state"] = incoming, None
                event["observed"]["output"], event["observed"]["mtu"] = output, mtu
                for binding in altered["mtus"]:
                    if binding["nextHop"] == "service":
                        binding["mtu"] = mtu
                path.write_text(json.dumps(altered))
                report = json.loads(invoke("wire-mtu", path, "--json"))
                assert report["compliant"], (mtu, length)
                computed = report["findings"][0]["expected"]["output"]["fragments"]
                assert len(computed) == len(output), (mtu, length)


def mtu_checks():
    from build_mtu_examples import build

    directory = ROOT / "examples/mtu"
    provenance = json.loads((directory / "capture-provenance.json").read_text())
    assert set(provenance["artifactSHA256"]) == {
        path.relative_to(directory).as_posix()
        for path in (directory / "native").rglob("*")
        if path.is_file()
    }
    for relative, digest in provenance["artifactSHA256"].items():
        assert hashlib.sha256((directory / relative).read_bytes()).hexdigest() == digest, relative
    for group in ["verifierSHA256", "projectionSHA256"]:
        for relative, digest in provenance[group].items():
            assert hashlib.sha256((ROOT / relative).read_bytes()).hexdigest() == digest, relative
    evidence, authentication, session, replay = build()
    for name, value in [
        ("checked-evidence", evidence),
        ("authentication", authentication),
        ("session", session),
        ("replay", replay),
    ]:
        assert value == json.loads((directory / f"{name}.json").read_text())
    assert evidence["frameCount"] == 27 and evidence["udpFragmentCount"] == 23
    assert evidence["icmpFrameCount"] == 4 and len(evidence["packetSamples"]) == 12
    assert replay["initial"] is not None
    report = json.loads(invoke("wire-mtu", directory / "replay.json", "--json"))
    assert report["compliant"] and report["eventCount"] == 13
    assert report["scope"] == "mtu-aware-ipv4-udp-tracked-forwarding" and report["assumptions"]
    assert all(
        finding["matched"] and finding["stateObserved"] and finding["stateMatched"]
        for finding in report["findings"]
    )
    assert [
        finding["expected"]["disposition"] if finding["expected"] else "erased"
        for finding in report["findings"]
    ] == [
        "forwardDrop",
        "forwardDrop",
        "forwarded",
        "ttlExpired",
        "forwarded",
        "forwardDrop",
        "mtuExceeded",
        "erased",
        "mtuExceeded",
        "ttlExpired",
        "forwarded",
        "forwarded",
        "forwarded",
    ]
    findings = report["findings"]
    assert not findings[2]["expectedState"][0]["seenReply"]
    assert findings[3]["expectedState"][0]["seenReply"]
    assert findings[6]["expectedState"] == findings[5]["expectedState"]
    assert (
        findings[7]["expectedState"]
        == findings[8]["expectedState"]
        == findings[9]["expectedState"]
        == []
    )
    assert findings[3]["expected"]["mtu"] is None and findings[9]["expected"]["mtu"] is None
    assert findings[6]["expected"]["mtu"] == findings[8]["expected"]["mtu"] == 600
    for event, finding in zip(replay["events"], findings, strict=True):
        if event["type"] == "erase":
            continue
        expected = finding["expected"]["output"]
        native = event["observed"]["output"]
        if not native:
            assert expected is None
            continue
        assert len(native) == len(expected["rawIPv4"])
        for raw, computed in zip(native, expected["rawIPv4"], strict=True):
            data = bytes.fromhex(raw)
            size = int.from_bytes(data[16:18], "big")
            assert data[14 : 14 + size].hex() == computed
        sample = next(
            sample for sample in evidence["packetSamples"] if sample["raw"] == event["raw"]
        )
        family = sample["outputFamily"]
        assert family["derivedByReassembly"] and expected["header"] == family["header"]
        assert expected["payloadHex"] == family["payloadHex"] and expected["ttl"] == family["ttl"]
        assert expected["udpChecksum"] == family["udpChecksum"]["value"]
        assert all(
            part["wireLength"] <= finding["expected"]["mtu"] for part in expected["fragments"]
        )
    for index in [2, 11, 12]:
        output = findings[index]["expected"]["output"]
        assert [part["wireLength"] for part in output["fragments"]] == [596, 596, 76]
        assert [part["offsetBytes"] for part in output["fragments"]] == [0, 576, 1152]
        assert [part["moreFragments"] for part in output["fragments"]] == [True, True, False]
        assert len(bytes.fromhex(output["payloadHex"])) == 1200
    assert findings[10]["expected"]["output"]["fragments"][0]["wireLength"] == 600
    assert findings[10]["expected"]["output"]["fragments"][0]["dontFragment"]
    assert findings[12]["expected"]["output"]["udpChecksum"] == 0
    mtu_boundary_checks(replay)
    assert json.loads(invoke("session-firewall", directory / "session.json", "--json"))["compliant"]
    assert json.loads(
        invoke(
            "compile-session",
            directory / "authentication.json",
            directory / "requirements.json",
            "--after",
            "19",
        )
    ) == json.loads((directory / "permit.json").read_text())
    with tempfile.TemporaryDirectory(prefix="netlib-wire-mtu-") as folder:
        path = Path(folder) / "changed.json"
        altered = json.loads(json.dumps(replay))
        altered["events"][2]["observed"]["output"].reverse()
        path.write_text(json.dumps(altered))
        assert json.loads(invoke("wire-mtu", path, "--json"))["compliant"]
        altered["events"][2]["observed"]["output"] = []
        path.write_text(json.dumps(altered))
        mismatch = json.loads(invoke("wire-mtu", path, "--json", code=1))
        assert not mismatch["findings"][2]["matched"]
        assert all(finding["matched"] for finding in mismatch["findings"][3:])
        assert mismatch["final"] == report["final"]
        altered = json.loads(json.dumps(replay))
        altered["events"][8]["observed"]["disposition"] = "forwarded"
        path.write_text(json.dumps(altered))
        assert not json.loads(invoke("wire-mtu", path, "--json", code=1))["findings"][8]["matched"]
        for output in [
            replay["events"][2]["observed"]["output"][:-1],
            replay["events"][2]["observed"]["output"] * 2,
            None,
        ]:
            altered = json.loads(json.dumps(replay))
            altered["events"][2]["observed"]["output"] = output
            path.write_text(json.dumps(altered))
            invoke("wire-mtu", path, code=2)
        for mtus in [[], replay["mtus"] * 2, [{"nextHop": "service", "mtu": 67}]]:
            altered = json.loads(json.dumps(replay))
            altered["mtus"] = mtus
            path.write_text(json.dumps(altered))
            invoke("wire-mtu", path, code=2)


def main():
    traffic_checks()
    linux_checks()
    stateful_checks()
    conntrack_checks()
    lifecycle_checks()
    revocation_checks()
    buffered_checks()
    eap_checks()
    admission_checks()
    wire_checks()
    wire_forwarding_checks()
    mtu_checks()
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
        f"Profile CLI checks passed for {count} fixtures and extended packet, stateful, conntrack, lifecycle, revocation, buffered, and EAP commands."
    )


if __name__ == "__main__":
    main()
