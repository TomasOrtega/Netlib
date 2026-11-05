"""Compare received-error CLI replay with native evidence and an independent PMTU oracle."""

import copy
import hashlib
import ipaddress
import json
import tempfile
from pathlib import Path

from build_received_icmp_examples import build
from check_cli import ROOT, invoke
from check_wire_capture import folded_sum

DIRECTORY = ROOT / "examples/received-icmp"
PROJECTION_SOURCES = {
    "scripts/build_received_icmp_examples.py",
    "scripts/test_build_received_icmp_examples.py",
    "scripts/check_received_icmp_examples.py",
    "scripts/build_admission_examples.py",
    "docs/RECEIVED_ICMP.md",
    "docs/research/RECEIVED_ICMP_PMTU.md",
}


def provenance_checks():
    provenance = json.loads((DIRECTORY / "capture-provenance.json").read_text())
    assert set(provenance["artifactSHA256"]) == {
        path.relative_to(DIRECTORY).as_posix()
        for path in (DIRECTORY / "native").rglob("*")
        if path.is_file()
    }
    for relative, digest in provenance["artifactSHA256"].items():
        assert hashlib.sha256((DIRECTORY / relative).read_bytes()).hexdigest() == digest, relative
    required = PROJECTION_SOURCES | {
        path.relative_to(ROOT).as_posix()
        for path in DIRECTORY.iterdir()
        if path.is_file() and path.name != "capture-provenance.json"
    }
    assert set(provenance["projectionSHA256"]) == required
    for group in ["producerSourceSHA256", "verifierSHA256", "projectionSHA256"]:
        assert provenance[group], group
        for relative, digest in provenance[group].items():
            assert hashlib.sha256((ROOT / relative).read_bytes()).hexdigest() == digest, relative


def _ip(raw):
    frame = bytes.fromhex(raw)
    assert frame[12:14] == bytes.fromhex("0800")
    packet = frame[14:]
    assert packet[0] == 69
    return packet[: int.from_bytes(packet[2:4], "big")]


def _header(packet):
    return {
        "source": str(ipaddress.IPv4Address(packet[12:16])),
        "destination": str(ipaddress.IPv4Address(packet[16:20])),
        "protocol": packet[9],
        "sourcePort": int.from_bytes(packet[20:22], "big"),
        "destinationPort": int.from_bytes(packet[22:24], "big"),
    }


def _feedback(raw):
    packet = _ip(raw)
    control = packet[20:]
    kind = {"type": control[0], "code": control[1]}
    if control[:2] == bytes([3, 4]):
        kind["mtu"] = int.from_bytes(control[6:8], "big")
    return kind, _header(control[8:]), str(ipaddress.IPv4Address(packet[12:16]))


def _reference(bundle):
    route, policy, socket = bundle["route"], bundle["policy"], bundle["socket"]
    cache, rows = None, []
    previous = 0
    for event in bundle["events"]:
        now = event["at"]
        assert previous <= now
        previous = now
        active = cache if cache and now < cache["expires"] else None
        old = active["mtu"] if active else route["mtu"]
        expected = {"type": event["type"], "mtu": old}
        if event["type"] == "receive":
            kind, quoted, reporter = _feedback(event["raw"])
            accepted = kind["type"] == 3 and kind["code"] == 4 and quoted == socket
            disposition = None
            if accepted:
                advertised = kind["mtu"]
                if route["locked"] or active and active["locked"]:
                    disposition, cache = "locked", active
                elif old < advertised:
                    disposition, cache = "increase", active
                else:
                    below = advertised < policy["minimum"]
                    target = min(old, policy["minimum"]) if below else advertised
                    if (
                        active
                        and target == active["mtu"]
                        and not below
                        and now < active["expires"] - policy["lifetime"] // 2
                    ):
                        disposition, cache = "unchanged", active
                    else:
                        disposition = "updated"
                        cache = {
                            "mtu": target,
                            "locked": below,
                            "expires": now + policy["lifetime"],
                        }
            expected.update(
                kind=kind,
                quoted=quoted,
                reporter=reporter,
                acceptedFeedback=accepted,
                disposition=disposition,
            )
        elif event["type"] == "send":
            length = event["payloadLength"] + 28
            expected["decision"] = (
                "invalidLength"
                if length > 65535
                else "messageSize"
                if event["df"] and length > old
                else "accepted"
            )
        active = cache if cache and now < cache["expires"] else None
        expected["mtu"] = active["mtu"] if active else route["mtu"]
        state = {"currentMTU": expected["mtu"], "lastTime": now, "exception": active}
        assert 68 <= state["currentMTU"] <= route["mtu"]
        rows.append((expected, state))
    return rows


def _reference_report(bundle, report):
    rows = _reference(bundle)
    assert len(rows) == report["eventCount"] == len(report["findings"])
    for index, ((expected, state), finding) in enumerate(
        zip(rows, report["findings"], strict=True)
    ):
        assert finding["source"] == f"/events/{index}"
        assert finding["expected"] == expected, (index, finding["expected"], expected)
        assert finding["expectedState"] == state, (index, finding["expectedState"], state)
    assert report["final"] == rows[-1][1]


def native_checks():
    evidence, authentication, session, replay, host = build()
    for name, value in [
        ("checked-evidence", evidence),
        ("authentication", authentication),
        ("session", session),
        ("replay", replay),
        ("host", host),
    ]:
        assert value == json.loads((DIRECTORY / f"{name}.json").read_text()), name
    assert (evidence["frameCount"], evidence["icmpFrameCount"], evidence["eapFrameCount"]) == (
        60,
        22,
        18,
    )
    assert len(evidence["packetSamples"]) == 15
    gateway = json.loads(invoke("wire-related", DIRECTORY / "replay.json", "--json"))
    assert gateway["compliant"] and gateway["eventCount"] == 16
    assert gateway["scope"] == "received-icmp-tracked-forwarding" and gateway["assumptions"]
    assert sum(row["stateObserved"] for row in gateway["findings"]) == 13
    assert [i for i, row in enumerate(gateway["findings"]) if not row["stateObserved"]] == [
        2,
        6,
        8,
    ]
    previous = []
    dispositions = []
    for index, (event, finding) in enumerate(
        zip(replay["events"], gateway["findings"], strict=True)
    ):
        assert finding["source"] == f"/events/{index}"
        assert finding["matched"] and finding["stateMatched"]
        assert finding["stateObserved"] == (event["state"] is not None)
        expected = finding["expected"]
        if event["type"] != "erase":
            observed = [_ip(raw).hex() for raw in event["observed"]["forwarded"]]
            assert observed == (expected["output"] or {}).get("rawIPv4", [])
            assert event["observed"]["icmpOutput"] == []
        if event["type"] == "icmp":
            assert finding["expectedState"] == previous
            dispositions.append(expected["disposition"])
            if expected["output"]:
                incoming, outgoing = _ip(event["raw"]), bytes.fromhex(observed[0])
                assert outgoing[8] + 1 == incoming[8]
                assert outgoing[36] == incoming[36] == 63
                assert _header(outgoing[28:]) == host["socket"]
                assert outgoing[56:] == incoming[56:]
        previous = finding["expectedState"]
    assert dispositions == [
        "forwarded",
        "unrelated",
        "unrelated",
        "ttlExpired",
        "forwarded",
        "forwarded",
        "forwarded",
    ]
    assert gateway["final"] == previous and len(previous) == 1
    assert previous[0]["seenReply"] and previous[0]["sourceNAT"] and previous[0]["destinationNAT"]
    sender = json.loads(invoke("host-pmtu", DIRECTORY / "host.json", "--json"))
    assert sender["compliant"] and sender["eventCount"] == 19
    assert sender["scope"] == "udp-host-pmtu-feedback" and sender["assumptions"]
    assert all(finding["matched"] for finding in sender["findings"])
    _reference_report(host, sender)
    assert [
        row["expected"]["decision"]
        for row in sender["findings"]
        if row["expected"]["type"] == "send"
    ] == [
        "accepted",
        "messageSize",
        "accepted",
    ]
    assert sender["final"]["currentMTU"] == 576
    delivered = {
        raw
        for event in replay["events"]
        if event["type"] == "icmp"
        for raw in event["observed"]["forwarded"]
    }
    assert all(event["raw"] in delivered for event in host["events"] if event["type"] == "receive")
    assert json.loads(invoke("session-firewall", DIRECTORY / "session.json", "--json"))["compliant"]
    return replay, host, gateway, sender


def _ipv4(source, destination, protocol, payload, *, ttl=63):
    header = bytearray(20)
    header[0], header[8], header[9] = 69, ttl, protocol
    header[2:4] = (20 + len(payload)).to_bytes(2, "big")
    header[4:6] = bytes.fromhex("1234")
    header[12:16], header[16:20] = (
        ipaddress.IPv4Address(address).packed for address in [source, destination]
    )
    header[10:12] = (65535 - folded_sum(header)).to_bytes(2, "big")
    return bytes(header) + payload


def error_frame(socket, advertised, *, reporter="198.51.100.99", kind=(3, 4), quote_size=9):
    payload = bytes(range(13))
    udp = (
        socket["sourcePort"].to_bytes(2, "big")
        + socket["destinationPort"].to_bytes(2, "big")
        + (8 + len(payload)).to_bytes(2, "big")
        + bytes(2)
        + payload
    )
    quote = _ipv4(socket["source"], socket["destination"], socket["protocol"], udp)
    control = bytes(kind) + bytes(4) + (advertised if kind == (3, 4) else 0).to_bytes(2, "big")
    control += quote[: 20 + quote_size]
    control = control[:2] + (65535 - folded_sum(control)).to_bytes(2, "big") + control[4:]
    return (
        bytes.fromhex("0200000000010200000000020800")
        + _ipv4(reporter, socket["source"], 1, control, ttl=64)
    ).hex()


def boundary_checks(host):
    count, observations = 0, 0
    with tempfile.TemporaryDirectory(prefix="netlib-pmtu-reference-") as temporary:
        path = Path(temporary) / "synthetic.json"
        for physical in [68, 552, 576, 600, 4096, 65535]:
            for minimum in [68, 552, 600]:
                for lifetime in [1, 5, 600]:
                    bundle = copy.deepcopy(host)
                    bundle["route"], bundle["policy"] = (
                        {"mtu": physical, "locked": False},
                        {"minimum": minimum, "lifetime": lifetime},
                    )
                    events = [{"type": "query", "at": 0, "mtu": 0}]

                    def receive(at, advertised, **options):
                        events.append(
                            {
                                "type": "receive",
                                "at": at,
                                "raw": error_frame(host["socket"], advertised, **options),
                                "mtu": 0,
                            }
                        )

                    target = min(physical, max(minimum, 600))
                    threshold = 10 + (lifetime + 1) // 2
                    receive(10, target)
                    receive(10, 65535)
                    receive(threshold - 1, target)
                    receive(threshold, target, reporter="203.0.113.99")
                    for payload in sorted(
                        {0, 39, 40, 41, max(0, target - 29), target - 28, target - 27, 65507, 65508}
                    ):
                        for df in [False, True]:
                            events.append(
                                {
                                    "type": "send",
                                    "at": threshold,
                                    "payloadLength": payload,
                                    "df": df,
                                    "errorsDrained": True,
                                    "observed": "accepted",
                                }
                            )
                    receive(threshold, 0)
                    receive(threshold, 68)
                    deadline = threshold + lifetime
                    events.append({"type": "query", "at": deadline, "mtu": 0})
                    receive(deadline, minimum - 1)
                    events.append({"type": "query", "at": deadline + lifetime, "mtu": 0})
                    bundle["events"] = events
                    for event, (expected, _) in zip(events, _reference(bundle), strict=True):
                        if event["type"] == "send":
                            event["observed"] = expected["decision"]
                        else:
                            event["mtu"] = expected["mtu"]
                    path.write_text(json.dumps(bundle))
                    report = json.loads(invoke("host-pmtu", path, "--json"))
                    assert report["compliant"] and all(row["matched"] for row in report["findings"])
                    _reference_report(bundle, report)
                    count += 1
                    observations += len(events)
        bundle = copy.deepcopy(host)
        bundle["events"] = []
        for field, changed in [
            ("source", "192.0.2.3"),
            ("destination", "203.0.113.3"),
            ("protocol", 6),
            ("sourcePort", 41001),
            ("destinationPort", 8081),
        ]:
            quote = {**host["socket"], field: changed}
            bundle["events"].append(
                {"type": "receive", "at": 1, "raw": error_frame(quote, 576), "mtu": 4096}
            )
        bundle["events"].append(
            {
                "type": "receive",
                "at": 1,
                "raw": error_frame(host["socket"], 0, kind=(11, 0)),
                "mtu": 4096,
            }
        )
        bundle["events"].append(
            {"type": "receive", "at": 1, "raw": error_frame(host["socket"], 600), "mtu": 600}
        )
        bundle["events"].append(
            {
                "type": "receive",
                "at": 2,
                "raw": error_frame(host["socket"], 576, reporter="0.0.0.0"),
                "mtu": 576,
            }
        )
        for locked in [False, True]:
            bundle["route"]["locked"] = locked
            for event, (expected, _) in zip(bundle["events"], _reference(bundle), strict=True):
                event["mtu"] = expected["mtu"]
            path.write_text(json.dumps(bundle))
            report = json.loads(invoke("host-pmtu", path, "--json"))
            assert report["compliant"]
            assert all(not row["expected"]["acceptedFeedback"] for row in report["findings"][:6])
            _reference_report(bundle, report)
            count += 1
            observations += len(bundle["events"])
    assert count == 56
    return count, observations


def mutation_checks(replay, host, gateway, sender):
    count = 0
    with tempfile.TemporaryDirectory(prefix="netlib-received-mutations-") as temporary:
        path = Path(temporary) / "changed.json"

        def check(command, value, code):
            nonlocal count
            path.write_text(json.dumps(value))
            result = invoke(command, path, "--json", code=code)
            count += 1
            return json.loads(result) if code != 2 else None

        changed = copy.deepcopy(replay)
        changed["events"][7]["observed"]["forwarded"] = []
        failed = check("wire-related", changed, 1)
        assert [i for i, row in enumerate(failed["findings"]) if not row["matched"]] == [7]
        assert failed["final"] == gateway["final"]
        changed = copy.deepcopy(replay)
        changed["events"][7]["zone"] = 1
        failed = check("wire-related", changed, 1)
        assert failed["findings"][7]["expected"]["disposition"] == "unrelated"
        assert failed["final"] == gateway["final"]
        changed = copy.deepcopy(replay)
        changed["events"][7]["state"]["entries"] = []
        failed = check("wire-related", changed, 1)
        assert not failed["findings"][7]["stateMatched"]
        assert all(row["matched"] for row in failed["findings"][8:])
        assert failed["final"] == gateway["final"]
        changed = copy.deepcopy(replay)
        rules = changed["configs"][-1]["forward"]["nftables"]
        control = next(
            row["rule"] for row in rules if row.get("rule", {}).get("comment") == "RECEIVED_CONTROL"
        )
        control["expr"][-1] = {"drop": None}
        failed = check("wire-related", changed, 1)
        assert all(
            failed["findings"][i]["expected"]["disposition"] == "forwardDrop"
            for i in [7, 13, 14, 15]
        )
        assert failed["final"] == gateway["final"]
        for index, field, value in [(3, "mtu", 1200), (5, "observed", "accepted")]:
            changed = copy.deepcopy(host)
            changed["events"][index][field] = value
            failed = check("host-pmtu", changed, 1)
            assert [i for i, row in enumerate(failed["findings"]) if not row["matched"]] == [index]
            assert failed["final"] == sender["final"]
        invalid = [
            ("route", "mtu", 67),
            ("route", "mtu", 65536),
            ("policy", "minimum", 67),
            ("policy", "minimum", 65536),
            ("policy", "lifetime", 0),
            ("socket", "protocol", 6),
            ("socket", "sourcePort", 65536),
        ]
        for section, field, value in invalid:
            changed = copy.deepcopy(host)
            changed[section][field] = value
            check("host-pmtu", changed, 2)
        for field, value in [("schema", 2), ("events", []), ("unknown", True)]:
            check("host-pmtu", {**host, field: value}, 2)
        changed = copy.deepcopy(host)
        changed["events"][1]["at"] = changed["events"][0]["at"] - 1
        check("host-pmtu", changed, 2)
        changed = copy.deepcopy(host)
        changed["events"][1]["errorsDrained"] = False
        check("host-pmtu", changed, 2)
        for command, base, index in [("wire-related", replay, 7), ("host-pmtu", host, 2)]:
            changed = copy.deepcopy(base)
            raw = bytearray.fromhex(changed["events"][index]["raw"])
            raw[36] ^= 1
            changed["events"][index]["raw"] = raw.hex()
            check(command, changed, 2)
        changed = copy.deepcopy(host)
        changed["events"] = [
            {
                "type": "receive",
                "at": 0,
                "raw": error_frame(host["socket"], 600, quote_size=7),
                "mtu": None,
            }
        ]
        check("host-pmtu", changed, 2)
        changed = copy.deepcopy(replay)
        changed["events"][7]["observed"]["icmpOutput"] = changed["events"][7]["observed"][
            "forwarded"
        ]
        check("wire-related", changed, 2)
    return count


def check():
    provenance_checks()
    replay, host, gateway, sender = native_checks()
    traces, observations = boundary_checks(host)
    mutations = mutation_checks(replay, host, gateway, sender)
    print(
        f"Received ICMP CLI checks passed: 16 gateway events (13 table observations), "
        f"19 host events, {traces} independent PMTU traces ({observations} observations), "
        f"and {mutations} negative CLI mutations."
    )


if __name__ == "__main__":
    check()
