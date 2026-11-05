"""Check ICMP replay against native bytes and independent synthetic error construction."""

import copy
import hashlib
import json
import tempfile
from pathlib import Path

from build_icmp_examples import build
from check_cli import ROOT, invoke
from check_wire_capture import folded_sum


def boundaries(replay):
    source = replay["events"][8]
    ingress = bytes.fromhex(source["raw"])
    link = bytes.fromhex(source["observed"]["icmpOutput"][0])[:14]

    def ipv4(header, payload, ethernet):
        header = bytearray(header)
        header[2:4] = (20 + len(payload)).to_bytes(2, "big")
        header[10:12] = bytes(2)
        header[10:12] = (65535 - folded_sum(header)).to_bytes(2, "big")
        return ethernet + header + payload

    with tempfile.TemporaryDirectory(prefix="netlib-icmp-boundaries-") as folder:
        path = Path(folder) / "synthetic.json"
        count = 0
        for size in [28, 29, 63, 64, 547, 548, 549, 576, 577, 1228]:
            for reverse_mtu in [68, 69, 75, 76, 575, 576, 600, 4096]:
                for omitted in [False, True]:
                    header = bytearray(ingress[14:34])
                    header[1], header[8] = (size + reverse_mtu) % 256, 1
                    header[6:8] = (16384 if size % 2 == 0 else 0).to_bytes(2, "big")
                    data = bytes((index * 37 + 9) % 256 for index in range(size - 28))
                    udp = ingress[34:38] + (8 + len(data)).to_bytes(2, "big") + bytes(2) + data
                    if not omitted:
                        pseudo = header[12:20] + bytes([0, 17]) + len(udp).to_bytes(2, "big")
                        checksum = (65535 - folded_sum(pseudo + udp)) or 65535
                        udp = udp[:6] + checksum.to_bytes(2, "big") + data
                    incoming = ipv4(header, udp, ingress[:14])
                    quote_size = min(size, min(reverse_mtu, 576) - 28)
                    quote = incoming[14 : 14 + quote_size]
                    icmp = bytes([11, 0]) + bytes(6) + quote
                    icmp = icmp[:2] + (65535 - folded_sum(icmp)).to_bytes(2, "big") + icmp[4:]
                    outer = bytearray(20)
                    outer[0], outer[1] = 69, (header[1] & 30) | 192
                    outer[4:6], outer[8], outer[9] = bytes([0x42, 0x42]), 64, 1
                    outer[12:16], outer[16:20] = header[16:20], header[12:16]
                    output = ipv4(outer, icmp, link)
                    altered = copy.deepcopy(replay)
                    event = copy.deepcopy(source)
                    event["raw"], event["state"] = incoming.hex(), None
                    event["observed"].update(
                        disposition="ttlExpired",
                        mtu=None,
                        afterSource=None,
                        icmpOutput=[output.hex()],
                    )
                    altered["events"] = [event]
                    for binding in altered["mtus"]:
                        if binding["nextHop"] == "peer":
                            binding["mtu"] = reverse_mtu
                    path.write_text(json.dumps(altered))
                    report = json.loads(invoke("wire-icmp", path, "--json"))
                    expected = report["findings"][0]["expected"]["icmp"]["output"]
                    assert report["compliant"] and expected["rawIPv4"] == output[14:].hex()
                    assert expected["quoteLength"] == quote_size
                    assert expected["returnMTU"] == reverse_mtu
                    assert report["final"] == []
                    count += 1
        assert count == 160


def check():
    directory = ROOT / "examples/icmp"
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
    assert evidence["frameCount"] == 43 and evidence["icmpFrameCount"] == 12
    assert len(evidence["packetSamples"]) == 20
    report = json.loads(invoke("wire-icmp", directory / "replay.json", "--json"))
    assert report["compliant"] and report["eventCount"] == 21
    assert report["scope"] == "icmp-aware-ipv4-udp-tracked-forwarding" and report["assumptions"]
    outputs, complete = 0, 0
    for event, finding in zip(replay["events"], report["findings"], strict=True):
        assert finding["matched"] and finding["stateMatched"] and finding["stateObserved"]
        if event["type"] == "erase":
            assert finding["expected"] is None
            continue
        expected = finding["expected"]["icmp"]
        raw = event["observed"]["icmpOutput"]
        if not raw:
            assert expected["output"] is None and expected["disposition"] == "notNeeded"
            assert expected["classification"] is None
            continue
        data = bytes.fromhex(raw[0])
        ip_size = int.from_bytes(data[16:18], "big")
        output = expected["output"]
        assert output["rawIPv4"] == data[14 : 14 + ip_size].hex()
        assert expected["classification"] == "related" and expected["disposition"] == "sent"
        assert output["quoteLength"] + 28 == ip_size <= min(output["returnMTU"], 576)
        incoming = bytes.fromhex(event["raw"])
        original_size = int.from_bytes(incoming[16:18], "big")
        assert output["declaredLength"] == original_size
        assert data[42 : 14 + ip_size] == incoming[14 : 14 + output["quoteLength"]]
        assert output["tos"] == (incoming[15] & 30) | 192
        assert data[26:30] == incoming[30:34] and data[30:34] == incoming[26:30]
        observed = finding["observed"]["icmpOutput"][0]
        assert observed["quotedUDPComplete"] == (output["quoteLength"] == original_size)
        assert observed["quotedUDPChecksumVerified"] == (
            output["quoteLength"] == original_size and incoming[40:42] != bytes(2)
        )
        outputs += 1
        complete += observed["quotedUDPComplete"]
    assert outputs == 12 and complete == 5
    assert json.loads(invoke("session-firewall", directory / "session.json", "--json"))["compliant"]
    boundaries(replay)
    with tempfile.TemporaryDirectory(prefix="netlib-icmp-mismatch-") as folder:
        path = Path(folder) / "changed.json"
        altered = copy.deepcopy(replay)
        altered["events"][3]["observed"]["icmpOutput"] = []
        path.write_text(json.dumps(altered))
        failed = json.loads(invoke("wire-icmp", path, "--json", code=1))
        assert not failed["findings"][3]["matched"]
        assert all(finding["matched"] for finding in failed["findings"][4:])
        assert failed["final"] == report["final"]
        for field, value in [("rateLimit", 1), ("quoteLimit", 547), ("outerDontFragment", True)]:
            altered = copy.deepcopy(replay)
            altered["icmpProfile"][field] = value
            path.write_text(json.dumps(altered))
            invoke("wire-icmp", path, code=2)
    print("ICMP CLI checks passed: 21 native events and 160 independent synthetic boundary cases.")


if __name__ == "__main__":
    check()
