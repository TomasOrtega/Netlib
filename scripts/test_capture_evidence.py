"""Exercise the common evidence interface against actual capture profiles."""

import json
import shutil
import tempfile
import unittest
from pathlib import Path

from capture_evidence import CaptureEvidence, EvidenceError, complete_admission

ROOT = Path(__file__).resolve().parents[1]
REPLICATION = ROOT / "examples/replication/native"
SAFE_HANDOFF = ROOT / "examples/safe-handoff/native"


class AdmissionTests(unittest.TestCase):
    RAW = (
        "45000031c8fb00004011b3bbc0000202cb007102a0281f90001daeed"
        "7265706c69636174696f6e3a65737461626c697368"
    )

    def test_complete_early_bytes_are_preserved(self):
        value = complete_admission(self.RAW)
        self.assertEqual(value["raw"], self.RAW)
        self.assertEqual(value["mode"], "complete")
        self.assertEqual(value["udpChecksum"]["status"], "valid")

    def test_partial_seed_or_omitted_checksum_is_not_complete(self):
        raw = bytes.fromhex(self.RAW)
        pseudo = raw[12:20] + bytes((0, 17)) + raw[24:26]
        total = sum(int.from_bytes(pseudo[index : index + 2], "big") for index in range(0, 12, 2))
        while total > 65535:
            total = (total & 65535) + (total >> 16)
        for checksum in (bytes(2), total.to_bytes(2, "big")):
            with self.subTest(checksum=checksum.hex()), self.assertRaises(EvidenceError):
                complete_admission((raw[:26] + checksum + raw[28:]).hex())

    def test_later_valid_bytes_do_not_justify_an_invalid_early_copy(self):
        raw = bytearray.fromhex(self.RAW)
        raw[-1] ^= 1
        with self.assertRaises(EvidenceError):
            complete_admission(raw.hex())


class ReplicationAdapterTests(unittest.TestCase):
    def consume(self, evidence):
        manifest = json.loads((REPLICATION / "capture.json").read_text())
        evidence.read_boundary("initial")
        packets = []
        for event in manifest["events"]:
            evidence.read_boundary(event["id"] + ":before")
            if event["type"] == "packet":
                packets.append(evidence.bind_packet(event["id"]))
            evidence.read_boundary(event["id"] + ":after")
        evidence.read_boundary("final")
        return packets, evidence.finish()

    def test_actual_legacy_capture_uses_the_common_interface(self):
        evidence = CaptureEvidence.open(REPLICATION, "replication")
        packets, result = self.consume(evidence)
        self.assertEqual(result["packetCount"], 6)
        self.assertEqual(result["snapshotCount"], 56)
        self.assertEqual(
            [row["disposition"] for row in packets],
            ["forwarded", "routeDrop", "forwardDrop", "forwarded", "forwarded", "forwarded"],
        )
        self.assertTrue(all(row["admission"]["mode"] == "complete" for row in packets))
        self.assertTrue(all(row["admission"]["point"] == "gateway-ingress" for row in packets))
        self.assertEqual(packets[0]["admission"]["raw"], packets[0]["inputHex"])
        self.assertTrue(packets[-1]["outputEthernetHex"])

    def test_boundary_window_and_reference_are_checked(self):
        evidence = CaptureEvidence.open(REPLICATION, "replication")
        with self.assertRaisesRegex(EvidenceError, "Unknown boundary"):
            evidence.read_boundary("fictional:before")
        with self.assertRaisesRegex(EvidenceError, "window"):
            evidence.read_boundary("initial", (1, 2))

    def test_finish_requires_all_boundary_and_packet_bindings(self):
        evidence = CaptureEvidence.open(REPLICATION, "replication")
        evidence.read_boundary("initial")
        with self.assertRaisesRegex(EvidenceError, "Unconsumed"):
            evidence.finish()

    def test_duplicate_binding_is_not_a_second_packet_observation(self):
        evidence = CaptureEvidence.open(REPLICATION, "replication")
        evidence.bind_packet("establish")
        with self.assertRaisesRegex(EvidenceError, "reused"):
            evidence.bind_packet("establish")
        evidence.read_boundary("initial")
        with self.assertRaisesRegex(EvidenceError, "reused"):
            evidence.read_boundary("initial")

    def test_unknown_named_profile_is_rejected(self):
        with self.assertRaisesRegex(EvidenceError, "Unknown capture profile"):
            CaptureEvidence.open(REPLICATION, "caller-defined-rules")

    def test_compatibility_adapter_keeps_the_authoritative_gate(self):
        with tempfile.TemporaryDirectory() as temporary:
            directory = Path(temporary) / "native"
            shutil.copytree(REPLICATION, directory)
            manifest = json.loads((directory / "capture.json").read_text())
            manifest["endpoints"][0]["command"] = ["true"]
            (directory / "capture.json").write_text(json.dumps(manifest))
            with self.assertRaisesRegex(EvidenceError, "endpoint"):
                CaptureEvidence.open(directory, "replication")


class SafeHandoffAdapterTests(unittest.TestCase):
    def consume(self, directory):
        evidence = CaptureEvidence.open(directory, "safe-handoff")
        manifest = json.loads((directory / "capture.json").read_text())
        evidence.read_boundary("initial")
        for event in manifest["events"]:
            for side in ("before", "after"):
                evidence.read_boundary(event["id"] + ":" + side)
        evidence.read_boundary("final")
        packets = [evidence.bind_packet(ticket) for ticket in ("establish", 0, 1, 2, 3, 4, 5)]
        return packets, evidence.finish()

    def test_actual_split_admission_and_service_uses_the_same_interface(self):
        packets, report = self.consume(SAFE_HANDOFF)
        self.assertEqual(
            (
                report["packetCount"],
                report["snapshotCount"],
                report["frameCount"],
                report["nflogCount"],
            ),
            (7, 84, 26, 27),
        )
        self.assertTrue(
            all(packet["admission"]["point"] == "endpoint-postrouting" for packet in packets)
        )
        self.assertEqual(packets[1]["admitEvent"], "admit-primary")
        self.assertEqual(packets[1]["serveEvent"], "serve-primary")
        self.assertEqual(packets[1]["gateway"], "a")
        self.assertEqual(packets[4]["disposition"], "forwardDrop")
        self.assertEqual(packets[1]["admission"]["raw"], packets[1]["inputHex"])


if __name__ == "__main__":
    unittest.main()
