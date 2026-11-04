"""Valid wire bytes, checksum omissions, and native malformed-packet regressions."""

import copy
import json
import shutil
import tempfile
import unittest
from pathlib import Path

import check_wire_capture as check

ROOT = Path(__file__).resolve().parents[1]
CAPTURE = ROOT / "examples/wire/native"


class CaptureTests(unittest.TestCase):
    def reject(self, filename, change, pattern=".", lines=False):
        with tempfile.TemporaryDirectory() as temporary:
            directory = Path(temporary) / "native"
            shutil.copytree(CAPTURE, directory)
            path = directory / filename
            document = (
                [json.loads(line) for line in path.read_text().splitlines()]
                if lines
                else json.loads(path.read_text())
            )
            change(document)
            path.write_text(
                "".join(json.dumps(row) + "\n" for row in document)
                if lines
                else json.dumps(document)
            )
            with self.assertRaisesRegex(check.EvidenceError, pattern):
                check.check_capture(directory)

    def frame(self):
        return bytearray.fromhex(
            json.loads((CAPTURE / "data-frames.jsonl").read_text().splitlines()[0])["hex"]
        )

    def test_native_capture(self):
        evidence = check.check_capture(CAPTURE)
        self.assertEqual(
            (evidence["frameCount"], evidence["eapFrameCount"], evidence["probeFrameCount"]),
            (7, 18, 9),
        )
        self.assertEqual(
            [row["received"] for row in evidence["probes"]], [True, True, False, False, False]
        )
        self.assertEqual(
            [row["forwarded"] for row in evidence["probes"]], [True, True, True, True, False]
        )
        self.assertTrue(
            all(
                row["udpChecksum"]["status"] == "valid" and row["udpChecksum"]["value"]
                for row in evidence["frames"]
            )
        )

    def test_historical_partial_bytes_are_not_valid_udp_wire(self):
        rows = [
            json.loads(line)
            for line in (ROOT / "examples/admission/native/data-frames.jsonl")
            .read_text()
            .splitlines()
        ]
        self.assertEqual(len(rows), 7)
        for row in rows:
            decoded = check.inspect_frame(row["hex"])
            self.assertTrue(decoded["ipChecksum"]["valid"])
            self.assertEqual(decoded["reason"], "udp-checksum")

    def test_word_sum_odd_padding_and_carries(self):
        self.assertEqual(check.folded_sum(bytes.fromhex("0001f203f4f5f6f7")), 0xDDF2)
        self.assertEqual(check.folded_sum(bytes.fromhex("000102")), 0x0201)
        self.assertEqual(check.folded_sum(bytes.fromhex("ffffffff")), 65535)

    def test_udp_checksum_corruption_rejected(self):
        def change(rows):
            frame = bytearray.fromhex(rows[0]["hex"])
            frame[40] ^= 1
            rows[0]["hex"] = frame.hex()

        self.reject("data-frames.jsonl", change, "udp-checksum", lines=True)

    def test_pseudoheader_source_and_destination_are_checked(self):
        for offset in (29, 33):
            frame = self.frame()
            frame[offset] ^= 1
            frame[24:26] = bytes(2)
            frame[24:26] = (65535 - check.folded_sum(frame[14:34])).to_bytes(2, "big")
            decoded = check.inspect_frame(frame.hex())
            self.assertTrue(decoded["ipChecksum"]["valid"])
            self.assertEqual(decoded["reason"], "udp-checksum")

    def test_zero_udp_checksum_is_explicit_omission(self):
        frame = self.frame()
        frame[40:42] = bytes(2)
        decoded = check.decode_frame(frame.hex())
        self.assertEqual(decoded["udpChecksum"], {"value": 0, "status": "omitted"})

        def change(rows):
            rows[0]["hex"] = frame.hex()

        self.reject("data-frames.jsonl", change, "nonzero", lines=True)

    def test_udp_declared_length_must_match_selected_profile(self):
        for length in (7, 8, 65535):
            frame = self.frame()
            frame[38:40] = length.to_bytes(2, "big")
            self.assertEqual(check.inspect_frame(frame.hex())["reason"], "udp-length")

    def test_ipv4_checksum_and_length_are_checked(self):
        frame = self.frame()
        frame[24] ^= 1
        self.assertEqual(check.inspect_frame(frame.hex())["reason"], "ipv4-checksum")
        frame[16:18] = b"\xff\xff"
        with self.assertRaisesRegex(check.EvidenceError, "IPv4 wire length"):
            check.inspect_frame(frame.hex())

    def test_reserved_ipv4_flag_rejected_with_valid_checksum(self):
        frame = self.frame()
        frame[20] |= 0x80
        frame[24:26] = bytes(2)
        frame[24:26] = (65535 - check.folded_sum(frame[14:34])).to_bytes(2, "big")
        with self.assertRaisesRegex(check.EvidenceError, "wire profile"):
            check.decode_frame(frame.hex())

    def test_link_padding_is_outside_the_datagram(self):
        raw = self.frame().hex()
        decoded = check.decode_frame(raw + "aabbcc")
        self.assertEqual(decoded["paddingHex"], "aabbcc")
        self.assertEqual(decoded["payloadHex"], check.decode_frame(raw)["payloadHex"])

    def test_projected_raw_hex_rejects_whitespace(self):
        def change(rows):
            raw = rows[0]["hex"]
            rows[0]["hex"] = " ".join(raw[index : index + 2] for index in range(0, len(raw), 2))

        self.reject("data-frames.jsonl", change, "hexadecimal", lines=True)

    def test_offload_readback_and_interface_binding_rejected(self):
        self.reject(
            "offloads.json",
            lambda rows: rows[0]["after"].update(txChecksum=1),
            "Offload readback|remains enabled",
        )
        self.reject("offloads.json", lambda rows: rows.pop(), "offload readback")

    def test_false_malformed_udp_socket_delivery_rejected(self):
        def change(document):
            result = copy.deepcopy(document["probes"][0]["receiver"]["result"])
            result["payload"] = "wire-probe:udp-bad-checksum"
            document["probes"][2]["receiver"]["result"] = result

        self.reject("probe-observations.json", change, "UDP socket outcome")

    def test_bad_udp_forwarding_and_bad_ip_drop_are_independent(self):
        self.reject(
            "probe-frames.jsonl", lambda rows: rows.pop(5), "ingress or egress count", lines=True
        )

        def extra_egress(rows):
            row = copy.deepcopy(rows[-1])
            row.update(interface="service0", packetType=4, timeNs=row["timeNs"] + 1000)
            rows.append(row)

        self.reject("probe-frames.jsonl", extra_egress, "ingress or egress count", lines=True)

    def test_raw_sender_input_and_stdout_must_agree(self):
        def change(document):
            frame = bytearray.fromhex(document["raw"])
            frame[-1] ^= 1
            document["raw"] = frame.hex()

        self.reject("probe-raw-valid-input.json", change, "Raw sender bytes")

    def test_active_probe_policy_stdout_join_rejected(self):
        def change(commands):
            row = next(row for row in commands if row["command"][-2:] == ["list", "ruleset"])
            document = json.loads(row["stdout"])
            document["nftables"].append({"table": {"family": "ip", "name": "hidden"}})
            row["stdout"] = json.dumps(document)

        self.reject("probe-commands.json", change, "command history")


if __name__ == "__main__":
    unittest.main()
