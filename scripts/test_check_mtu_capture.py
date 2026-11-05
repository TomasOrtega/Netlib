"""Fragment families, MTU boundaries, and native evidence contradiction tests."""

import copy
import json
import shutil
import tempfile
import unittest
from pathlib import Path

import check_mtu_capture as check

CAPTURE = Path(__file__).resolve().parents[1] / "examples/mtu/native"


def write(path, value):
    path.write_text(json.dumps(value, indent=2) + "\n")


def repair_header(frame):
    frame[24:26] = bytes(2)
    frame[24:26] = (65535 - check.wire.folded_sum(frame[14:34])).to_bytes(2, "big")


class CaptureTests(unittest.TestCase):
    def reject(self, change, pattern="."):
        with tempfile.TemporaryDirectory() as temporary:
            directory = Path(temporary) / "native"
            shutil.copytree(CAPTURE, directory)
            change(directory)
            with self.assertRaisesRegex(check.EvidenceError, pattern):
                check.check_capture(directory)

    def change_json(self, filename, change, pattern="."):
        def mutate(directory):
            path = directory / filename
            document = json.loads(path.read_text())
            change(document)
            write(path, document)

        self.reject(mutate, pattern)

    def change_frames(self, change, pattern="."):
        def mutate(directory):
            path = directory / "frames.jsonl"
            rows = [json.loads(line) for line in path.read_text().splitlines()]
            change(rows)
            path.write_text("".join(json.dumps(row) + "\n" for row in rows))

        self.reject(mutate, pattern)

    def main_family(self):
        report = check.check_capture(CAPTURE)
        return report["packetSamples"][2]["outputFamily"]

    def mutate_main_output(self, change, pattern):
        originals = {row["raw"] for row in self.main_family()["fragments"]}

        def mutate(rows):
            for row in rows:
                if row["hex"] in originals:
                    frame = bytearray.fromhex(row["hex"])
                    change(frame)
                    repair_header(frame)
                    row["hex"] = frame.hex()

        self.change_frames(mutate, pattern)

    def change_export(self, selector, change, pattern):
        def mutate(directory):
            observations = json.loads((directory / "observations.json").read_text())
            export = selector(observations)
            document = json.loads((directory / export["file"]).read_text())
            original = copy.deepcopy(export["command"])
            change(document)
            text = json.dumps(document) + "\n"
            (directory / export["file"]).write_text(text)
            export["command"]["stdout"] = text
            commands = json.loads((directory / "commands.json").read_text())
            for row in commands:
                if row == original:
                    row["stdout"] = text
            write(directory / "commands.json", commands)
            write(directory / "observations.json", observations)

        self.reject(mutate, pattern)

    def test_native_capture(self):
        report = check.check_capture(CAPTURE)
        self.assertEqual(
            (report["frameCount"], report["udpFragmentCount"], report["icmpFrameCount"]),
            (27, 23, 4),
        )
        self.assertEqual(len(report["packetSamples"]), 12)
        family = report["packetSamples"][2]["outputFamily"]
        self.assertEqual([row["ipLength"] for row in family["fragments"]], [596, 596, 76])
        self.assertEqual([row["offsetBytes"] for row in family["fragments"]], [0, 576, 1152])
        self.assertEqual([row["moreFragments"] for row in family["fragments"]], [True, True, False])
        self.assertEqual(len(bytes.fromhex(family["payloadHex"])), 1200)

    def test_fragment_capture_precedes_post_step_snapshot(self):
        observations = json.loads((CAPTURE / "observations.json").read_text())
        boundary = observations["stages"][2]["lowTTLReply"]["before"]["command"]["endNs"]

        def change(rows):
            identifier = next(
                int.from_bytes(bytes.fromhex(row["hex"])[18:20], "big")
                for row in rows
                if row["interface"] == "auth0"
                and bytes.fromhex(row["hex"])[42:].startswith(b"mtu:credential-permitted-request|")
            )
            for row in rows:
                data = bytes.fromhex(row["hex"])
                if (
                    row["interface"] == "service0"
                    and row["packetType"] == 4
                    and data[23] == 17
                    and int.from_bytes(data[18:20], "big") == identifier
                ):
                    boundary_offset = len(
                        [other for other in rows[: rows.index(row)] if other["timeNs"] > boundary]
                    )
                    row["timeNs"] = boundary + boundary_offset + 1

        self.change_frames(change, "snapshot")

    def test_sysctl_stdout_matches_saved_settings(self):
        def change(commands):
            row = next(
                row
                for row in commands
                if row["command"][:5] == ["ip", "netns", "exec", "auth", "sysctl"]
            )
            row["stdout"] = row["stdout"].replace(
                "net.ipv4.ip_forward = 1", "net.ipv4.ip_forward = 0"
            )

        self.change_json("commands.json", change, "settings.*stdout|sysctl")

    def test_unordered_fragment_reassembly(self):
        family = self.main_family()
        self.assertEqual(check.reassemble_fragments(list(reversed(family["fragments"]))), family)

    def test_fragment_family_requires_complete_unique_coverage(self):
        fragments = self.main_family()["fragments"]
        cases = {
            "missing-first": fragments[1:],
            "missing-last": fragments[:-1],
            "duplicate": [*fragments, fragments[1]],
        }
        for name, rows in cases.items():
            with self.subTest(name=name), self.assertRaises(check.EvidenceError):
                check.reassemble_fragments(rows)

    def test_checksum_valid_fragment_overlap_rejected(self):
        def change(frame):
            flags = int.from_bytes(frame[20:22], "big")
            if flags & 8191 == 72:
                frame[20:22] = ((flags & 0xE000) | 71).to_bytes(2, "big")

        self.mutate_main_output(change, "overlap|gap")

    def test_checksum_valid_fragment_gap_rejected(self):
        def change(frame):
            flags = int.from_bytes(frame[20:22], "big")
            if flags & 8191 == 72:
                frame[20:22] = ((flags & 0xE000) | 73).to_bytes(2, "big")

        self.mutate_main_output(change, "overlap|gap")

    def test_noninitial_payload_checked_by_reassembled_udp_checksum(self):
        def change(frame):
            if int.from_bytes(frame[20:22], "big") & 8191 == 72:
                frame[34] ^= 1

        self.mutate_main_output(change, "UDP pseudoheader checksum")

    def test_consistent_fragment_tos_still_must_match_input(self):
        self.mutate_main_output(lambda frame: frame.__setitem__(15, frame[15] ^ 1), "metadata")

    def test_df_cannot_accompany_fragment_offsets(self):
        def change(frame):
            frame[20] |= 64

        self.mutate_main_output(change, "DF cannot accompany")

    def test_gateway_input_fragments_are_outside_profile(self):
        def change(rows):
            frame = bytearray.fromhex(rows[0]["hex"])
            frame[20:22] = (1).to_bytes(2, "big")
            repair_header(frame)
            rows[0]["hex"] = frame.hex()

        self.change_frames(change, "ingress fragmentation")

    def test_exact_mtu_and_omitted_checksum_are_observed(self):
        report = check.check_capture(CAPTURE)
        exact = report["packetSamples"][9]
        self.assertTrue(exact["ingress"]["dontFragment"])
        self.assertEqual(exact["ingress"]["ipLength"], 600)
        self.assertEqual(len(exact["observed"]["output"]), 1)
        omitted = report["packetSamples"][-1]
        self.assertEqual(omitted["ingress"]["udpChecksum"]["status"], "omitted")
        self.assertEqual(omitted["outputFamily"]["udpChecksum"]["status"], "omitted")
        self.assertEqual(len(omitted["observed"]["output"]), 3)

    def test_ttl_precedes_mtu_error(self):
        report = check.check_capture(CAPTURE)
        cached, fresh, expired = report["packetSamples"][6:9]
        for sample in (cached, fresh):
            self.assertEqual(sample["observed"]["disposition"], "mtuExceeded")
            self.assertEqual(sample["icmpObservations"][0]["nextHopMTU"], 600)
            self.assertEqual(sample["observed"]["output"], [])
        self.assertEqual(expired["observed"]["disposition"], "ttlExpired")
        self.assertEqual(expired["icmpObservations"][0]["icmpType"], 11)

    def test_valid_icmp_checksum_does_not_hide_wrong_mtu(self):
        def change(rows):
            row = next(row for row in rows if bytes.fromhex(row["hex"])[34:36] == b"\x03\x04")
            frame = bytearray.fromhex(row["hex"])
            frame[40:42] = (601).to_bytes(2, "big")
            frame[36:38] = bytes(2)
            frame[36:38] = (65535 - check.wire.folded_sum(frame[34:])).to_bytes(2, "big")
            row["hex"] = frame.hex()

        self.change_frames(change, "next-hop MTU")

    def test_fresh_mtu_drop_does_not_confirm(self):
        def mutate(directory):
            shutil.copyfile(
                directory / "exact-mtu-df-after-conntrack.json",
                directory / "fresh-df-oversize-after-conntrack.json",
            )

        self.reject(mutate, "unexpectedly confirmed")

    def test_per_event_mtu_export_checked_even_with_consistent_stdout(self):
        def change(document):
            next(row for row in document if row["ifname"] == "service0")["mtu"] = 601

        self.change_export(
            lambda observations: observations["stages"][2]["requestLinks"]["auth"],
            change,
            "Per-event link MTU",
        )

    def test_full_ruleset_rejects_unaccounted_hook(self):
        self.change_export(
            lambda observations: observations["stages"][2]["exports"]["ruleset"],
            lambda document: document["nftables"].append(
                {"table": {"family": "ip", "name": "hidden"}}
            ),
            "unaccounted hook",
        )

    def test_native_socket_pmtu_mode_is_checked(self):
        self.change_json(
            "observations.json",
            lambda observations: observations["stages"][2]["sent"]["result"].update(mtuDiscover=2),
            "PMTU mode",
        )

    def test_complete_family_still_requires_measured_mtu_split(self):
        family = self.main_family()
        original = {row["raw"]: index for index, row in enumerate(family["fragments"])}
        payload = bytes.fromhex(family["ipPayloadHex"])
        offsets, sizes = [0, 568, 1144], [568, 576, 64]

        def change(rows):
            for row in rows:
                if row["hex"] not in original:
                    continue
                index = original[row["hex"]]
                offset, size = offsets[index], sizes[index]
                frame = bytearray.fromhex(row["hex"])[:34] + payload[offset : offset + size]
                frame[16:18] = (20 + size).to_bytes(2, "big")
                frame[20:22] = (offset // 8 | (8192 if index < 2 else 0)).to_bytes(2, "big")
                repair_header(frame)
                row["hex"] = frame.hex()

        self.change_frames(change, "MTU split boundary")

    def test_icmp_quote_matches_full_original_prefix(self):
        def change(rows):
            row = next(row for row in rows if bytes.fromhex(row["hex"])[34:36] == b"\x03\x04")
            frame = bytearray.fromhex(row["hex"])
            frame[70] ^= 1
            frame[36:38] = bytes(2)
            frame[36:38] = (65535 - check.wire.folded_sum(frame[34:])).to_bytes(2, "big")
            row["hex"] = frame.hex()

        self.change_frames(change, "ICMP quote")

    def test_cached_mtu_drop_preserves_replied_entry(self):
        def change(document):
            entry = document["entries"][0]
            before, after = (
                entry["id"].to_bytes(4, "big").hex(),
                (entry["id"] ^ 1).to_bytes(4, "big").hex(),
            )
            original = entry["raw"]
            self.assertEqual(original.count(before), 1)
            entry["id"] ^= 1
            entry["raw"] = original.replace(before, after)
            document["messages"] = [
                entry["raw"] if message == original else message for message in document["messages"]
            ]

        self.change_json(
            "cached-df-oversize-after-conntrack.json", change, "preserve the replied binding"
        )

    def test_mtu_readback_must_precede_corresponding_send(self):
        def change(directory):
            observations = json.loads((directory / "observations.json").read_text())
            stage = observations["stages"][2]
            command = stage["requestLinks"]["auth"]["command"]
            original = copy.deepcopy(command)
            command.update(startNs=stage["sent"]["endNs"] + 1, endNs=stage["sent"]["endNs"] + 2)
            commands = json.loads((directory / "commands.json").read_text())
            for row in commands:
                if row == original:
                    row.update(command)
            commands.sort(key=lambda row: row["startNs"])
            write(directory / "commands.json", commands)
            write(directory / "observations.json", observations)

        self.reject(change, "MTU export stdout or observation interval")


if __name__ == "__main__":
    unittest.main()
