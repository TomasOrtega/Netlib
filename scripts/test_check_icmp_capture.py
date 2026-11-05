"""Native ICMP checks and explicitly synthetic evidence contradiction cases."""

import copy
import json
import shutil
import tempfile
import unittest
from pathlib import Path

import check_icmp_capture as check

CAPTURE = Path(__file__).resolve().parents[1] / "examples/icmp/native"


def write(path, value):
    path.write_text(json.dumps(value, indent=2) + "\n")


def repair(frame):
    size = int.from_bytes(frame[16:18], "big")
    frame[24:26] = bytes(2)
    frame[24:26] = (65535 - check.wire.folded_sum(frame[14:34])).to_bytes(2, "big")
    frame[36:38] = bytes(2)
    frame[36:38] = (65535 - check.wire.folded_sum(frame[34 : 14 + size])).to_bytes(2, "big")


class CaptureTests(unittest.TestCase):
    def reject(self, change, pattern="."):
        with tempfile.TemporaryDirectory() as temporary:
            directory = Path(temporary) / "native"
            shutil.copytree(CAPTURE, directory)
            change(directory)
            with self.assertRaisesRegex(check.EvidenceError, pattern):
                check.check_capture(directory)

    def change_frames(self, change, pattern="."):
        def mutate(directory):
            path = directory / "frames.jsonl"
            rows = [json.loads(line) for line in path.read_text().splitlines()]
            change(rows)
            path.write_text("".join(json.dumps(row) + "\n" for row in rows))

        self.reject(mutate, pattern)

    def change_error(self, change, pattern=".", selector=lambda row, data: True):
        def mutate(rows):
            row = next(
                row
                for row in rows
                if bytes.fromhex(row["hex"])[23] == 1 and selector(row, bytes.fromhex(row["hex"]))
            )
            frame = bytearray.fromhex(row["hex"])
            change(frame)
            repair(frame)
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
            (43, 31, 12),
        )
        self.assertEqual(len(report["packetSamples"]), 20)
        self.assertEqual(len(report["icmpOutputTraces"]), 12)
        self.assertEqual(
            sum(len(row["observed"]["icmpOutput"]) for row in report["packetSamples"]), 12
        )
        samples = {row["label"]: row for row in report["packetSamples"]}
        for name, length, _, omitted, _ in check.EXTRA:
            error = samples[name]["icmpObservations"][0]
            self.assertEqual(error["quoteLength"], min(length, 548))
            self.assertEqual(error["quoteComplete"], length <= 548)
            self.assertEqual(
                error["quotedUdpChecksum"]["status"],
                "omitted" if omitted else "valid" if length <= 548 else "partial",
            )
        reply = samples["quote-reply-odd"]["icmpObservations"][0]
        self.assertEqual(
            (reply["sourceAddress"], reply["destinationAddress"]), ("203.0.113.1", "198.51.100.2")
        )

    def test_reused_trace_identifiers_are_distinct_episodes(self):
        import re

        with tempfile.TemporaryDirectory() as temporary:
            path = Path(temporary) / "trace.txt"
            path.write_text(
                re.sub(
                    r"trace id [0-9a-f]{8}",
                    "trace id 00000001",
                    (CAPTURE / "trace.txt").read_text(),
                )
            )
            udp, errors = check.parse_traces(path)
        self.assertEqual((len(udp), len(errors)), (20, 12))
        self.assertEqual({row["id"] for row in udp + errors}, {"00000001"})

    def test_after_destination_udp_checksum_is_independent(self):
        def mutate(directory):
            path = directory / "trace.txt"
            lines = path.read_text().splitlines()
            index = next(
                index
                for index, line in enumerate(lines)
                if "netlib_trace afterDestination packet:" in line and "ip id 64769 " in line
            )
            lines[index] = lines[index].replace("udp checksum 47456", "udp checksum 1")
            path.write_text("\n".join(lines) + "\n")

        self.reject(mutate, "whole UDP.*checksum")

    def test_one_output_trace_cannot_explain_two_errors(self):
        def mutate(rows):
            errors = [row for row in rows if bytes.fromhex(row["hex"])[34:36] == bytes((3, 4))]
            frame = bytearray.fromhex(errors[1]["hex"])
            frame[18:20] = bytes.fromhex(errors[0]["hex"])[18:20]
            repair(frame)
            errors[1]["hex"] = frame.hex()

        self.change_frames(mutate, "output hook packet metadata|ordered.*trace")

    def test_repeated_outer_ids_use_distinct_ordered_episodes(self):
        with tempfile.TemporaryDirectory() as temporary:
            directory = Path(temporary) / "native"
            shutil.copytree(CAPTURE, directory)
            path = directory / "frames.jsonl"
            rows = [json.loads(line) for line in path.read_text().splitlines()]
            errors = [row for row in rows if bytes.fromhex(row["hex"])[34:36] == bytes((3, 4))]
            first_id = int.from_bytes(bytes.fromhex(errors[0]["hex"])[18:20], "big")
            frame = bytearray.fromhex(errors[1]["hex"])
            second_id = int.from_bytes(frame[18:20], "big")
            frame[18:20] = first_id.to_bytes(2, "big")
            repair(frame)
            errors[1]["hex"] = frame.hex()
            path.write_text("".join(json.dumps(row) + "\n" for row in rows))
            path = directory / "trace.txt"
            path.write_text(path.read_text().replace(f"ip id {second_id} ", f"ip id {first_id} "))
            report = check.check_capture(directory)
        sources = [row["outputTrace"]["source"] for row in report["icmpFrames"]]
        self.assertEqual(len(set(sources)), 12)

    def test_omitted_udp_checksum_stays_zero_at_every_hook(self):
        def mutate(directory):
            path = directory / "trace.txt"
            lines = path.read_text().splitlines()
            index = next(
                index
                for index, line in enumerate(lines)
                if "netlib_trace afterDestination packet:" in line and "ip id 64773 " in line
            )
            lines[index] = lines[index].replace("udp checksum 0", "udp checksum 1")
            path.write_text("\n".join(lines) + "\n")

        self.reject(mutate, "whole UDP.*checksum")

    def test_udp_icmp_late_hook_is_required_once(self):
        def mutate(directory, duplicate):
            path = directory / "trace.txt"
            lines = path.read_text().splitlines()
            index = next(
                index
                for index, line in enumerate(lines)
                if " netlib_icmp_late late packet: iif " in line
            )
            lines[index : index + 2] = lines[index : index + 2] * (2 if duplicate else 0)
            path.write_text("\n".join(lines) + "\n")

        for duplicate in (False, True):
            with self.subTest(duplicate=duplicate):
                self.reject(
                    lambda directory: mutate(directory, duplicate), "late hook must occur once"
                )

    def test_udp_icmp_late_hook_ipv4_metadata_is_checked(self):
        def mutate(directory):
            path = directory / "trace.txt"
            lines = path.read_text().splitlines()
            index = next(
                index
                for index, line in enumerate(lines)
                if " netlib_icmp_late late packet: iif " in line
            )
            lines[index] = lines[index].replace("ip ttl 63", "ip ttl 62")
            path.write_text("\n".join(lines) + "\n")

        self.reject(mutate, "IPv4 metadata")

    def test_udp_icmp_late_hook_drop_is_checked(self):
        def mutate(directory):
            path = directory / "trace.txt"
            path.write_text(
                path.read_text().replace(
                    "netlib_icmp_late late policy accept", "netlib_icmp_late late policy drop", 1
                )
            )

        self.reject(mutate, "late.*verdict|continues after a drop")

    def test_output_trace_has_terminal_verdict(self):
        def mutate(directory):
            path = directory / "trace.txt"
            lines = path.read_text().splitlines()
            index = next(
                index
                for index, line in enumerate(lines)
                if " netlib_icmp outputBefore policy accept" in line
            )
            del lines[index]
            path.write_text("\n".join(lines) + "\n")

        self.reject(mutate, "terminal")

    def test_output_trace_tos_must_match_raw(self):
        def mutate(directory):
            path = directory / "trace.txt"
            path.write_text(
                path.read_text().replace("ip dscp cs6 ip ecn ect0", "ip dscp cs6 ip ecn not-ect", 1)
            )

        self.reject(mutate, "metadata")

    def test_valid_checksum_does_not_hide_wrong_outer_address(self):
        self.change_error(lambda frame: frame.__setitem__(29, frame[29] ^ 1), "NAT addresses")

    def test_valid_checksum_does_not_hide_wrong_outer_tos(self):
        self.change_error(lambda frame: frame.__setitem__(15, frame[15] ^ 1), "TOS")

    def test_valid_checksum_does_not_hide_wrong_outer_ttl(self):
        self.change_error(lambda frame: frame.__setitem__(22, 63), "TTL")

    def test_valid_checksum_does_not_hide_wrong_df(self):
        self.change_error(lambda frame: frame.__setitem__(20, 64), "flags")

    def test_quote_compares_entire_original_prefix(self):
        self.change_error(
            lambda frame: frame.__setitem__(70, frame[70] ^ 1),
            "ICMP quote",
            selector=lambda row, data: len(data) == 590,
        )

    def test_valid_shorter_quote_rejected(self):
        def change(frame):
            del frame[-1:]
            frame[16:18] = (len(frame) - 14).to_bytes(2, "big")

        self.change_error(change, "quote boundary", selector=lambda row, data: len(data) == 590)

    def test_icmp_checksum_is_independent(self):
        def mutate(rows):
            row = next(row for row in rows if bytes.fromhex(row["hex"])[23] == 1)
            frame = bytearray.fromhex(row["hex"])
            frame[36] ^= 1
            row["hex"] = frame.hex()

        self.change_frames(mutate, "valid ICMP")

    def test_icmp_reserved_word_checked(self):
        self.change_error(lambda frame: frame.__setitem__(38, 1), "code or next-hop MTU")

    def test_quote_partial_checksum_is_not_whole_udp_validation(self):
        report = check.check_capture(CAPTURE)
        partial = next(row for row in report["icmpFrames"] if row["quotedIpLength"] == 549)
        quote = bytes.fromhex(partial["quoteHex"])
        pseudo = quote[12:20] + bytes((0, 17)) + partial["quotedUdpLength"].to_bytes(2, "big")
        self.assertNotEqual(check.wire.folded_sum(pseudo + quote[20:]), 65535)

    def test_icmp_measured_before_post_step_snapshot(self):
        observations = json.loads((CAPTURE / "observations.json").read_text())
        probe = observations["mtuProbes"][6]

        def mutate(rows):
            row = next(
                row
                for row in rows
                if bytes.fromhex(row["hex"])[23] == 1
                and int.from_bytes(bytes.fromhex(row["hex"])[46:48], "big") == 0xFD06
            )
            row["timeNs"] = probe["after"]["command"]["startNs"] + 1

        self.change_frames(mutate, "measured drop interval")

    def test_output_related_policy_is_exact(self):
        self.change_export(
            lambda value: value["finalExports"]["output"],
            lambda document: document["nftables"][2]["chain"].update(policy="accept"),
            "output or forwarding policy",
        )

    def test_hidden_hook_rejected_with_consistent_stdout(self):
        self.change_export(
            lambda value: value["finalExports"]["ruleset"],
            lambda document: document["nftables"].append(
                {"table": {"family": "ip", "name": "hidden"}}
            ),
            "unaccounted hook",
        )

    def test_related_counter_binds_all_errors(self):
        def change(document):
            rule = next(
                row["rule"]
                for row in document["nftables"]
                if row.get("rule", {}).get("comment") == "ICMP_RELATED"
            )
            rule["expr"][-1]["counter"]["packets"] -= 1

        self.change_export(
            lambda value: value["finalExports"]["ruleset"], change, "RELATED counter"
        )

    def test_settings_stdout_bound_to_command(self):
        def mutate(directory):
            path = directory / "icmp-settings.txt"
            path.write_text(path.read_text().replace("icmp_ratelimit = 0", "icmp_ratelimit = 1000"))

        self.reject(mutate, "settings stdout")

    def test_output_trace_related_rule_is_required(self):
        def mutate(directory):
            path = directory / "trace.txt"
            path.write_text(
                path.read_text().replace(
                    "rule ct state related counter", "rule ct state established counter", 1
                )
            )

        self.reject(mutate, "RELATED classification")


if __name__ == "__main__":
    unittest.main()
