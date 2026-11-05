"""Native NAT, TTL, hook, and producer-join contradiction regressions."""

import copy
import json
import shutil
import tempfile
import unittest
from pathlib import Path

import check_wire_nat_capture as check

CAPTURE = Path(__file__).resolve().parents[1] / "examples/wire-nat/native"


def write(path, value):
    path.write_text(json.dumps(value, indent=2) + "\n")


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

    def change_export(self, selector, change, pattern="."):
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

    def change_raw_scalar(self, document, field, new_value):
        entry = document["entries"][0]
        old_raw = entry["raw"]
        before, after = entry[field].to_bytes(4, "big").hex(), new_value.to_bytes(4, "big").hex()
        self.assertEqual(old_raw.count(before), 1)
        entry[field] = new_value
        entry["raw"] = old_raw.replace(before, after)
        document["messages"] = [
            entry["raw"] if raw == old_raw else raw for raw in document["messages"]
        ]

    def retime_export(self, directory, export_selector, window):
        observations = json.loads((directory / "observations.json").read_text())
        export = export_selector(observations)
        commands = json.loads((directory / "commands.json").read_text())
        original = copy.deepcopy(export["command"])
        start, end = window(observations)
        export["command"].update(startNs=start, endNs=end)
        for row in commands:
            if row == original:
                row.update(startNs=start, endNs=end)
        commands.sort(key=lambda row: row["startNs"])
        write(directory / "commands.json", commands)
        write(directory / "observations.json", observations)

    def test_native_capture(self):
        report = check.check_capture(CAPTURE)
        self.assertEqual(
            (report["frameCount"], report["udpFrameCount"], report["icmpFrameCount"]), (17, 14, 3)
        )
        self.assertEqual(len(report["packetSamples"]), 10)
        self.assertEqual(
            [stage["eapFramesBeforeSend"] for stage in report["stages"]], [0, 16, 16, 18]
        )
        self.assertEqual(report["initialFile"], "initial-conntrack.json")

    def test_tos_and_df_preserved_across_nat(self):
        report = check.check_capture(CAPTURE)
        packet = next(
            row for row in report["packetSamples"] if row["label"] == "credential-permitted-request"
        )
        for offset, mask in ((15, 1), (20, 64)):
            frame = bytearray.fromhex(packet["egress"]["raw"])
            frame[offset] ^= mask
            frame[24:26] = bytes(2)
            frame[24:26] = (65535 - check.wire.folded_sum(frame[14:34])).to_bytes(2, "big")
            changed = check.decode_frame(
                {
                    "hex": frame.hex(),
                    "timeNs": packet["egress"]["timeNs"],
                    "interface": "service0",
                    "packetType": 4,
                },
                1,
            )
            with (
                self.subTest(offset=offset),
                self.assertRaisesRegex(check.EvidenceError, "metadata|TOS|flags"),
            ):
                check.check_trace(packet["trace"], packet["ingress"], changed, "forwarded")

    def test_ttl_export_must_precede_the_probe(self):
        def mutate(directory):
            def window(observations):
                probe = observations["ttlProbes"][0]
                start, end = probe["server"]["endNs"], probe["after"]["command"]["startNs"]
                return start + (end - start) // 4, start + (end - start) // 2

            self.retime_export(
                directory, lambda observations: observations["ttlExports"]["firewall"], window
            )

        self.reject(mutate, "TTL configuration export")

    def test_network_export_must_precede_initial_packet_state(self):
        def mutate(directory):
            self.retime_export(
                directory,
                lambda observations: observations["networkExports"]["auth-routes"],
                lambda observations: (
                    observations["stages"][0]["endNs"] + 100,
                    observations["stages"][0]["endNs"] + 200,
                ),
            )

        self.reject(mutate, "Network export.*initial")

    def test_authorization_status_stdout_is_joined(self):
        def change(commands):
            row = next(
                row
                for row in commands
                if len(row["command"]) > 4 and row["command"][4] == "hostapd_cli"
            )
            row["stdout"] = row["stdout"].replace("flags=[AUTHORIZED]", "flags=")

        self.change_json("commands.json", change, "status export")

    def test_complete_wire_checksum_required(self):
        def change(rows):
            frame = bytearray.fromhex(rows[0]["hex"])
            frame[40] ^= 1
            rows[0]["hex"] = frame.hex()

        self.change_frames(change, "udp-checksum")

    def test_fixed_nat_target_cannot_change(self):
        def change(document):
            rule = next(
                item["rule"]
                for item in document["nftables"]
                if "rule" in item and item["rule"]["chain"] == "source"
            )
            rule["expr"][-1]["snat"]["port"] = 40001

        self.change_export(
            lambda observations: observations["stages"][2]["exports"]["nat"],
            change,
            "fixed NAT policy",
        )

    def test_complete_ruleset_rejects_hidden_hook(self):
        self.change_export(
            lambda observations: observations["stages"][2]["exports"]["ruleset"],
            lambda document: document["nftables"].append(
                {"table": {"family": "ip", "name": "hidden"}}
            ),
            "unaccounted hook",
        )

    def test_established_forward_bypass_rejected(self):
        def change(document):
            document["nftables"].append(
                {
                    "rule": {
                        "family": "ip",
                        "table": "netlib",
                        "chain": "forward",
                        "handle": 999,
                        "comment": "BYPASS",
                        "expr": [
                            {
                                "match": {
                                    "op": "==",
                                    "left": {"ct": {"key": "state"}},
                                    "right": "established",
                                }
                            },
                            {"accept": None},
                        ],
                    }
                }
            )

        self.change_export(
            lambda observations: observations["stages"][3]["exports"]["firewall"],
            change,
            "conntrack bypass",
        )

    def test_initial_state_must_be_authoritatively_empty(self):
        def mutate(directory):
            shutil.copyfile(
                directory / "ttl-two-after-conntrack.json", directory / "initial-conntrack.json"
            )

        self.reject(mutate, "Initial visible")

    def test_reply_seen_before_ttl_drop_requires_raw_status(self):
        self.change_json(
            "after-ttl-one-reply-conntrack.json",
            lambda document: self.change_raw_scalar(document, "status", 440),
            "mark.*seen",
        )

    def test_logoff_drop_keeps_same_cached_binding(self):
        self.change_json(
            "logged-off-cached-conntrack.json",
            lambda document: self.change_raw_scalar(
                document, "id", document["entries"][0]["id"] ^ 1
            ),
            "retain the same",
        )

    def test_fresh_ttl_drop_cannot_confirm(self):
        def mutate(directory):
            shutil.copyfile(
                directory / "ttl-two-after-conntrack.json",
                directory / "ttl-one-after-conntrack.json",
            )

        self.reject(mutate, "unexpectedly confirmed")

    def test_targeted_erase_zone_is_checked(self):
        def mutate(directory):
            observations = json.loads((directory / "observations.json").read_text())
            original = copy.deepcopy(observations["erase"]["command"])
            observations["erase"]["command"]["command"][-1] = "1"
            commands = json.loads((directory / "commands.json").read_text())
            for row in commands:
                if row == original:
                    row["command"][-1] = "1"
            write(directory / "observations.json", observations)
            write(directory / "commands.json", commands)

        self.reject(mutate, "target exactly")

    def test_native_after_dnat_checkpoint_is_not_invented(self):
        def mutate(directory):
            path = directory / "trace.txt"
            lines = path.read_text().splitlines()
            index = next(
                index
                for index, line in enumerate(lines)
                if "netlib_trace afterDestination packet:" in line
            )
            lines[index] = lines[index].replace("ip daddr 198.51.100.2", "ip daddr 198.51.100.3")
            path.write_text("\n".join(lines) + "\n")

        self.reject(mutate, "after DNAT")

    def test_trace_ids_need_not_be_globally_unique(self):
        import re

        with tempfile.TemporaryDirectory() as temporary:
            path = Path(temporary) / "trace.txt"
            text = (CAPTURE / "trace.txt").read_text()
            path.write_text(re.sub(r"(?m)^trace id [0-9a-f]+", "trace id 00000000", text))
            traces = check.parse_traces(path)
            self.assertEqual(len(traces), 10)
            self.assertEqual(len({trace["id"] for trace in traces}), 1)

    def test_time_exceeded_is_observed_separately(self):
        self.change_frames(
            lambda rows: rows.pop(
                next(index for index, row in enumerate(rows) if bytes.fromhex(row["hex"])[23] == 1)
            ),
            "ICMP frame count",
        )

    def test_cached_nat_preserves_explicit_udp_omission(self):
        report = check.check_capture(CAPTURE)
        sample = report["packetSamples"][-1]
        self.assertEqual(sample["label"], "udp-zero")
        self.assertEqual(sample["ingress"]["udpChecksum"], {"value": 0, "status": "omitted"})
        self.assertEqual(sample["egress"]["udpChecksum"], {"value": 0, "status": "omitted"})

    def test_native_producer_version_cannot_disagree(self):
        self.reject(
            lambda directory: (directory / "iproute2-version.txt").write_text(
                "ip utility, iproute2-0.0.0\n"
            ),
            "producer version",
        )

    def test_icmp_quote_must_belong_to_the_drop_interval(self):
        observations = json.loads((CAPTURE / "observations.json").read_text())

        def change(rows):
            row = next(row for row in rows if bytes.fromhex(row["hex"])[23] == 1)
            row["timeNs"] = observations["stages"][1]["endNs"] + 100
            rows.sort(key=lambda item: item["timeNs"])

        self.change_frames(change, "ICMP.*interval")

    def test_socket_ttl_is_bound_to_the_retained_wire_bytes(self):
        def mutate(directory):
            path = directory / "frames.jsonl"
            rows = [json.loads(line) for line in path.read_text().splitlines()]
            identifier = None
            for row in rows:
                frame = bytearray.fromhex(row["hex"])
                if (
                    frame[23] == 17
                    and frame[42:].decode() == "wire-nat:credential-permitted:request"
                ):
                    identifier = int.from_bytes(frame[18:20], "big")
                    frame[22] -= 62
                    frame[24:26] = bytes(2)
                    frame[24:26] = (65535 - check.wire.folded_sum(frame[14:34])).to_bytes(2, "big")
                    row["hex"] = frame.hex()
            self.assertIsNotNone(identifier)
            path.write_text("".join(json.dumps(row) + "\n" for row in rows))
            path = directory / "trace.txt"
            lines = path.read_text().splitlines()
            for index, line in enumerate(lines):
                if f"ip id {identifier} " in line:
                    lines[index] = line.replace("ip ttl 64 ", "ip ttl 2 ").replace(
                        "ip ttl 63 ", "ip ttl 1 "
                    )
            path.write_text("\n".join(lines) + "\n")

        self.reject(mutate, "socket TTL")


if __name__ == "__main__":
    unittest.main()
