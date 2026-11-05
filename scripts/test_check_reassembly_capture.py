"""Synthetic decoder contradictions stay separate from retained native packets."""

import copy
import json
import shutil
import struct
import tempfile
import unittest
from pathlib import Path

import check_reassembly_capture as check


def attribute(kind, payload, padding=0):
    size = 4 + len(payload)
    return struct.pack("=HH", size, kind) + payload + bytes((padding,)) * ((-size) % 4)


def packet(flags=0x6000, payload=b"odd"):
    header = bytes.fromhex("450000170123000040110000c0000202cb007102")
    header = header[:6] + flags.to_bytes(2, "big") + header[8:]
    crc = 65535 - check.wire.folded_sum(header)
    return header[:10] + crc.to_bytes(2, "big") + header[12:] + payload


def message(padding=0):
    ethernet = bytes.fromhex("02000000ea0102000000ea020800")
    attributes = b"".join(
        attribute(kind, data, padding)
        for kind, data in (
            (1, bytes.fromhex("08000000")),
            (3, bytes(16)),
            (4, (3).to_bytes(4, "big")),
            (8, bytes.fromhex("0006000002000000ea020000")),
            (9, packet()),
            (10, b"PRE_DEFRAG\0"),
            (12, bytes(4)),
            (13, (1).to_bytes(4, "big")),
            (15, bytes.fromhex("0001")),
            (16, ethernet),
            (17, bytes.fromhex("000e")),
        )
    )
    raw = (
        struct.pack("=IHHII", 20 + len(attributes), 0x400, 0, 0, 0)
        + bytes((2, 0, 0, 42))
        + attributes
    )
    return {"timeNs": 1, "sender": [0, 0], "flags": 0, "hex": raw.hex()}


class DecodeTests(unittest.TestCase):
    def test_link_inventory_cannot_hide_duplicate_interface(self):
        row = {
            "ifname": "peer0",
            "mtu": 600,
            "address": "02:00:00:00:ea:02",
            "flags": ["UP"],
            "link_type": "ether",
        }
        with self.assertRaisesRegex(check.EvidenceError, "duplicate"):
            check.check_links([{**row, "mtu": 1500}, row], "peer")

    def test_ipv4_payload_is_preserved_before_queue_normalization(self):
        result = check.decode_ipv4(packet().hex())
        self.assertTrue(result["dontFragment"])
        self.assertTrue(result["moreFragments"])
        self.assertEqual(result["payloadHex"], b"odd".hex())

    def test_nflog_padding_is_not_packet_data(self):
        result = check.decode_nflog(message(0xA5), 1)
        self.assertEqual(result["packet"]["raw"], packet().hex())

    def test_nflog_packet_and_hardware_metadata(self):
        result = check.decode_nflog(message(), 7)
        self.assertEqual(result["source"], "nflog.jsonl:7")
        self.assertEqual(result["prefix"], "PRE_DEFRAG")
        self.assertEqual(result["inputIndex"], 3)
        self.assertEqual((result["localSequence"], result["globalSequence"]), (0, 1))

    def test_nflog_requires_kernel_sender(self):
        row = message()
        row["sender"][0] = 1
        with self.assertRaisesRegex(check.EvidenceError, "kernel"):
            check.decode_nflog(row, 1)

    def test_bad_ipv4_checksum_is_rejected(self):
        raw = bytearray(packet())
        raw[10] ^= 1
        with self.assertRaisesRegex(check.EvidenceError, "checksum"):
            check.decode_ipv4(raw.hex())

    def test_reserved_ipv4_flag_is_unsupported(self):
        with self.assertRaisesRegex(check.EvidenceError, "reserved"):
            check.decode_ipv4(packet(0x8000).hex())

    def test_duplicate_netlink_attribute_is_rejected(self):
        with self.assertRaisesRegex(check.EvidenceError, "duplicate"):
            check.netlink_attributes(attribute(9, b"a") + attribute(9, b"b"))


class NativeCaptureTests(unittest.TestCase):
    def test_native_capture_accounts_for_all_observation_surfaces(self):
        evidence = check.check_capture(check.DIRECTORY / "native")
        self.assertEqual(
            {
                key: evidence[key]
                for key in (
                    "eventCount",
                    "fragmentCount",
                    "waitCount",
                    "eraseCount",
                    "stateObservationCount",
                    "timeoutEmissionCount",
                    "nflogCount",
                    "frameCount",
                )
            },
            {
                "eventCount": 82,
                "fragmentCount": 79,
                "waitCount": 2,
                "eraseCount": 1,
                "stateObservationCount": 73,
                "timeoutEmissionCount": 2,
                "nflogCount": 107,
                "frameCount": 266,
            },
        )
        self.assertEqual(len(evidence["afAliases"]), 21)
        waits = [event for event in evidence["events"] if event["type"] == "wait"]
        self.assertEqual([event["expired"][0]["zone"] for event in waits], [0, 10])
        for event in waits:
            self.assertEqual(
                event["expired"][0]["firstSource"],
                event["timeoutEmissions"][0]["quotedFirstSource"],
            )

    def reject_observations(self, change, pattern="."):
        with tempfile.TemporaryDirectory() as temporary:
            directory = Path(temporary) / "native"
            shutil.copytree(check.DIRECTORY / "native", directory)
            path = directory / "observations.json"
            observed = json.loads(path.read_text())
            change(observed)
            for stage in observed["stages"]:
                selected = next(step for step in observed["steps"] if step["name"] == stage["name"])
                stage.clear()
                stage.update(copy.deepcopy(selected))
            path.write_text(json.dumps(observed))
            with self.assertRaisesRegex(check.EvidenceError, pattern):
                check.check_capture(directory)

    def test_raw_send_requires_actual_server_receive_rpc(self):
        self.reject_observations(
            lambda observed: next(
                step for step in observed["steps"] if step["name"] == "permit-split-tail"
            ).update(server=None),
            "server|RPC",
        )

    def test_permitted_reply_requires_sender_and_client_rpcs(self):
        for key in ("reply", "client"):
            with self.subTest(key=key):
                self.reject_observations(
                    lambda observed, key=key: next(
                        step for step in observed["steps"] if step["name"] == "credential-permitted"
                    ).update({key: None}),
                    "reply|client|RPC",
                )

    def test_denied_socket_requires_client_timeout_rpc(self):
        self.reject_observations(
            lambda observed: next(
                step for step in observed["steps"] if step["name"] == "authenticated-only"
            ).update(client=None),
            "client|RPC",
        )

    def test_reply_and_receive_payloads_must_match_actual_wire_bytes(self):
        for key in ("reply", "client", "server"):
            with self.subTest(key=key):

                def change(observed, key=key):
                    step = next(
                        step for step in observed["steps"] if step["name"] == "credential-permitted"
                    )
                    step[key]["result"]["payload"] = "fabricated reply"

                self.reject_observations(change, "payload|receive")

    def test_client_read_cannot_precede_reply_send(self):
        def change(observed):
            step = next(
                step for step in observed["steps"] if step["name"] == "credential-permitted"
            )
            step["client"]["startNs"] = step["reply"]["startNs"] - 2
            step["client"]["endNs"] = step["reply"]["startNs"] - 1

        self.reject_observations(change, "order|RPC|reply|client")

    def test_each_send_requires_all_native_link_readbacks(self):
        for value in (None, {}):
            with self.subTest(value=value):
                self.reject_observations(
                    lambda observed, value=value: next(
                        step for step in observed["steps"] if step["name"] == "permit-split-tail"
                    ).update(links=value),
                    "link|MTU",
                )

    def test_post_snapshot_cannot_alias_another_episode(self):
        def change(observed):
            observed["steps"][2]["after"] = copy.deepcopy(observed["steps"][3]["after"])

        self.reject_observations(change, "snapshot|conntrack|artifact")

    def test_short_policy_must_follow_actual_readback(self):
        def change(observed):
            next(step for step in observed["steps"] if step["queuePolicy"] == "normal").update(
                queuePolicy="short"
            )

        self.reject_observations(change, "policy")

    def test_final_exports_cannot_be_omitted(self):
        self.reject_observations(lambda observed: observed.update(finalExports={}), "export|table")

    def test_unknown_queue_policy_is_not_normal_by_default(self):
        self.reject_observations(
            lambda observed: next(
                step for step in observed["steps"] if step["name"] == "permit-split-tail"
            ).update(queuePolicy="bogus"),
            "policy",
        )

    def reject_capture(self, change, pattern="."):
        with tempfile.TemporaryDirectory() as temporary:
            directory = Path(temporary) / "native"
            shutil.copytree(check.DIRECTORY / "native", directory)
            change(directory)
            with self.assertRaisesRegex(check.EvidenceError, pattern):
                check.check_capture(directory)

    def test_source_nat_unknown_handle_requires_actual_rule(self):
        def change(directory):
            path = directory / "trace.txt"
            text = path.read_text()
            import re

            text = re.sub(
                r"(ip netlib_nat source )rule[^\n]+( \(verdict accept\))",
                r"\1unknown rule handle 999999\2",
                text,
                count=1,
            )
            path.write_text(text)

        self.reject_capture(change, "handle|rule|trace")

    def test_extra_controller_command_is_not_silently_ignored(self):
        def change(directory):
            path = directory / "commands.json"
            commands = json.loads(path.read_text())
            previous = commands[-1]["endNs"]
            commands.append(
                {
                    "command": ["ip", "-n", "auth", "link", "set", "auth0", "mtu", "9000"],
                    "startNs": previous + 1,
                    "endNs": previous + 2,
                    "returncode": 0,
                    "stdout": "",
                    "stderr": "",
                }
            )
            path.write_text(json.dumps(commands))

        self.reject_capture(change, "Unattributed")

    def test_bootstrap_command_after_readbacks_cannot_escape_journal(self):
        def change(directory):
            path = directory / "commands.json"
            commands = json.loads(path.read_text())
            observed = json.loads((directory / "observations.json").read_text())
            index = max(
                index
                for index, row in enumerate(commands)
                if row["endNs"] < observed["steps"][0]["startNs"]
            )
            previous = commands[index]["endNs"]
            commands.insert(
                index + 1,
                {
                    "command": [
                        "ip",
                        "netns",
                        "exec",
                        "auth",
                        "sysctl",
                        "-w",
                        "net.ipv4.ipfrag_high_thresh=0",
                    ],
                    "startNs": previous + 1,
                    "endNs": previous + 2,
                    "returncode": 0,
                    "stdout": "net.ipv4.ipfrag_high_thresh = 0\n",
                    "stderr": "",
                },
            )
            path.write_text(json.dumps(commands))

        self.reject_capture(change, "Unattributed")

    def test_admission_control_commands_require_the_actual_argv(self):
        for key in ("credentialInstall", "logoff"):
            with self.subTest(key=key):

                def change(directory, key=key):
                    path = directory / "observations.json"
                    observed = json.loads(path.read_text())
                    previous = copy.deepcopy(observed[key])
                    observed[key].update(command=["true"], stdout="", stderr="")
                    journal = directory / "commands.json"
                    commands = json.loads(journal.read_text())
                    commands[commands.index(previous)] = observed[key]
                    journal.write_text(json.dumps(commands))
                    path.write_text(json.dumps(observed))

                self.reject_capture(change, "command|Logoff|credential")

    def test_initial_network_reads_cannot_alias_later_step_reads(self):
        for namespace in ("peer", "auth", "server"):
            with self.subTest(namespace=namespace):
                self.reject_observations(
                    lambda observed, namespace=namespace: observed["networkExports"][
                        f"{namespace}-links"
                    ].update(
                        command=copy.deepcopy(observed["steps"][-1]["links"][namespace]["command"])
                    ),
                    "network|baseline|boundary|reused",
                )

    def test_per_send_interface_indices_must_match_nflog_topology(self):
        def change(directory):
            path = directory / "observations.json"
            observed = json.loads(path.read_text())
            step = observed["steps"][0]
            record = step["links"]["auth"]
            previous = copy.deepcopy(record["command"])
            rows = json.loads(record["command"]["stdout"])
            for row in rows:
                if row["ifname"] != "lo":
                    row["ifindex"] += 9000
            record["command"]["stdout"] = json.dumps(rows) + "\n"
            (directory / record["file"]).write_text(record["command"]["stdout"])
            journal = directory / "commands.json"
            commands = json.loads(journal.read_text())
            commands[commands.index(previous)] = record["command"]
            journal.write_text(json.dumps(commands))
            observed["stages"][0] = copy.deepcopy(step)
            path.write_text(json.dumps(observed))

        self.reject_capture(change, "index|indices|interface")

    def test_route_type_cannot_contradict_the_forwarding_route(self):
        def change(directory):
            path = directory / "observations.json"
            observed = json.loads(path.read_text())
            record = observed["networkExports"]["auth-routes"]
            previous = copy.deepcopy(record["command"])
            rows = json.loads(previous["stdout"])
            next(row for row in rows if row["dst"] == "198.51.100.0/24")["type"] = "blackhole"
            record["command"]["stdout"] = json.dumps(rows) + "\n"
            (directory / record["file"]).write_text(record["command"]["stdout"])
            journal = directory / "commands.json"
            commands = json.loads(journal.read_text())
            commands[commands.index(previous)] = record["command"]
            journal.write_text(json.dumps(commands))
            path.write_text(json.dumps(observed))

        self.reject_capture(change, "routing|route")

    def test_raw_arrival_cannot_precede_actual_inner_send(self):
        def change(directory):
            observed = json.loads((directory / "observations.json").read_text())
            step = next(step for step in observed["steps"] if step["name"] == "permit-split-tail")
            emitted = json.loads(step["sent"]["stdout"])
            path = directory / "nflog.jsonl"
            rows = [json.loads(line) for line in path.read_text().splitlines()]
            row = next(
                row
                for index, row in enumerate(rows, 1)
                if step["startNs"] < row["timeNs"] < step["endNs"]
                and check.decode_nflog(row, index)["prefix"] == "PRE_DEFRAG"
            )
            row["timeNs"] = (step["sent"]["startNs"] + emitted["startNs"]) // 2
            path.write_text("".join(json.dumps(row) + "\n" for row in rows))

        self.reject_capture(change, "actual.*send|emission|causal")

    def test_reply_arrival_cannot_precede_reply_rpc(self):
        def change(directory):
            observed = json.loads((directory / "observations.json").read_text())
            step = next(
                step for step in observed["steps"] if step["name"] == "credential-permitted"
            )
            path = directory / "nflog.jsonl"
            rows = [json.loads(line) for line in path.read_text().splitlines()]
            request_index = 0
            for index, row in enumerate(rows, 1):
                decoded = check.decode_nflog(row, index)
                if step["startNs"] < row["timeNs"] < step["endNs"]:
                    if decoded["packet"]["source"] == "192.0.2.2":
                        request_index += 1
                        row["timeNs"] = step["sent"]["endNs"] + request_index
                    elif decoded["prefix"] == "PRE_DEFRAG":
                        row["timeNs"] = step["server"]["endNs"] + 1
            path.write_text("".join(json.dumps(row) + "\n" for row in rows))

        self.reject_capture(change, "reply.*send|emission|causal")

    def test_whole_fitting_reply_must_remain_one_packet(self):
        def change(directory):
            evidence = check.check_capture(check.DIRECTORY / "native")
            event = next(
                event
                for event in evidence["events"]
                if event["type"] == "fragment"
                and event["stepName"] == "credential-permitted"
                and not event["derived"]["reassembled"]
                and event["observed"]["forwarded"]
            )
            frame = bytes.fromhex(event["observed"]["forwarded"][0])
            ip, data = frame[14:], frame[34:]
            parts = []
            for offset, payload, more in ((0, data[:16], True), (16, data[16:], False)):
                header = bytearray(ip[:20])
                header[2:4] = (20 + len(payload)).to_bytes(2, "big")
                header[6:8] = ((8192 if more else 0) | offset // 8).to_bytes(2, "big")
                header[10:12] = bytes(2)
                header[10:12] = (65535 - check.wire.folded_sum(header)).to_bytes(2, "big")
                parts.append((frame[:14] + header + payload).hex())
            for namespace in ("auth", "peer"):
                path = directory / f"frames-{namespace}.jsonl"
                rows = []
                for line in path.read_text().splitlines():
                    row = json.loads(line)
                    if row["hex"] == frame.hex():
                        rows.extend(
                            {**row, "timeNs": row["timeNs"] + index, "hex": part}
                            for index, part in enumerate(parts)
                        )
                    else:
                        rows.append(row)
                path.write_text("".join(json.dumps(row) + "\n" for row in rows))

        self.reject_capture(change, "Unreassembled|unfragmented|whole")


if __name__ == "__main__":
    unittest.main()
