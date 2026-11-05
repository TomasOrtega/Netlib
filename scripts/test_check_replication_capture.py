"""Native replication evidence and contradiction regressions."""

import json
import re
import shutil
import tempfile
import unittest
from pathlib import Path

import check_replication_capture as check

CAPTURE = Path(__file__).resolve().parents[1] / "examples/replication/native"


class FTFWTests(unittest.TestCase):
    NEW = (
        "1000005400000042"
        "000c0000c0000202cb007102"
        "00080005000001b8"
        "0005000211000000"
        "00080003a0281f90"
        "0008000700000000"
        "0008000ccb007101"
        "0008000dc6336402"
        "0006000e409c0000"
        "0006000f28230000"
    )

    def test_decode_selected_nat_record_and_native_port_encoding(self):
        message = check.decode_ftfw(self.NEW, byteorder="little")[0]
        self.assertEqual((message["type"], message["sequence"]), ("new", 66))
        self.assertEqual(message["attributes"]["original"], check.ORIGINAL)
        self.assertEqual(message["attributes"]["status"], 440)
        self.assertEqual(message["attributes"]["sourceNAT"], "203.0.113.1")
        self.assertEqual(message["attributes"]["destinationNAT"], "198.51.100.2")
        self.assertEqual(message["attributes"]["sourceNATPort"], 40000)
        self.assertEqual(message["attributes"]["destinationNATPort"], 9000)
        self.assertNotIn("remainingTTL", message["attributes"])

    def test_control_and_aggregated_messages(self):
        acknowledgment = "1a080010000000430000004200000042"
        alive = "1a10000800000044"
        rows = check.decode_ftfw(acknowledgment + alive, byteorder="little")
        self.assertEqual([row["type"] for row in rows], ["ack", "alive"])
        self.assertEqual(rows[0]["fromSequence"], 66)
        self.assertEqual(rows[0]["toSequence"], 66)

    def test_malformed_header_and_attribute_rejected(self):
        changes = (
            "20" + self.NEW[2:],
            self.NEW[:4] + "ffff" + self.NEW[8:],
            self.NEW + "00",
            self.NEW.replace("0006000e409c0000", "0005000e40000000"),
            self.NEW.replace("0006000e409c0000", "0006000e409c0001"),
            self.NEW.replace("0008000700000000", "0008000500000000"),
            self.NEW.replace("0008000700000000", "0008002100000000"),
            "1a180010000000430000004200000042",
        )
        for raw in changes:
            with self.subTest(raw=raw), self.assertRaises(check.EvidenceError):
                check.decode_ftfw(raw, byteorder="little")

    def test_external_cache_xml_exposes_original_and_status_labels(self):
        raw = (
            '<flow><meta direction="original"><layer3 protonum="2" protoname="ipv4">'
            "<src>192.0.2.2</src><dst>203.0.113.2</dst></layer3>"
            '<layer4 protonum="17" protoname="udp"><sport>41000</sport><dport>8080</dport>'
            '</layer4></meta><meta direction="reply"><layer3 protonum="0" protoname="unknown">'
            '<src></src><dst></dst></layer3><layer4 protonum="0" protoname="unknown"></layer4>'
            '</meta><meta direction="independent"><unreplied/></meta></flow>\n'
        )
        rows = check.decode_cache_xml(raw)
        self.assertEqual(rows, [{"original": check.ORIGINAL, "unreplied": True, "assured": False}])
        marked = check.decode_cache_xml(raw.replace("<unreplied/>", "<mark>0</mark><unreplied/>"))
        self.assertEqual(marked[0]["mark"], 0)
        self.assertEqual(check.decode_cache_xml(""), [])
        for bad in (
            raw.replace("41000", "-1"),
            raw.replace("<unreplied/>", "<status>440</status>"),
        ):
            with self.subTest(raw=bad), self.assertRaises(check.EvidenceError):
                check.decode_cache_xml(bad)

    def test_native_update_retains_zero_synproxy_extension(self):
        update = "11000064" + self.NEW[8:] + "0010001f" + "00" * 12
        row = check.decode_ftfw(update, byteorder="little")[0]
        self.assertEqual(row["attributes"]["synproxy"], [0, 0, 0])
        changed = update[:-2] + "01"
        with self.assertRaisesRegex(check.EvidenceError, "SYNPROXY"):
            check.decode_ftfw(changed, byteorder="little")

    def test_fenced_primary_loses_only_its_connected_data_routes(self):
        routes = check.expected_routes("a", {"original": "b", "reply": "b"}, fenced=True)
        self.assertEqual(
            routes,
            {
                ("10.10.0.0/24", "syncl", None, "10.10.0.1", None),
                ("203.0.113.1", None, None, None, "blackhole"),
            },
        )

    def test_neighbor_alias_uses_the_actual_peer_interface_mac(self):
        row = {
            "dst": "198.51.100.2",
            "dev": "sbr",
            "lladdr": "02:00:00:10:03:00",
            "state": ["STALE"],
        }
        check.check_neighbor(row, "b")
        with self.assertRaises(check.EvidenceError):
            check.check_neighbor({**row, "lladdr": "02:00:00:10:02:00"}, "b")


class CaptureTests(unittest.TestCase):
    def move_command(self, directory, expected, stamp):
        commands = json.loads((directory / "commands.json").read_text())
        manifest = json.loads((directory / "capture.json").read_text())
        index = next(index for index, row in enumerate(commands) if row["arguments"] == expected)
        commands[index].update(startNs=stamp, endNs=stamp + 1)
        order = sorted(range(len(commands)), key=lambda index: commands[index]["startNs"])
        mapping = {before: after for after, before in enumerate(order)}

        def update(value):
            if isinstance(value, dict):
                for key, child in value.items():
                    if key == "command" and type(child) is int:
                        value[key] = mapping[child]
                    elif key == "commands":
                        value[key] = [mapping[index] for index in child]
                    else:
                        update(child)
            elif isinstance(value, list):
                for child in value:
                    update(child)

        update(manifest)
        for event in manifest["events"]:
            if event["type"] in ("handoff", "commit", "policy"):
                event["result"] = mapping[event["result"]]
            elif event["type"] == "fence":
                event["result"] = [mapping[index] for index in event["result"]]
        (directory / "capture.json").write_text(json.dumps(manifest))
        (directory / "commands.json").write_text(json.dumps([commands[index] for index in order]))

    def reject_change(self, change, pattern="."):
        with tempfile.TemporaryDirectory() as temporary:
            directory = Path(temporary) / "native"
            shutil.copytree(CAPTURE, directory)
            change(directory)
            with self.assertRaisesRegex(check.EvidenceError, pattern):
                check.check_capture(directory)

    def change_json(self, filename, change, pattern="."):
        def mutate(directory):
            path = directory / filename
            value = json.loads(path.read_text())
            change(value)
            path.write_text(json.dumps(value))

        self.reject_change(mutate, pattern)

    def export_change(self, filename, change, pattern="."):
        def mutate(directory):
            path = directory / filename
            value = json.loads(path.read_text())
            change(value)
            text = json.dumps(value)
            path.write_text(text)
            commands = json.loads((directory / "commands.json").read_text())
            manifest = json.loads((directory / "capture.json").read_text())

            def references(value):
                if isinstance(value, dict):
                    if value.get("file") == filename:
                        yield value["command"]
                    for child in value.values():
                        yield from references(child)
                elif isinstance(value, list):
                    for child in value:
                        yield from references(child)

            indices = list(references(manifest))
            self.assertEqual(len(indices), 1)
            commands[indices[0]]["stdout"] = text
            (directory / "commands.json").write_text(json.dumps(commands))

        self.reject_change(mutate, pattern)

    def test_retained_capture(self):
        report = check.check_capture(CAPTURE)
        self.assertEqual(
            (
                report["packetCount"],
                report["snapshotCount"],
                report["frameCount"],
                report["nflogCount"],
            ),
            (6, 56, 20, 16),
        )
        stage = report["events"][1]
        self.assertEqual(stage["before"]["b"], [])
        self.assertFalse(stage["cache"][0]["seenReply"])
        self.assertTrue(stage["sourceSync"])
        self.assertEqual(report["events"][6]["after"]["b"][0]["status"], 440)
        packets = [row for row in report["events"] if row["type"] == "packet"]
        self.assertEqual(
            [row["disposition"] for row in packets],
            ["forwarded", "routeDrop", "forwardDrop", "forwarded", "forwarded", "forwarded"],
        )
        self.assertEqual(
            [row["classification"] for row in packets],
            ["new", "new", "established", "established", "established", "established"],
        )
        self.assertIsNone(packets[1]["outputEthernetHex"])
        self.assertTrue(packets[-1]["outputEthernetHex"])

    def test_command_success_cannot_replace_actual_kernel_install(self):
        def mutate(directory):
            shutil.copyfile(
                directory / "initial-b-conntrack.json", directory / "commit-after-b-conntrack.json"
            )

        self.reject_change(mutate, "record presence")

    def test_conntrack_raw_completion_and_structured_fields_are_checked(self):
        self.change_json(
            "initial-b-conntrack.json", lambda value: value["messages"].clear(), "DONE"
        )
        self.change_json(
            "commit-after-b-conntrack.json",
            lambda value: value["entries"][0].update(status=442),
            "structured",
        )

    def test_positive_lifetime_is_required_at_every_native_prefix(self):
        def mutate(value):
            row = value["entries"][0]
            before = b"\x08\0\x07\0" + row["remainingTTL"].to_bytes(4, "big")
            after = b"\x08\0\x07\0" + bytes(4)
            row["remainingTTL"] = 0
            row["raw"] = bytes.fromhex(row["raw"]).replace(before, after).hex()
            value["messages"] = [
                bytes.fromhex(raw).replace(before, after).hex() for raw in value["messages"]
            ]

        self.change_json("continued-original-before-a-conntrack.json", mutate, "lifetime")

    def test_commit_timeout_does_not_accept_lifetime_above_configured_bound(self):
        def mutate(value):
            row = value["entries"][0]
            before = b"\x08\0\x07\0" + row["remainingTTL"].to_bytes(4, "big")
            after = b"\x08\0\x07\0" + (181).to_bytes(4, "big")
            row["remainingTTL"] = 181
            row["raw"] = bytes.fromhex(row["raw"]).replace(before, after).hex()
            value["messages"] = [
                bytes.fromhex(raw).replace(before, after).hex() for raw in value["messages"]
            ]

        self.change_json("commit-after-b-conntrack.json", mutate, "lifetime")

    def test_cache_presence_cannot_be_inferred_from_sync_or_commit(self):
        self.reject_change(lambda directory: (directory / "stage-b-cache-0.xml").write_text(""))

    def test_daemon_mode_and_timeout_are_bound_to_configuration(self):
        for before, after in (
            ("DisableExternalCache Off", "DisableExternalCache On"),
            ("CommitTimeout 180", "CommitTimeout 1"),
        ):
            with self.subTest(before=before):
                self.reject_change(
                    lambda directory: (directory / "b.conf").write_text(
                        (directory / "b.conf").read_text().replace(before, after)
                    ),
                    "configuration",
                )

    def test_matching_sync_frame_aliases_cannot_override_source_nat(self):
        def mutate(directory):
            for actor in ("a", "b"):
                path = directory / f"{actor}-frames.jsonl"
                rows = [json.loads(line) for line in path.read_text().splitlines()]
                for row in rows:
                    if "hex" not in row or not row["interface"].startswith("sync"):
                        continue
                    frame = bytearray.fromhex(row["hex"])
                    if b"\0\x06\0\x0e\x40\x9c" not in frame:
                        continue
                    frame = frame.replace(b"\0\x06\0\x0e\x40\x9c", b"\0\x06\0\x0e\x41\x9c")
                    size = int.from_bytes(frame[16:18], "big")
                    frame[40:42] = bytes(2)
                    udp = frame[34 : 14 + size]
                    pseudo = frame[26:34] + bytes((0, 17)) + len(udp).to_bytes(2, "big")
                    checksum = 65535 - check.wire.folded_sum(pseudo + udp)
                    frame[40:42] = (checksum or 65535).to_bytes(2, "big")
                    row["hex"] = frame.hex()
                path.write_text("".join(json.dumps(row) + "\n" for row in rows))

        self.reject_change(mutate, "FTFW record")

    def test_every_selected_af_frame_is_consumed(self):
        def mutate(directory):
            path = directory / "client-frames.jsonl"
            lines = path.read_text().splitlines()
            index = next(
                index
                for index, line in enumerate(lines)
                if json.loads(line).get("packetType") == 0
                and "7265706c69636174696f6e3a7065726d6974746564" in line
            )
            del lines[index]
            path.write_text("\n".join(lines) + "\n")

        self.reject_change(mutate, "Missing or additional")

    def test_observer_failure_and_unexpected_socket_errors_are_rejected(self):
        self.change_json(
            "capture.json", lambda value: value["observers"][1].update(returncode=1), "Observer"
        )

        def mutate(directory):
            path = directory / "a-frames.jsonl"
            text = path.read_text()
            self.assertIn('"socketError": 100', text)
            path.write_text(text.replace('"socketError": 100', '"socketError": 99', 1))

        self.reject_change(mutate, "socket error")

    def test_route_owners_and_rpdb_are_actual_readbacks(self):
        self.export_change(
            "uncommitted-before-server-routes.json",
            lambda rows: next(row for row in rows if row["dst"] == "203.0.113.1").update(
                gateway="198.51.100.1"
            ),
            "route ownership",
        )
        self.export_change(
            "permitted-before-b-rules.json",
            lambda rows: rows.append({"priority": 100, "src": "all", "table": 123}),
            "RPDB",
        )

    def test_fence_and_full_policy_exports_cannot_be_overridden(self):
        self.export_change(
            "fence-primary-after-a-links.json",
            lambda rows: next(row for row in rows if row["ifname"] == "car")["flags"].append("UP"),
            "fence",
        )
        self.export_change(
            "denied-before-b-nftables.json",
            lambda value: next(
                row["chain"]
                for row in value["nftables"]
                if "chain" in row and row["chain"]["table"] == "netlib"
            ).update(policy="accept"),
            "ruleset",
        )

    def test_unknown_journal_mutation_is_rejected(self):
        def mutate(rows):
            row = next(row for row in rows if row["arguments"][:3] == ["ip", "link", "add"])
            row["arguments"][2] = "delete"

        self.change_json("commands.json", mutate, "unaccounted mutations")

    def test_bootstrap_must_precede_initial_state_readbacks(self):
        def mutate(directory):
            manifest = json.loads((directory / "capture.json").read_text())
            commands = json.loads((directory / "commands.json").read_text())
            stamp = commands[manifest["initialCaches"]["b"]["command"]]["endNs"] + 1
            self.move_command(
                directory,
                ["ip", "netns", "exec", "b", "ip", "route", "add", "blackhole", "203.0.113.1/32"],
                stamp,
            )

        self.reject_change(mutate, "Setup mutation")

    def test_duplicate_observer_cannot_hide_failure(self):
        def mutate(value):
            value["observers"].insert(
                0,
                {
                    **value["observers"][0],
                    "command": ["true"],
                    "returncode": 99,
                    "runningBeforeStop": False,
                },
            )

        self.change_json("capture.json", mutate, "observer")

    def test_endpoint_identity_binding_and_lifetime_are_checked(self):
        changes = (
            lambda value: value["endpoints"][0].update(command=["true"]),
            lambda value: value["endpoints"][0].update(returncode=99),
            lambda value: value["endpoints"][0]["binding"]["response"]["result"].update(
                local=["127.0.0.1", 1]
            ),
        )
        for change in changes:
            with self.subTest(change=change):
                self.change_json("capture.json", change, "endpoint")

    def test_daemon_shutdown_must_follow_last_daemon_observation(self):
        def mutate(directory):
            manifest = json.loads((directory / "capture.json").read_text())
            stamp = manifest["events"][1]["endNs"] + 1
            self.move_command(
                directory,
                ["ip", "netns", "exec", "b", "conntrackd", "-C", f"{check.BASE}/b.conf", "-k"],
                stamp,
            )

        self.reject_change(mutate, "Daemon was stopped")

    def test_internal_cache_must_match_actual_source_tuple(self):
        def mutate(directory):
            manifest = json.loads((directory / "capture.json").read_text())
            reference = manifest["events"][1]["result"]["internal"]
            path = directory / reference["file"]
            text = path.read_text().replace("192.0.2.2", "192.0.2.99")
            path.write_text(text)
            commands = json.loads((directory / "commands.json").read_text())
            commands[reference["command"]]["stdout"] = text
            (directory / "commands.json").write_text(json.dumps(commands))

        self.reject_change(mutate, "internal cache")

    def test_intermediate_translated_checksum_is_checked(self):
        def mutate(directory):
            path = directory / "a-trace.txt"
            text, count = re.subn(
                r"(ip netlib forward packet: [^\n]*udp checksum )(\d+)",
                lambda matched: matched[1] + str((int(matched[2]) + 1) % 65536),
                path.read_text(),
            )
            self.assertEqual(count, 1)
            path.write_text(text)

        self.reject_change(mutate, "translated checksum")

    def test_route_operation_leg_cannot_disagree_with_coherent_readbacks(self):
        def mutate(directory):
            manifest = json.loads((directory / "capture.json").read_text())
            commands = json.loads((directory / "commands.json").read_text())
            manifest["events"][2]["leg"] = "reply"
            client = (directory / "initial-client-routes.json").read_text()
            server = (directory / "server-route-after-server-routes.json").read_text()
            observations = [manifest["events"][2]["after"], manifest["final"]]
            observations += [
                event[side] for event in manifest["events"][3:] for side in ("before", "after")
            ]
            for observation in observations:
                for actor, text in (("client", client), ("server", server)):
                    reference = observation["networks"][actor]["routes"]
                    (directory / reference["file"]).write_text(text)
                    commands[reference["command"]]["stdout"] = text
            (directory / "capture.json").write_text(json.dumps(manifest))
            (directory / "commands.json").write_text(json.dumps(commands))

        self.reject_change(mutate, "handoff leg")

    def test_route_attributes_cannot_hide_tos_or_mtu_selectors(self):
        for extra in (
            {"tos": 16},
            {"mtu": 28},
            {"nexthops": [{"gateway": "192.0.3.2", "dev": "cbr"}]},
        ):
            with self.subTest(extra=extra):
                self.export_change(
                    "continued-original-before-b-routes.json",
                    lambda rows: next(row for row in rows if row["dst"] == "198.51.100.2").update(
                        extra
                    ),
                    "route attribute",
                )

    def test_sync_update_cannot_precede_its_actual_source_state(self):
        def mutate(directory):
            manifest = json.loads((directory / "capture.json").read_text())
            stamp = manifest["events"][5]["endNs"] + 1
            for actor in ("a", "b"):
                path = directory / f"{actor}-frames.jsonl"
                rows = [json.loads(line) for line in path.read_text().splitlines()]
                selected = []
                for row in rows:
                    if "hex" not in row:
                        continue
                    frame = bytes.fromhex(row["hex"])
                    if (
                        row["interface"].startswith("sync")
                        and frame[12:14] == b"\x08\0"
                        and frame[26:30] == bytes((10, 10, 0, 2))
                    ):
                        selected.append(row)
                self.assertTrue(selected)
                for index, row in enumerate(sorted(selected, key=lambda row: row["timeNs"])):
                    row["timeNs"] = stamp + index
                rows.sort(key=lambda row: row["timeNs"])
                path.write_text("".join(json.dumps(row) + "\n" for row in rows))

        self.reject_change(mutate, "source state")


if __name__ == "__main__":
    unittest.main()
