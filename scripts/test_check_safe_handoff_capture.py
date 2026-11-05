"""Finite safe handoff protocol and evidence contradictions."""

import json
import shutil
import tempfile
import unittest
from pathlib import Path

import check_safe_handoff_capture as check

CAPTURE = Path(__file__).resolve().parents[1] / "examples/safe-handoff/native"


class CaptureTests(unittest.TestCase):
    def reject_change(self, change, pattern="."):
        with tempfile.TemporaryDirectory() as temporary:
            directory = Path(temporary) / "native"
            shutil.copytree(CAPTURE, directory)
            change(directory)
            with self.assertRaisesRegex(check.EvidenceError, pattern):
                check.check_capture(directory)

    def change_manifest(self, change, pattern="."):
        def mutate(directory):
            path = directory / "capture.json"
            manifest = json.loads(path.read_text())
            change(manifest)
            path.write_text(json.dumps(manifest))

        self.reject_change(mutate, pattern)

    def change_export(self, event, side, section, key, change, pattern="."):
        def mutate(directory):
            manifest = json.loads((directory / "capture.json").read_text())
            selected = next(row for row in manifest["events"] if row["id"] == event)
            reference = selected[side][section]
            for part in key if isinstance(key, tuple) else (key,):
                reference = reference[part]
            path = directory / reference["file"]
            value = json.loads(path.read_text())
            change(value)
            text = json.dumps(value)
            path.write_text(text)
            journal = directory / "commands.json"
            commands = json.loads(journal.read_text())
            commands[reference["command"]]["stdout"] = text
            journal.write_text(json.dumps(commands))

        self.reject_change(mutate, pattern)

    def test_actual_safe_handoff(self):
        report = check.check_capture(CAPTURE)
        self.assertEqual((report["packetCount"], report["snapshotCount"]), (7, 84))
        self.assertEqual(report["events"][4]["packet"]["gateway"], "a")
        self.assertEqual(report["events"][9]["packet"]["gateway"], "a")
        self.assertEqual(report["events"][15]["packet"]["disposition"], "forwardDrop")
        self.assertTrue(report["safeFence"]["completedPrimaryTicket"])
        self.assertEqual(report["queuePendingCounts"], [1, 1, 1, 1, 0, 1, 1, 0])

    def test_route_admission_cannot_predate_the_actual_send(self):
        def mutate(directory):
            manifest = json.loads((directory / "capture.json").read_text())
            stamp = manifest["events"][0]["result"]["sender"]["response"]["startNs"] - 1
            path = directory / "client-nflog.jsonl"
            rows = [json.loads(line) for line in path.read_text().splitlines()]
            rows[0]["timeNs"] = stamp
            path.write_text("".join(json.dumps(row) + "\n" for row in rows))
            path = directory / "admission-polls.json"
            polls = json.loads(path.read_text())
            polls[0]["record"]["timeNs"] = stamp
            path.write_text(json.dumps(polls))

        self.reject_change(mutate, "Admission.*send")

    def test_atomic_receive_cannot_finish_before_the_send(self):
        def mutate(manifest):
            result = manifest["events"][0]["result"]
            sender, receiver = result["sender"], result["receiver"]
            receiver.update(startNs=sender["startNs"] + 1, endNs=sender["response"]["startNs"] - 1)
            receiver["response"].update(
                startNs=sender["startNs"] + 2,
                endNs=sender["response"]["startNs"] - 2,
            )

        self.change_manifest(mutate, "receive.*send")

    def test_held_ticket_cannot_be_retargeted_by_a_later_handoff(self):
        self.change_manifest(
            lambda value: value["events"][9].update(gateway="b"), "gateway|admission"
        )

    def test_native_handoff_leg_is_bound_to_the_exact_command(self):
        self.change_manifest(lambda value: value["events"][5].update(leg="reply"), "metadata")

    def test_ticket_identity_is_not_reused_for_an_overtaking_packet(self):
        self.change_manifest(lambda value: value["events"][7].update(ticket=0), "ticket")

    def test_primary_is_still_queued_after_both_route_changes(self):
        self.change_export(
            "server-route",
            "after",
            "qdiscs",
            "cal",
            lambda rows: rows[0].update(qlen=0),
            "pending queue",
        )

    def test_queue_deletion_does_not_substitute_for_completion(self):
        self.change_export(
            "serve-primary",
            "after",
            "qdiscs",
            "cal",
            lambda rows: rows[0].update(drops=1),
            "Queue reports loss",
        )

    def test_queue_delay_and_backlog_are_profile_facts(self):
        self.change_export(
            "admit-primary",
            "after",
            "qdiscs",
            "cal",
            lambda rows: rows[0]["options"]["delay"].update(jitter=0.1),
            "delay-only",
        )
        self.change_export(
            "admit-standby",
            "after",
            "qdiscs",
            "cbl",
            lambda rows: rows[0].update(backlog=66),
            "backlog",
        )

    def test_barrier_names_the_selected_completed_ticket(self):
        self.change_manifest(
            lambda value: value["events"][10]["result"].update(ticket=3), "Drain barrier"
        )

    def test_current_deny_policy_is_required_at_service(self):
        self.change_export(
            "serve-standby",
            "before",
            "tables",
            "b",
            lambda document: document["nftables"].pop(),
            "ruleset",
        )

    def test_held_gateway_logs_cannot_precede_the_actual_service(self):
        def mutate(directory):
            manifest = json.loads((directory / "capture.json").read_text())
            stamp = manifest["events"][13]["endNs"] + 1
            path = directory / "b-nflog.jsonl"
            rows = [json.loads(line) for line in path.read_text().splitlines()]
            selected = []
            for number, row in enumerate(rows, 1):
                decoded = check.legacy.decode_nflog(row, "b", number)
                if decoded["packet"]["payloadHex"] == b"safe-handoff:held-standby".hex():
                    selected.append(row)
            self.assertEqual(len(selected), 2)
            for offset, row in enumerate(selected):
                row["timeNs"] = stamp + offset
            path.write_text("".join(json.dumps(row) + "\n" for row in rows))

        self.reject_change(mutate, "service")

    def test_endpoint_transmit_tap_cannot_precede_held_queue_service(self):
        def mutate(directory):
            manifest = json.loads((directory / "capture.json").read_text())
            stamp = manifest["events"][4]["endNs"] + 1
            path = directory / "client-frames.jsonl"
            rows = [json.loads(line) for line in path.read_text().splitlines()]
            selected = [
                row for row in rows if b"safe-handoff:held-primary" in bytes.fromhex(row["hex"])
            ]
            self.assertEqual(len(selected), 1)
            selected[0]["timeNs"] = stamp
            rows.sort(key=lambda row: row["timeNs"])
            path.write_text("".join(json.dumps(row) + "\n" for row in rows))

        self.reject_change(mutate, "service")

    def test_endpoint_postrouting_policy_is_a_complete_readback(self):
        self.change_export(
            "admit-primary",
            "before",
            "endpointTables",
            "client",
            lambda document: document["nftables"].pop(),
            "route-admission hook",
        )

    def test_boundary_indices_bind_admission_and_gateway_interfaces(self):
        for actor, field in (("client", "links"), ("a", "links"), ("client", "addresses")):
            with self.subTest(actor=actor, field=field):
                self.change_export(
                    "admit-primary",
                    "before",
                    "networks",
                    (actor, field),
                    lambda rows: rows[1].update(ifindex=10003),
                    "interface index",
                )

    def test_link_readback_cannot_add_an_unmodelled_master(self):
        self.change_export(
            "admit-primary",
            "before",
            "networks",
            ("client", "links"),
            lambda rows: rows[1].update(master="vrf-hidden"),
            "link attributes",
        )

    def test_address_readback_cannot_hide_expiry(self):
        self.change_export(
            "admit-primary",
            "before",
            "networks",
            ("client", "addresses"),
            lambda rows: rows[1]["addr_info"][0].update(valid_life_time=1),
            "address attributes",
        )

    def test_boundary_dumps_cannot_reuse_an_earlier_artifact(self):
        for section, keys in (("conntrack", ("a",)), ("networks", ("a", "routes"))):

            def mutate(directory):
                path = directory / "capture.json"
                manifest = json.loads(path.read_text())
                event = manifest["events"][3]
                before, after = event["before"][section], event["after"][section]
                for key in keys:
                    before, after = before[key], after[key]
                after["file"] = before["file"]
                if section == "conntrack":
                    journal = directory / "commands.json"
                    commands = json.loads(journal.read_text())
                    commands[after["command"]]["arguments"][-1] = (
                        check.SAFE_BASE + "/" + before["file"]
                    )
                    journal.write_text(json.dumps(commands))
                path.write_text(json.dumps(manifest))

            with self.subTest(section=section):
                self.reject_change(mutate, "artifact")

    def test_actual_admission_poll_cannot_rewrite_its_raw_source(self):
        def mutate(directory):
            path = directory / "admission-polls.json"
            polls = json.loads(path.read_text())
            polls[1]["record"]["timeNs"] += 1
            path.write_text(json.dumps(polls))

        self.reject_change(mutate, "unchanged NFLOG")

    def test_admission_poll_cannot_read_future_raw_log_records(self):
        def mutate(directory):
            path = directory / "admission-polls.json"
            polls = json.loads(path.read_text())
            polls[0]["attempts"][-1]["lineCount"] = 5
            path.write_text(json.dumps(polls))

        self.reject_change(mutate, "future raw")

    def test_failed_duplicate_observer_is_not_hidden_by_a_mapping(self):
        self.change_manifest(
            lambda value: value["observers"].insert(0, {**value["observers"][0], "returncode": 99}),
            "duplicate raw observer",
        )

    def test_permanent_neighbor_profile_does_not_ignore_extra_arp(self):
        def mutate(directory):
            source = (
                Path(__file__).resolve().parents[1]
                / "examples/replication/native/client-frames.jsonl"
            )
            arp = next(
                row
                for row in map(json.loads, source.read_text().splitlines())
                if bytes.fromhex(row["hex"])[12:14] == bytes.fromhex("0806")
            )
            path = directory / "client-frames.jsonl"
            rows = [json.loads(line) for line in path.read_text().splitlines()]
            arp["timeNs"] = rows[0]["timeNs"] - 1
            rows.insert(0, arp)
            path.write_text("".join(json.dumps(row) + "\n" for row in rows))

        self.reject_change(mutate, "ARP")

    def test_endpoint_process_and_socket_binding_are_bound(self):
        self.change_manifest(
            lambda value: value["endpoints"][0].update(command=["true"]), "Endpoint process"
        )

    def test_barrier_delete_command_is_not_just_a_success_code(self):
        def mutate(directory):
            manifest = json.loads((directory / "capture.json").read_text())
            index = manifest["events"][10]["result"]["deleteCommand"]
            path = directory / "commands.json"
            commands = json.loads(path.read_text())
            commands[index]["arguments"] = ["true"]
            path.write_text(json.dumps(commands))

        self.reject_change(mutate, "control command")


if __name__ == "__main__":
    unittest.main()
