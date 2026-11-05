"""Join actual adversary, ingress guard, tracking, and retirement observations."""

import json
import os
import shutil
import struct
import tempfile
import unittest
from pathlib import Path

from attachment_capture_evidence import AttachmentEvidence, EvidenceError
from check_attachment_capture import check_capture

ROOT = Path(__file__).resolve().parents[1]
CAPTURE = Path(os.environ.get("NETLIB_ATTACHMENT_CAPTURE", ROOT / "examples/attachments/native"))


def opened(directory):
    evidence = AttachmentEvidence(directory)
    evidence.boundary("initial")
    for event in evidence.manifest["events"]:
        for side in ("before", "after"):
            evidence.boundary(event["id"] + ":" + side)
    evidence.boundary("final")
    return evidence


class AttachmentNativePathTests(unittest.TestCase):
    def test_whole_native_history_keeps_spoofed_tuple_off_the_attached_input(self):
        result = check_capture(CAPTURE)
        self.assertEqual(result["packetCount"], 15)

    def test_joint_service_exposes_the_single_namespace_kernel_log_order(self):
        result = check_capture(CAPTURE)
        event = next(row for row in result["events"] if row["type"] == "serve-pair")
        self.assertEqual(event["serviceOrder"], [packet["ticket"] for packet in event["packets"]])
        self.assertEqual(len(event["serviceSources"]), 2)

    def test_attached_and_queued_packets_visit_the_actual_guard_before_tracking(self):
        evidence = opened(CAPTURE)
        packets = [evidence.packet(ticket, None) for ticket in ("establish", *range(7))]
        self.assertEqual(sum(row["outputEthernetHex"] is not None for row in packets), 6)
        self.assertEqual([row["ticket"] for row in packets if not row["guardAdmitted"]], [5, 6])


class AttachmentContradictionTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix="netlib-attachment-contradiction-")
        self.addCleanup(self.temporary.cleanup)
        self.directory = Path(self.temporary.name) / "native"
        shutil.copytree(CAPTURE, self.directory)

    def read(self, name):
        return json.loads((self.directory / name).read_text())

    def write(self, name, value):
        (self.directory / name).write_text(json.dumps(value, indent=2) + "\n")

    def event(self, name):
        manifest = self.read("capture.json")
        return manifest, next(row for row in manifest["events"] if row["id"] == name)

    def export(self, reference, change):
        value = self.read(reference["file"])
        change(value)
        self.write(reference["file"], value)
        commands = self.read("commands.json")
        commands[reference["command"]]["stdout"] = (self.directory / reference["file"]).read_text()
        self.write("commands.json", commands)

    def rejected(self):
        with self.assertRaises((EvidenceError, ValueError, KeyError, TypeError, IndexError)):
            check_capture(self.directory)

    def guard_document(self, name, change):
        _, event = self.event(name)
        value = self.read(event["result"]["file"])
        change(value["nftables"])
        self.write(event["result"]["file"], value)

    def test_guard_namespace_identity_must_retain_the_actual_interface_inventory(self):
        _, event = self.event("install-primary-attachment")
        self.export(
            event["result"]["binding"]["sources"]["identity"],
            lambda value: value["interfaces"][1].update(ifindex=999),
        )
        self.rejected()

    def test_guard_link_readback_must_be_the_same_live_interface_instance(self):
        _, event = self.event("install-primary-attachment")
        self.export(
            event["result"]["binding"]["sources"]["links"],
            lambda rows: next(row for row in rows if row["ifname"] == "car").update(mtu=64),
        )
        self.rejected()

    def test_authentication_attachment_birth_must_join_the_actual_eap_port(self):
        manifest = self.read("capture.json")
        birth = manifest["namespaceLifetimes"]["auth"]
        birth["interfaces"]["auth0"]["ifindex"] = 999
        self.export(
            birth["identity"],
            lambda value: next(row for row in value["interfaces"] if row["name"] == "auth0").update(
                ifindex=999
            ),
        )
        self.write("capture.json", manifest)
        self.rejected()

    def test_guard_installation_uses_the_actual_numeric_input(self):
        def changed(rows):
            rule = next(
                row["rule"] for row in rows if row.get("rule", {}).get("comment") == "ORIGINAL"
            )
            rule["expr"][0]["match"]["right"] = "car"

        self.guard_document("install-primary-attachment", changed)
        self.rejected()

    def test_flush_cannot_hide_an_unrelated_stderr_error(self):
        _, event = self.event("reset-tracking")
        commands = self.read("commands.json")
        commands[event["result"]["commands"]["a"]]["stderr"] = "flush failed silently\n"
        self.write("commands.json", commands)
        self.rejected()

    def insert_unmodeled_command(self, name):
        manifest, event = self.event(name)
        commands = self.read("commands.json")
        position = event["commands"][-1] + 1
        end = commands[position - 1]["endNs"]
        inserted = {
            "arguments": ["true"],
            "startNs": end + 1,
            "endNs": end + 2,
            "returncode": 0,
            "stdout": "",
            "stderr": "",
        }

        def shift(value, key=None):
            if type(value) is int and key in {
                "command",
                "creationCommand",
                "moveCommand",
                "upCommand",
                "startCommand",
                "deleteCommand",
                "result",
                "commandIndex",
            }:
                return value + int(value >= position)
            if isinstance(value, list):
                if key in {"commands", "result"} and all(type(item) is int for item in value):
                    return [item + int(item >= position) for item in value]
                return [shift(item) for item in value]
            if isinstance(value, dict):
                if key in {"commands", "resynchronization"}:
                    return {item: index + int(index >= position) for item, index in value.items()}
                return {item: shift(content, item) for item, content in value.items()}
            return value

        manifest = shift(manifest)
        event = next(row for row in manifest["events"] if row["id"] == name)
        event["commands"].append(position)
        commands.insert(position, inserted)
        self.write("commands.json", commands)
        self.write("capture.json", manifest)
        for path in self.directory.glob("*-bindings.json"):
            self.write(path.name, shift(self.read(path.name)))

    def test_startup_cannot_hide_an_unmodeled_mutation_after_its_receipts(self):
        self.insert_unmodeled_command("start-replication")
        self.rejected()

    def test_guard_cannot_hide_an_unmodeled_mutation_after_its_installation(self):
        self.insert_unmodeled_command("install-primary-attachment")
        self.rejected()

    def test_protect_marker_cannot_hide_an_unmodeled_mutation_after_readiness(self):
        self.insert_unmodeled_command("protect-marker")
        self.rejected()

    def mutate_dump(self, reference, path, value, field=None):
        document = self.read(reference["file"])
        record = document["entries"][0]
        previous = record["raw"]
        raw = bytearray.fromhex(previous)

        def replace(start, end, selectors):
            while start < end:
                length, kind = struct.unpack_from("=HH", raw, start)
                if kind & 0x3FFF == selectors[0]:
                    if len(selectors) > 1:
                        return replace(start + 4, start + length, selectors[1:])
                    raw[start + 4 : start + length] = value.to_bytes(length - 4, "big")
                    return
                start += (length + 3) & ~3
            self.fail("Missing actual raw conntrack attribute")

        replace(20, len(raw), path)
        record["raw"] = raw.hex()
        if field:
            record[field] = value
        document["messages"] = [
            record["raw"] if text == previous else text for text in document["messages"]
        ]
        self.write(reference["file"], document)

    def test_wrong_ingress_reply_cannot_mark_the_connection_reply_seen(self):
        _, event = self.event("forged-reply-a")
        self.mutate_dump(event["after"]["conntrack"]["a"], [3], 442, "status")
        self.rejected()

    def test_wrong_ingress_original_cannot_mark_the_connection_assured(self):
        _, event = self.event("cached-original-b")
        self.mutate_dump(event["after"]["conntrack"]["b"], [3], 444, "status")
        self.rejected()

    def test_wrong_ingress_cannot_increment_original_accounting(self):
        _, event = self.event("cached-original-a")
        self.mutate_dump(event["after"]["conntrack"]["a"], [9, 1], 2)
        self.rejected()

    def test_wrong_ingress_reply_cannot_increment_reply_accounting(self):
        _, event = self.event("forged-reply-b")
        self.mutate_dump(event["after"]["conntrack"]["b"], [10, 2], 65)
        self.rejected()

    def test_early_drop_cannot_refresh_an_existing_short_timeout(self):
        _, event = self.event("cached-original-a")
        self.mutate_dump(event["after"]["conntrack"]["a"], [7], 30, "remainingTTL")
        self.rejected()

    def test_early_drop_cannot_replace_a_long_timeout_with_a_short_refresh(self):
        _, event = self.event("cached-original-b")
        self.mutate_dump(event["after"]["conntrack"]["b"], [7], 29, "remainingTTL")
        self.rejected()

    def test_both_queued_drops_preserve_assured_connection_accounting(self):
        _, event = self.event("serve-stale-pair")
        self.mutate_dump(event["after"]["conntrack"]["b"], [10, 1], 3)
        self.rejected()

    def test_early_drop_cannot_replace_the_native_connection_identity(self):
        _, event = self.event("cached-original-b")
        self.mutate_dump(event["after"]["conntrack"]["b"], [12], 12345, "id")
        self.rejected()

    def test_reset_must_empty_the_actual_full_table(self):
        _, event = self.event("reset-tracking")
        previous = self.read(event["before"]["conntrack"]["a"]["file"])
        self.write(event["result"]["tables"]["a"]["file"], previous)
        self.rejected()

    def test_protected_epoch_must_start_with_empty_actual_daemon_caches(self):
        _, event = self.event("protect-marker")
        reference = event["result"]["cacheReadiness"]["b"]["external"]
        manifest, stage = self.event("replicate")
        text = (self.directory / stage["result"]["external"]["file"]).read_text()
        (self.directory / reference["file"]).write_text(text)
        commands = self.read("commands.json")
        commands[reference["command"]]["stdout"] = text
        self.write("commands.json", commands)
        self.rejected()

    def test_guard_binding_cannot_substitute_an_unrelated_subject(self):
        _, event = self.event("install-primary-attachment")
        filename = event["result"]["binding"]["file"]
        value = self.read(filename)
        value["principal"] = "mallory@campus.example.test"
        self.write(filename, value)
        self.rejected()

    def test_guard_binding_cannot_change_its_application_scope(self):
        _, event = self.event("install-primary-attachment")
        filename = event["result"]["binding"]["file"]
        value = self.read(filename)
        value["scope"]["resource"] = "unrelated-service"
        self.write(filename, value)
        self.rejected()

    def test_explicit_guard_deny_cannot_claim_the_old_credential_prefix(self):
        _, event = self.event("install-standby-attachment-deny")
        filename = event["result"]["binding"]["file"]
        value = self.read(filename)
        value["currentAuthenticationEvent"] = "credential"
        self.write(filename, value)
        self.rejected()

    def test_guard_cannot_be_installed_after_conntrack(self):
        self.guard_document(
            "install-primary-attachment",
            lambda rows: next(row["chain"] for row in rows if "chain" in row).update(prio=-199),
        )
        self.rejected()

    def test_guard_cannot_use_name_identity_in_place_of_meta_iif(self):
        def changed(rows):
            rule = next(
                row["rule"] for row in rows if row.get("rule", {}).get("comment") == "ORIGINAL"
            )
            rule["expr"][0]["match"]["left"]["meta"]["key"] = "iifname"

        self.guard_document("install-primary-attachment", changed)
        self.rejected()

    def test_actual_guard_deny_cannot_leave_cached_tuple_allow_rules(self):
        _, event = self.event("install-standby-attachment-deny")
        active = self.read("install-standby-attachment-load.json")["nftables"]
        self.guard_document(
            "install-standby-attachment-deny",
            lambda rows: rows.__setitem__(slice(2, None), active[1:]),
        )
        self.rejected()

    def test_guard_cannot_omit_a_pre_nat_transport_selector(self):
        def changed(rows):
            rule = next(
                row["rule"] for row in rows if row.get("rule", {}).get("comment") == "ORIGINAL"
            )
            rule["expr"] = [
                expression
                for expression in rule["expr"]
                if expression.get("match", {}).get("left")
                != {"payload": {"protocol": "udp", "field": "sport"}}
            ]

        self.guard_document("install-primary-attachment", changed)
        self.rejected()

    def test_maintenance_socket_requires_actual_daemon_fd_ownership(self):
        _, event = self.event("start-replication")
        self.export(
            event["result"]["socketReadiness"]["a"],
            lambda value: value["sockets"][0]["owners"][0].update(pid=99999),
        )
        self.rejected()

    def test_maintenance_socket_cannot_move_to_another_namespace(self):
        _, event = self.event("start-replication")
        self.export(
            event["result"]["socketReadiness"]["a"],
            lambda value: value.update(namespace="net:[99999]"),
        )
        self.rejected()

    def test_maintenance_guard_cannot_guess_port_3780_as_the_sender(self):
        def changed(rows):
            rule = next(row["rule"] for row in rows if row.get("rule", {}).get("comment") == "SYNC")
            next(
                expression["match"]
                for expression in rule["expr"]
                if expression.get("match", {}).get("left")
                == {"payload": {"protocol": "udp", "field": "sport"}}
            )["right"] = 3780

        self.guard_document("install-primary-attachment", changed)
        self.rejected()

    def test_raw_packet_observer_cannot_claim_a_different_namespace(self):
        manifest = self.read("capture.json")
        observer = next(
            row
            for row in manifest["observers"]
            if row["actor"] == "attacker" and row["kind"] == "packet"
        )
        observer["identity"]["namespace"] = "net:[99999]"
        self.write("capture.json", manifest)
        self.rejected()

    def test_namespace_birth_cannot_alias_another_live_actor(self):
        manifest = self.read("capture.json")
        attacker = manifest["namespaceLifetimes"]["attacker"]
        other = self.read(manifest["namespaceLifetimes"]["a"]["identity"]["file"])["namespace"]
        self.export(attacker["identity"], lambda value: value.update(namespace=other))
        self.rejected()

    def test_boundary_cannot_reuse_an_earlier_kernel_dump(self):
        manifest, event = self.event("cached-original-b")
        event["after"]["conntrack"]["b"] = event["before"]["conntrack"]["b"]
        self.write("capture.json", manifest)
        self.rejected()

    def test_logoff_requires_the_actual_authenticator_event(self):
        _, event = self.event("logoff")
        commands = self.read("commands.json")
        commands[event["result"]["command"]]["arguments"][-1] = "status"
        self.write("commands.json", commands)
        self.rejected()

    def test_withdrawal_must_disable_the_adversary_link_too(self):
        _, event = self.event("withdraw-primary")
        reference = event["result"]["checks"]["links"]
        self.export(
            reference,
            lambda rows: next(row for row in rows if row["ifname"] == "aar").update(
                flags=["BROADCAST", "MULTICAST", "UP", "LOWER_UP"], operstate="UP"
            ),
        )
        self.rejected()

    def test_live_primary_reads_cannot_follow_retirement(self):
        manifest, event = self.event("continued-request")
        archive = next(row for row in manifest["events"] if row["id"] == "withdraw-primary")[
            "before"
        ]
        event["after"]["conntrack"]["a"] = archive["conntrack"]["a"]
        self.write("capture.json", manifest)
        self.rejected()

    def test_primary_archive_cannot_be_labelled_as_a_future_read(self):
        manifest, event = self.event("continued-request")
        event["after"]["archivedA"]["boundary"] = "continued-reply:after"
        self.write("capture.json", manifest)
        self.rejected()

    def test_socket_timeout_cannot_replace_the_actual_guard_drop(self):
        path = self.directory / "b-trace.txt"
        lines = path.read_text().splitlines()
        index = next(
            index
            for index in range(len(lines) - 1, -1, -1)
            if "netlib_attachment ingress" in lines[index] and "drop" in lines[index]
        )
        lines.pop(index)
        path.write_text("\n".join(lines) + "\n")
        self.rejected()

    def test_unsafe_matching_tuple_cannot_seed_protected_replication_before_bootstrap(self):
        evidence = opened(self.directory)
        frame = next(
            frame
            for frame in evidence.sync
            if any(message.get("attributes") for message in frame["messages"])
        )
        timestamp = evidence.events["protect-marker"]["endNs"] + 1_000_000
        for actor in ("a", "b"):
            path = self.directory / f"{actor}-frames.jsonl"
            rows = [json.loads(line) for line in path.read_text().splitlines()]
            for row in rows:
                if row.get("hex") == frame["hex"]:
                    row["timeNs"] = timestamp
            rows.sort(key=lambda row: row["timeNs"])
            path.write_text("".join(json.dumps(row) + "\n" for row in rows))
        self.rejected()

    def change_nflog_attribute(self, actor, prefix, attribute, change):
        path = self.directory / f"{actor}-nflog.jsonl"
        rows = [json.loads(line) for line in path.read_text().splitlines()]
        for row in rows:
            raw = bytearray.fromhex(row["hex"])
            if prefix.encode() + b"\0" not in raw:
                continue
            offset = 20
            while offset < len(raw):
                length, kind = struct.unpack_from("=HH", raw, offset)
                if kind == attribute:
                    previous = raw[offset + 4 : offset + length]
                    following = change(previous)
                    self.assertEqual(len(following), len(previous))
                    raw[offset + 4 : offset + length] = following
                    row["hex"] = raw.hex()
                    path.write_text("".join(json.dumps(value) + "\n" for value in rows))
                    return
                offset += (length + 3) & ~3
        self.fail("Missing actual NFLOG attribute")

    def test_nflog_input_index_cannot_be_replaced_by_the_claimed_data_port(self):
        self.change_nflog_attribute("a", "ATTACH_DROP", 4, lambda value: (2).to_bytes(4, "big"))
        self.rejected()

    def test_nflog_source_mac_cannot_replace_actual_ethernet_metadata(self):
        self.change_nflog_attribute(
            "a",
            "ATTACH_DROP",
            8,
            lambda value: value[:4] + bytes.fromhex("020000aabbcc") + value[10:],
        )
        self.rejected()

    def test_nflog_bytes_cannot_be_repaired_from_later_packet_copies(self):
        self.change_nflog_attribute(
            "a", "ATTACH_DROP", 9, lambda value: value[:-1] + bytes((value[-1] ^ 1,))
        )
        self.rejected()

    def test_missing_guard_log_cannot_be_excused_as_a_receive_timeout(self):
        path = self.directory / "b-nflog.jsonl"
        rows = [json.loads(line) for line in path.read_text().splitlines()]
        index = next(
            index for index, row in enumerate(rows) if b"ATTACH_DROP\0" in bytes.fromhex(row["hex"])
        )
        rows.pop(index)
        path.write_text("".join(json.dumps(row) + "\n" for row in rows))
        self.rejected()

    def test_authentication_cannot_be_spliced_after_current_credential_install(self):
        _, event = self.event("credential")
        path = self.directory / "eap/success-frames.jsonl"
        rows = [json.loads(line) for line in path.read_text().splitlines()]
        rows[15]["timeNs"] = event["endNs"] + 1
        path.write_text("".join(json.dumps(row) + "\n" for row in rows))
        self.rejected()

    def test_actual_eap_process_cannot_start_after_its_packet_evidence(self):
        manifest, event = self.event("authenticate")
        timestamp = event["result"]["endNs"] - 1
        manifest["eap"]["producers"]["authenticator"]["startNs"] = timestamp
        event["result"]["producers"]["authenticator"]["startNs"] = timestamp
        self.write("capture.json", manifest)
        self.rejected()

    def test_checked_certificate_journal_cannot_be_spliced_from_a_different_execution(self):
        commands = self.read("eap/commands.json")
        commands[-1]["stdout"] = "different certificate export\n"
        self.write("eap/commands.json", commands)
        self.rejected()

    def test_daemon_process_cannot_predate_its_fresh_namespace_and_start_command(self):
        _, event = self.event("start-replication")
        self.export(
            event["result"]["socketReadiness"]["a"],
            lambda value: value["processes"][0].update(startTimeTicks=1),
        )
        self.rejected()

    def test_two_simultaneously_live_daemons_cannot_alias_one_process_pid(self):
        _, event = self.event("start-replication")
        first = self.read(event["result"]["socketReadiness"]["a"]["file"])["processes"][0]

        def changed(value):
            value["processes"][0]["pid"] = first["pid"]
            for item in value["sockets"]:
                for owner in item["owners"]:
                    owner["pid"] = first["pid"]

        self.export(event["result"]["socketReadiness"]["b"], changed)
        self.rejected()

    def test_two_live_namespace_sockets_cannot_alias_one_owned_inode(self):
        _, event = self.event("start-replication")
        first = self.read(event["result"]["socketReadiness"]["a"]["file"])
        second = self.read(event["result"]["socketReadiness"]["b"]["file"])
        source = next(item["inode"] for item in first["sockets"] if item["local"]["port"] != 3780)
        previous = next(
            item["inode"] for item in second["sockets"] if item["local"]["port"] != 3780
        )

        def changed(value):
            for item in value["processes"][0]["fdSockets"]:
                if item["inode"] == previous:
                    item["inode"] = source
            for item in value["sockets"]:
                if item["inode"] == previous:
                    item["inode"] = source

        self.export(event["result"]["socketReadiness"]["b"], changed)
        _, guard = self.event("install-primary-attachment")
        filename = guard["result"]["binding"]["file"]
        binding = self.read(filename)
        binding["maintenanceSource"]["socketInode"] = source
        self.write(filename, binding)
        self.rejected()

    def test_simultaneously_live_observers_cannot_alias_one_process(self):
        manifest = self.read("capture.json")
        workers = [row for row in manifest["observers"] if row["kind"] == "packet"]
        workers[1]["identity"]["pid"] = workers[0]["identity"]["pid"]
        self.write("capture.json", manifest)
        self.rejected()

    def test_daemon_cannot_alias_a_still_live_packet_observer(self):
        manifest, event = self.event("start-replication")
        observer = next(
            row for row in manifest["observers"] if row["kind"] == "packet" and row["actor"] == "a"
        )

        def changed(value):
            value["processes"][0]["pid"] = observer["identity"]["pid"]
            for socket in value["sockets"]:
                for owner in socket["owners"]:
                    owner["pid"] = observer["identity"]["pid"]

        self.export(event["result"]["socketReadiness"]["a"], changed)
        self.rejected()

    def test_daemon_cannot_alias_the_still_live_eap_producer(self):
        manifest, event = self.event("start-replication")
        pid = manifest["eap"]["producers"]["authenticator"]["pid"]

        def changed(value):
            value["processes"][0]["pid"] = pid
            for socket in value["sockets"]:
                for owner in socket["owners"]:
                    owner["pid"] = pid

        self.export(event["result"]["socketReadiness"]["a"], changed)
        self.rejected()


if __name__ == "__main__":
    unittest.main()
