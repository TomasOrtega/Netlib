"""Reject contradictory authentication, packet, installation, and withdrawal evidence."""

import copy
import json
import os
import shutil
import tempfile
import unittest
from pathlib import Path

from check_campus_capture import ROOT, EvidenceError, check_capture

CAPTURE = Path(os.environ.get("NETLIB_CAMPUS_CAPTURE", ROOT / "examples/campus/native"))


class CampusCaptureTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.baseline = check_capture(CAPTURE)

    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix="netlib-campus-contradiction-")
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

    def test_shared_native_baseline(self):
        report = self.baseline
        self.assertEqual(
            (
                report["packetCount"],
                report["snapshotCount"],
                report["frameCount"],
                report["nflogCount"],
                report["syncFrameCount"],
            ),
            (8, 88, 28, 30, 26),
        )
        self.assertEqual(report["eapEvidence"]["frameCount"], 18)
        self.assertEqual(report["withdrawal"]["archiveBoundary"], "withdraw-primary:before")
        self.assertEqual(set(report["final"]), {"b"})

    def test_withdrawal_readback_cannot_change_interface_identity(self):
        _, event = self.event("withdraw-primary")
        ref = event["result"]["checks"]["links"]
        self.export(
            ref,
            lambda rows: next(row for row in rows if row["ifname"] == "syncl").update(
                ifindex=99999
            ),
        )
        self.rejected()

    def test_authenticator_lifetime_cannot_start_after_its_frames(self):
        manifest, event = self.event("authenticate")
        late = event["result"]["endNs"] - 1
        event["result"]["producers"]["authenticator"]["startNs"] = late
        manifest["eap"]["producers"]["authenticator"]["startNs"] = late
        self.write("capture.json", manifest)
        self.rejected()

    def test_observer_cannot_stop_before_withdrawal_service(self):
        manifest, event = self.event("continued-reply")
        manifest["eap"]["observer"]["stopNs"] = event["startNs"]
        self.write("capture.json", manifest)
        self.rejected()

    def test_authentication_frame_cannot_move_after_credential(self):
        _, event = self.event("credential")
        lines = [
            json.loads(line)
            for line in (self.directory / "eap/success-frames.jsonl").read_text().splitlines()
        ]
        lines[15]["timeNs"] = event["endNs"] + 1
        (self.directory / "eap/success-frames.jsonl").write_text(
            "".join(json.dumps(row) + "\n" for row in lines)
        )
        self.rejected()

    def test_authentication_requires_the_actual_client_namespace(self):
        manifest = self.read("capture.json")
        manifest["eap"]["supplicantCommand"][3] = "unrelated-peer"
        self.write("capture.json", manifest)
        self.rejected()

    def test_checked_method_cannot_name_the_outer_identity(self):
        path = self.directory / "eap/success-authenticator.jsonl"
        path.write_text(
            path.read_text().replace("alice@campus.example.test", "anonymous@campus.example.test")
        )
        self.rejected()

    def test_actual_logoff_command_cannot_be_a_status_query(self):
        _, event = self.event("logoff")
        commands = self.read("commands.json")
        commands[event["result"]["command"]]["arguments"][-1] = "status"
        self.write("commands.json", commands)
        self.rejected()

    def test_installed_credential_requires_the_checked_subject(self):
        manifest, event = self.event("credential")
        ref = event["result"]["installed"]
        self.export(
            ref, lambda credential: credential.update(subject="mallory@campus.example.test")
        )
        self.rejected()

    def test_policy_load_cannot_substitute_stale_permit(self):
        _, event = self.event("install-standby-deny")
        path = self.directory / event["result"]["file"]
        batch = json.loads(path.read_text())
        permit = self.read("input/permit.json")["nftables"]
        batch["nftables"] = [permit[0], batch["nftables"][1], *permit[1:]]
        path.write_text(json.dumps(batch))
        self.rejected()

    def test_native_deny_cannot_bypass_established_flows(self):
        _, event = self.event("install-standby-deny")
        ref = event["after"]["tables"]["b"]

        def changed(document):
            document["nftables"].append(
                {
                    "rule": {
                        "family": "ip",
                        "table": "netlib",
                        "chain": "forward",
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

        self.export(ref, changed)
        self.rejected()

    def test_live_primary_snapshot_cannot_be_supplied_after_withdrawal(self):
        manifest, event = self.event("continued-request")
        archive = next(row for row in manifest["events"] if row["id"] == "withdraw-primary")[
            "before"
        ]
        event["after"]["conntrack"]["a"] = copy.deepcopy(archive["conntrack"]["a"])
        self.write("capture.json", manifest)
        self.rejected()

    def test_archive_cannot_be_relabelled_as_a_future_boundary(self):
        manifest, event = self.event("continued-request")
        event["after"]["archivedA"]["boundary"] = "continued-reply:after"
        self.write("capture.json", manifest)
        self.rejected()

    def test_primary_forwarding_must_actually_be_disabled(self):
        _, event = self.event("withdraw-primary")
        ref = event["result"]["checks"]["forwarding"]
        (self.directory / ref["file"]).write_text("net.ipv4.ip_forward = 1\n")
        commands = self.read("commands.json")
        commands[ref["command"]]["stdout"] = "net.ipv4.ip_forward = 1\n"
        self.write("commands.json", commands)
        self.rejected()

    def test_primary_daemon_must_actually_be_absent(self):
        _, event = self.event("withdraw-primary")
        self.export(
            event["result"]["checks"]["daemon"],
            lambda value: value.update(matchingProcesses=[9999]),
        )
        self.rejected()

    def test_sync_loss_before_withdrawal_cannot_be_hidden(self):
        path = self.directory / "b-frames.jsonl"
        lines = [json.loads(line) for line in path.read_text().splitlines()]
        selected = next(
            i
            for i, row in enumerate(lines)
            if row.get("interface") == "syncr" and row.get("packetType") == 0
        )
        lines.pop(selected)
        path.write_text("".join(json.dumps(row) + "\n" for row in lines))
        self.rejected()

    def test_before_withdrawal_daemon_error_cannot_be_excused(self):
        _, event = self.event("withdraw-primary")
        ref = event["result"]["standbyLogBefore"]
        original = (self.directory / ref["file"]).read_text()
        changed = original + "[ERROR] no dedicated links available!\n"
        (self.directory / ref["file"]).write_text(changed)
        (self.directory / "b.log").write_text(
            changed + (self.directory / "b.log").read_text()[len(original) :]
        )
        commands = self.read("commands.json")
        commands[ref["command"]]["stdout"] = changed
        self.write("commands.json", commands)
        self.rejected()

    def test_socket_timeout_cannot_replace_actual_gateway_drop(self):
        path = self.directory / "b-trace.txt"
        lines = path.read_text().splitlines()
        selected = next(
            i for i in range(len(lines) - 1, -1, -1) if "netlib forward policy drop" in lines[i]
        )
        lines.pop(selected)
        path.write_text("\n".join(lines) + "\n")
        self.rejected()

    def test_endpoint_packet_bytes_cannot_be_repaired(self):
        path = self.directory / "client-nflog.jsonl"
        rows = [json.loads(line) for line in path.read_text().splitlines()]
        raw = bytearray.fromhex(rows[0]["hex"])
        raw[-1] ^= 1
        rows[0]["hex"] = raw.hex()
        path.write_text("".join(json.dumps(row) + "\n" for row in rows))
        self.rejected()

    def test_retirement_cannot_precede_its_verification_receipt(self):
        manifest, event = self.event("withdraw-primary")
        event["result"]["retiredAtNs"] = event["startNs"]
        self.write("capture.json", manifest)
        self.rejected()

    def test_boundary_cannot_alias_an_earlier_kernel_export(self):
        manifest, event = self.event("continued-reply")
        event["after"]["conntrack"]["b"] = event["before"]["conntrack"]["b"]
        self.write("capture.json", manifest)
        self.rejected()

    def test_certificate_generation_journal_cannot_be_omitted(self):
        self.write("eap/commands.json", [])
        self.rejected()

    def test_certificate_export_cannot_come_from_another_journal(self):
        commands = self.read("eap/commands.json")
        commands[-1]["stdout"] = "unrelated certificate export\n"
        self.write("eap/commands.json", commands)
        self.rejected()

    def authentication_exports(self, kind, change):
        manifest, logoff = self.event("logoff")
        for ref in (
            manifest["authenticationNetwork"]["auth"][kind],
            logoff["result"]["network"][kind],
        ):
            self.export(ref, change)

    def test_auth_namespace_cannot_shrink_its_mtu(self):
        for kind in ("links", "addresses"):
            self.authentication_exports(
                kind,
                lambda rows: next(row for row in rows if row["ifname"] == "auth0").update(mtu=64),
            )
        self.rejected()

    def test_auth_namespace_cannot_join_an_unobserved_bridge(self):
        for kind in ("links", "addresses"):
            self.authentication_exports(
                kind,
                lambda rows: next(row for row in rows if row["ifname"] == "auth0").update(
                    master="outside-bridge"
                ),
            )
        self.rejected()

    def test_auth_namespace_cannot_add_an_unobserved_address(self):
        self.authentication_exports(
            "addresses",
            lambda rows: rows.append(
                {
                    "ifname": "unobserved0",
                    "addr_info": [{"family": "inet", "local": "10.90.0.1", "prefixlen": 24}],
                }
            ),
        )
        self.rejected()

    def test_auth_namespace_cannot_add_policy_routing(self):
        self.authentication_exports(
            "rules", lambda rows: rows.append({"priority": 999, "src": "all", "table": "777"})
        )
        self.rejected()

    def test_unmodeled_forward_table_objects_cannot_be_discarded(self):
        _, event = self.event("install-standby-deny")
        ref = event["after"]["tables"]["b"]
        self.export(
            ref,
            lambda document: document["nftables"].append(
                {
                    "set": {
                        "family": "ip",
                        "table": "netlib",
                        "name": "unmodeled",
                        "type": "ipv4_addr",
                        "elem": [],
                    }
                }
            ),
        )
        self.rejected()

    def test_auth_namespace_peer_export_cannot_claim_different_routes(self):
        manifest = self.read("capture.json")
        self.export(manifest["authenticationNetwork"]["peer"]["routes"], lambda rows: rows.clear())
        self.rejected()


if __name__ == "__main__":
    unittest.main()
