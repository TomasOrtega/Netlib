"""Independent admission evidence and contradiction regressions."""

import copy
import json
import shutil
import tempfile
import unittest
from pathlib import Path

import check_admission_capture as check

CAPTURE = Path(__file__).resolve().parents[1] / "examples/admission/native"


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

    def test_native_capture(self):
        evidence = check.check_capture(CAPTURE)
        self.assertEqual((evidence["frameCount"], evidence["eapFrameCount"]), (7, 18))
        self.assertEqual(
            [stage["delivered"] for stage in evidence["stages"]], [False, False, True, False]
        )
        self.assertEqual(
            [stage["eapFramesBeforeSend"] for stage in evidence["stages"]], [0, 16, 16, 18]
        )
        self.assertEqual(
            evidence["stages"][2]["cachedRow"]["id"], evidence["stages"][3]["cachedRow"]["id"]
        )
        self.assertTrue(evidence["stages"][3]["credentialInstalled"])

    def test_false_socket_delivery_rejected(self):
        self.reject(
            "observations.json",
            lambda document: document["stages"][0]["server"].update(
                result=document["stages"][0]["sent"]["result"]
            ),
            "socket result",
        )

    def test_missing_reply_or_changed_port_rejected(self):
        self.reject(
            "observations.json",
            lambda document: document["stages"][2]["client"].update(result=None),
            "socket result",
        )
        self.reject(
            "observations.json",
            lambda document: document["stages"][3]["sent"]["result"].update(sourcePort=41001),
            "socket result",
        )

    def test_timeout_without_measured_wait_rejected(self):
        self.reject(
            "observations.json",
            lambda document: document["stages"][3]["server"].update(
                endNs=document["stages"][3]["server"]["startNs"] + 1
            ),
            "timeout",
        )

    def test_missing_or_extra_raw_packet_rejected(self):
        self.reject("data-frames.jsonl", lambda rows: rows.pop(3), "packet count", lines=True)

        def duplicate(rows):
            row = copy.deepcopy(rows[-1])
            row["timeNs"] += 1000
            rows.append(row)

        self.reject("data-frames.jsonl", duplicate, "packet count|Extra raw", lines=True)

    def test_wrong_raw_mac_or_payload_rejected(self):
        def mac(rows):
            frame = bytearray.fromhex(rows[0]["hex"])
            frame[6] ^= 2
            rows[0]["hex"] = frame.hex()

        def payload(rows):
            frame = bytearray.fromhex(rows[2]["hex"])
            frame[-1] ^= 1
            rows[2]["hex"] = frame.hex()

        self.reject("data-frames.jsonl", mac, "MAC role", lines=True)
        self.reject("data-frames.jsonl", payload, "payload", lines=True)

    def test_malformed_ip_or_udp_length_rejected(self):
        for offset in (16, 38):

            def change(rows):
                frame = bytearray.fromhex(rows[0]["hex"])
                frame[offset : offset + 2] = b"\xff\xff"
                rows[0]["hex"] = frame.hex()

            self.reject("data-frames.jsonl", change, "length|checksum", lines=True)

    def test_missing_reply_firewall_rule_rejected(self):
        self.reject(
            "credential-permitted-firewall.json",
            lambda document: document["nftables"].pop(),
            "generated policy",
        )

    def test_established_bypass_rejected(self):
        def change(document):
            document["nftables"].append(
                {
                    "rule": {
                        "family": "ip",
                        "table": "netlib",
                        "chain": "forward",
                        "handle": 100,
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

        self.reject("logged-off-cached-firewall.json", change, "conntrack bypass")

    def test_hidden_hook_or_tracking_verdict_rejected(self):
        self.reject(
            "logged-off-cached-ruleset.json",
            lambda document: document["nftables"].append(
                {"table": {"family": "ip", "name": "hidden"}}
            ),
            "extra native",
        )

        def change(document):
            rule = next(
                item["rule"]
                for item in document["nftables"]
                if "rule" in item and item["rule"]["table"] == "netlib_tracking"
            )
            rule["expr"].append({"accept": None})

        self.reject("logged-off-cached-ruleset.json", change, "tracking rule")

    def test_tracking_counter_contradiction_rejected(self):
        def change(document):
            rule = next(
                item["rule"]
                for item in document["nftables"]
                if "rule" in item and item["rule"]["table"] == "netlib_tracking"
            )
            rule["expr"][1]["counter"]["packets"] += 1

        self.reject("logged-off-cached-ruleset.json", change, "counters")

    def test_cached_row_raw_or_identity_contradiction_rejected(self):
        self.reject(
            "logged-off-cached-conntrack.json",
            lambda document: document["entries"][0].update(status=8),
            "raw evidence",
        )

        def replace_id(document):
            entry = document["entries"][0]
            old_raw = entry["raw"]
            before = entry["id"].to_bytes(4, "big").hex()
            after = (entry["id"] + 1).to_bytes(4, "big").hex()
            self.assertEqual(old_raw.count(before), 1)
            entry["raw"] = old_raw.replace(before, after)
            entry["id"] += 1
            document["messages"] = [
                entry["raw"] if raw == old_raw else raw for raw in document["messages"]
            ]

        self.reject("logged-off-cached-conntrack.json", replace_id, "same cached flow")

    def test_policy_load_and_credential_order_rejected(self):
        self.reject(
            "observations.json",
            lambda document: document["stages"][2]["load"].update(
                endNs=document["stages"][2]["sent"]["startNs"] + 1
            ),
            "load is late",
        )
        self.reject(
            "observations.json",
            lambda document: document["credentialInstall"].update(
                endNs=document["stages"][2]["load"]["startNs"] + 1
            ),
            "cutover order",
        )

    def test_installed_credential_and_immutable_policy_rejected(self):
        self.reject(
            "installed-demo-credential.json",
            lambda document: document.update(subject="mallory"),
            "Installed local",
        )
        self.reject("input/permit.json", lambda document: document["nftables"].pop(), "Immutable")
        self.reject(
            "credential-permitted-load.json",
            lambda document: document["nftables"].pop(),
            "Applied transaction",
        )

    def test_eap_success_without_native_tls_completion_rejected(self):
        self.reject(
            "eap/success-authenticator.jsonl",
            lambda rows: rows.__setitem__(
                slice(None), [row for row in rows if row["line"] != "EAP-TLS: CONTINUE -> SUCCESS"]
            ),
            "method observation",
            lines=True,
        )

    def test_late_native_method_evidence_rejected(self):
        with tempfile.TemporaryDirectory() as temporary:
            directory = Path(temporary) / "native"
            shutil.copytree(CAPTURE, directory)
            observations = json.loads((directory / "observations.json").read_text())
            lower = observations["stages"][1]["endNs"] + 1
            upper = observations["eap"]["endNs"] - 1
            for role in ("authenticator", "supplicant"):
                path = directory / "eap" / f"success-{role}.jsonl"
                rows = [json.loads(line) for line in path.read_text().splitlines()]
                for index, row in enumerate(rows):
                    row["timeNs"] = lower + (upper - lower) * (index + 1) // (len(rows) + 1)
                path.write_text("".join(json.dumps(row) + "\n" for row in rows))
            with self.assertRaisesRegex(check.EvidenceError, "method evidence.*checkpoint"):
                check.check_capture(directory)

    def test_native_export_stdout_contradiction_rejected(self):
        def change(commands):
            records = [
                record
                for record in commands
                if record["command"]
                == ["ip", "netns", "exec", "auth", "nft", "-j", "-nn", "list", "ruleset"]
            ]
            document = json.loads(records[2]["stdout"])
            document["nftables"].append(
                {
                    "rule": {
                        "family": "ip",
                        "table": "netlib",
                        "chain": "forward",
                        "handle": 999,
                        "expr": [{"accept": None}],
                    }
                }
            )
            records[2]["stdout"] = json.dumps(document)

        self.reject("commands.json", change, "export.*stdout")

    def test_native_route_and_link_contradictions_rejected(self):
        self.reject("auth-routes.json", lambda rows: rows[1].update(dev="auth0"), "route")
        self.reject(
            "auth-links.json", lambda rows: rows[2].update(address=check.eap.PEER), "link|MAC"
        )


if __name__ == "__main__":
    unittest.main()
