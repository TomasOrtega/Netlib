"""Native EAP evidence and contradiction regressions."""

import copy
import json
import shutil
import tempfile
import unittest
from pathlib import Path

import check_eap_capture as check

CAPTURE = Path(__file__).resolve().parents[1] / "examples/eap/native"


class CaptureTests(unittest.TestCase):
    def reject_change(self, filename, change, pattern=".", lines=False):
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

    def reject_log(self, filename, marker):
        self.reject_change(
            filename,
            lambda rows: rows.__setitem__(
                slice(None), [row for row in rows if marker not in row["line"]]
            ),
            lines=True,
        )

    def test_native_capture(self):
        report = check.check_capture(CAPTURE)
        self.assertEqual(report["frameCount"], 32)
        self.assertEqual([phase["terminalIdentifier"] for phase in report["phases"]], [7, 6])
        self.assertEqual(
            [phase["methodEvidence"]["accepted"] for phase in report["phases"]], [True, False]
        )
        self.assertEqual(
            report["phases"][0]["logicalAuthorization"],
            {"beforeLogoff": True, "afterLogoff": False},
        )

    def test_success_without_method_evidence_rejected(self):
        for filename, marker in (
            ("success-authenticator.jsonl", "EAP-TLS: CONTINUE -> SUCCESS"),
            ("success-authenticator.jsonl", "preverify_ok=1 err=0 (ok) ca_cert_verify=1 depth=0"),
            ("success-authenticator.jsonl", "Client acknowledged final TLS handshake message"),
            ("success-supplicant.jsonl", "ACKing protected success indication"),
            ("success-supplicant.jsonl", "OCSP response verification succeeded"),
        ):
            with self.subTest(marker=marker):
                self.reject_log(filename, marker)

    def test_negotiated_tls_version_contradictions_rejected(self):
        for phase in ("success", "bad-server"):
            for role in ("authenticator", "supplicant"):

                def mutate(rows):
                    for row in rows:
                        row["line"] = row["line"].replace(
                            "SSL: Using TLS version TLSv1.3", "SSL: Using TLS version TLSv1.2"
                        )

                with self.subTest(phase=phase, role=role):
                    self.reject_change(f"{phase}-{role}.jsonl", mutate, "TLS version", lines=True)

    def test_protected_success_byte_contradictions_rejected(self):
        for role, action in (("authenticator", "Send"), ("supplicant", "ACKing")):

            def mutate(rows):
                for row in rows:
                    if row["line"].startswith(f"EAP-TLS: {action} protected success indication"):
                        row["line"] = row["line"].replace("0x00", "0x01")

            with self.subTest(role=role):
                self.reject_change(f"success-{role}.jsonl", mutate, "protected success", lines=True)

    def test_conflicting_repeated_tls_version_marker_rejected(self):
        for role in ("authenticator", "supplicant"):

            def mutate(rows):
                row = next(row for row in rows if row["line"] == "SSL: Using TLS version TLSv1.3")
                row["line"] = "SSL: Using TLS version TLSv1.2"

            with self.subTest(role=role):
                self.reject_change(f"success-{role}.jsonl", mutate, "TLS version", lines=True)

    def test_missing_authenticator_protected_success_send_rejected(self):
        self.reject_log("success-authenticator.jsonl", "EAP-TLS: Send protected success indication")

    def test_protected_success_send_after_terminal_result_rejected(self):
        def mutate(rows):
            send = rows.pop(
                next(
                    index
                    for index, row in enumerate(rows)
                    if row["line"].startswith("EAP-TLS: Send protected success indication")
                )
            )
            index = (
                next(
                    index
                    for index, row in enumerate(rows)
                    if "CTRL-EVENT-EAP-SUCCESS" in row["line"]
                )
                + 1
            )
            send["timeNs"] = (rows[index - 1]["timeNs"] + rows[index]["timeNs"]) // 2
            rows.insert(index, send)

        self.reject_change("success-authenticator.jsonl", mutate, "method result order", lines=True)

    def test_duplicate_or_conflicting_protected_success_marker_rejected(self):
        for role, action in (("authenticator", "Send"), ("supplicant", "ACKing")):
            for byte in ("0x00", "0x01"):

                def mutate(rows):
                    index = next(
                        index
                        for index, row in enumerate(rows)
                        if row["line"].startswith(f"EAP-TLS: {action} protected success indication")
                    )
                    extra = copy.deepcopy(rows[index])
                    extra["timeNs"] = (rows[index]["timeNs"] + rows[index + 1]["timeNs"]) // 2
                    extra["line"] = extra["line"].replace("0x00", byte)
                    rows.insert(index + 1, extra)

                with self.subTest(role=role, byte=byte):
                    self.reject_change(
                        f"success-{role}.jsonl", mutate, "protected success", lines=True
                    )

    def test_bad_certificate_rejection_requires_native_failure(self):
        self.reject_log("bad-server-supplicant.jsonl", "CTRL-EVENT-EAP-TLS-CERT-ERROR")
        self.reject_log("bad-server-authenticator.jsonl", "CTRL-EVENT-EAP-FAILURE")

    def test_wrong_terminal_identifier_rejected_independently_of_log_bytes(self):
        rows = [
            json.loads(line) for line in (CAPTURE / "success-frames.jsonl").read_text().splitlines()
        ]
        frames = [check.decode_frame(row) for row in rows]
        frames[15]["eap"]["identifier"] = 8
        with self.assertRaisesRegex(check.EvidenceError, "Terminal identifier"):
            check.check_sequence(frames, True)

    def test_wrong_response_identifier_rejected(self):
        rows = [
            json.loads(line) for line in (CAPTURE / "success-frames.jsonl").read_text().splitlines()
        ]
        frames = [check.decode_frame(row) for row in rows]
        frames[4]["eap"]["identifier"] = 9
        with self.assertRaisesRegex(check.EvidenceError, "outstanding Request"):
            check.check_sequence(frames, True)

    def test_stale_or_misbound_method_window_rejected(self):
        self.reject_change(
            "success-authenticator.jsonl",
            lambda rows: rows[461].update(timeNs=0),
            "stale",
            lines=True,
        )
        self.reject_change(
            "observations.json", lambda document: document["phases"][0].update(phaseId=2), "phase"
        )
        self.reject_change(
            "observations.json", lambda document: document.update(subject=check.OUTER), "subject"
        )
        self.reject_change(
            "observations.json", lambda document: document.update(method=1), "method"
        )

    def test_method_result_after_native_authorization_rejected(self):
        def mutate(rows):
            method = rows.pop(
                next(
                    index
                    for index, row in enumerate(rows)
                    if row["line"] == "EAP-TLS: CONTINUE -> SUCCESS"
                )
            )
            index = (
                next(index for index, row in enumerate(rows) if "AP-STA-CONNECTED" in row["line"])
                + 1
            )
            method["timeNs"] = (rows[index - 1]["timeNs"] + rows[index]["timeNs"]) // 2
            rows.insert(index, method)

        self.reject_change("success-authenticator.jsonl", mutate, "method result order", lines=True)

    def test_wrong_link_role_or_peer_rejected(self):
        for offset in (0, 6):

            def mutate(rows):
                frame = bytearray.fromhex(rows[1]["hex"])
                frame[offset] ^= 2
                rows[1]["hex"] = frame.hex()

            self.reject_change("success-frames.jsonl", mutate, "MAC|role", lines=True)
        self.reject_change(
            "success-frames.jsonl",
            lambda rows: rows[1].update(packetType=2),
            "direction",
            lines=True,
        )

    def test_malformed_lengths_rejected(self):
        for offset in (16, 20):

            def mutate(rows):
                frame = bytearray.fromhex(rows[1]["hex"])
                frame[offset : offset + 2] = b"\xff\xff"
                rows[1]["hex"] = frame.hex()

            self.reject_change("success-frames.jsonl", mutate, "length", lines=True)

    def test_native_byte_payload_contradiction_rejected(self):
        def mutate(rows):
            frame = bytearray.fromhex(rows[4]["hex"])
            frame[-1] ^= 1
            rows[4]["hex"] = frame.hex()

        self.reject_change("success-frames.jsonl", mutate, "native EAPOL hexdumps", lines=True)

    def test_duplicate_extra_or_missing_event_rejected(self):
        def duplicate(rows):
            extra = copy.deepcopy(rows[4])
            extra["timeNs"] = (rows[4]["timeNs"] + rows[5]["timeNs"]) // 2
            rows.insert(5, extra)

        self.reject_change("success-frames.jsonl", duplicate, "native EAPOL hexdumps", lines=True)
        self.reject_change("success-frames.jsonl", lambda rows: rows.pop(16), lines=True)
        self.reject_change(
            "success-authenticator.jsonl",
            lambda rows: rows.append(
                {
                    "timeNs": rows[-1]["timeNs"] + 1,
                    "line": "auth0: CTRL-EVENT-EAP-SUCCESS " + check.PEER,
                }
            ),
            "duplicate",
            lines=True,
        )

    def test_untrusted_identity_is_distinct_from_certificate_principal(self):
        report = check.check_capture(CAPTURE)
        identity = report["phases"][0]["frames"][2]["eap"]
        self.assertEqual(bytes.fromhex(identity["dataHex"]).decode(), check.OUTER)
        self.assertNotEqual(check.OUTER, report["phases"][0]["methodEvidence"]["subject"])

    def test_valid_eap_and_ethernet_padding_is_not_method_data(self):
        row = {
            "timeNs": 1,
            "packetType": 4,
            "hex": "02000000ea0202000000ea01888e0200000603070004aabbccdd",
        }
        frame = check.decode_frame(row)
        self.assertEqual(frame["eap"]["paddingHex"], "aabb")
        self.assertEqual(frame["eapol"]["paddingHex"], "ccdd")
        self.assertEqual(frame["eap"]["dataHex"], "")

    def test_truncated_tls_fragment_flight_rejected(self):
        rows = [
            json.loads(line) for line in (CAPTURE / "success-frames.jsonl").read_text().splitlines()
        ]
        frames = [check.decode_frame(row) for row in rows]
        original = frames[4]["eap"]["dataHex"]
        frames[4]["eap"]["dataHex"] = original[:2] + "ffffffff" + original[10:]
        with self.assertRaisesRegex(check.EvidenceError, "TLS fragment"):
            check.check_tls_fragments(frames)

    def test_nonempty_tls_fragment_ack_rejected(self):
        rows = [
            json.loads(line) for line in (CAPTURE / "success-frames.jsonl").read_text().splitlines()
        ]
        frames = [check.decode_frame(row) for row in rows]
        frames[5]["eap"]["dataHex"] = "00160303000102"
        with self.assertRaisesRegex(check.EvidenceError, "fragment ACK"):
            check.check_tls_fragments(frames)

    def test_booleans_do_not_replace_integer_fields(self):
        self.reject_change(
            "observations.json", lambda document: document.update(schema=True), "schema"
        )
        self.reject_change(
            "observations.json",
            lambda document: document["phases"][0].update(phaseId=True),
            "phase",
        )


if __name__ == "__main__":
    unittest.main()
