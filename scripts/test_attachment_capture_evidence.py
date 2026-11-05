"""Check numeric ingress references and raw conntrack accounting contracts."""

import struct
import unittest

from attachment_capture_evidence import (
    EvidenceError,
    accounting,
    countdown_compatible,
    ifindex,
    namespace_inode,
    resolve_iif,
)
from check_attachment_capture import expected_guard


def attribute(kind, payload):
    size = len(payload) + 4
    return struct.pack("=HH", size, kind) + payload + bytes((-size) % 4)


class AttachmentReferenceTests(unittest.TestCase):
    def setUp(self):
        self.links = [{"ifindex": 1, "ifname": "lo"}, {"ifindex": 7, "ifname": "car"}]
        self.expression = {"match": {"op": "==", "left": {"meta": {"key": "iif"}}, "right": "car"}}

    def test_actual_iif_export_name_resolves_to_numeric_instance(self):
        self.assertEqual(resolve_iif(self.expression, self.links), 7)
        self.expression["match"]["right"] = 7
        self.assertEqual(resolve_iif(self.expression, self.links), 7)

    def test_iifname_does_not_establish_numeric_instance(self):
        self.expression["match"]["left"]["meta"]["key"] = "iifname"
        with self.assertRaises(EvidenceError):
            resolve_iif(self.expression, self.links)

    def test_numeric_reference_must_be_current_in_this_namespace(self):
        self.expression["match"]["right"] = 8
        with self.assertRaises(EvidenceError):
            resolve_iif(self.expression, self.links)

    def test_duplicate_native_indices_are_not_an_interface_binding(self):
        self.links.append({"ifindex": 7, "ifname": "reused"})
        with self.assertRaises(EvidenceError):
            resolve_iif(self.expression, self.links)

    def test_index_range_excludes_zero_boolean_and_overflow(self):
        for index in (0, -1, True, 2**31):
            with self.subTest(index=index), self.assertRaises(EvidenceError):
                ifindex(index)
        self.assertEqual(ifindex(2**31 - 1), 2**31 - 1)

    def test_namespace_inode_is_native_identity_not_name(self):
        self.assertEqual(namespace_inode("net:[4026532382]"), 4026532382)
        for value in ("a", "net:[0]", "net:[-1]", "net:[01]"):
            with self.subTest(value=value), self.assertRaises(EvidenceError):
                namespace_inode(value)


class AttachmentAccountingTests(unittest.TestCase):
    def raw(self, *, duplicate=False, missing=False):
        payload = attribute(1, (3).to_bytes(8, "big")) + attribute(5, b"")
        if not missing:
            payload += attribute(2, (192).to_bytes(8, "big"))
        if duplicate:
            payload += attribute(1, (9).to_bytes(8, "big"))
        return (bytes(20) + attribute(0x8009, payload) + attribute(0x800A, payload)).hex()

    def test_accounting_comes_from_both_nested_raw_directions(self):
        self.assertEqual(
            accounting(self.raw()),
            {"original": {"packets": 3, "bytes": 192}, "reply": {"packets": 3, "bytes": 192}},
        )

    def test_missing_and_duplicate_counts_are_rejected(self):
        for options in ({"duplicate": True}, {"missing": True}):
            with self.subTest(options=options), self.assertRaises(EvidenceError):
                accounting(self.raw(**options))

    def test_countdown_allows_elapsed_integer_quantization(self):
        countdown_compatible(
            29,
            28,
            {"startNs": 0, "endNs": 1000},
            {"startNs": 1_000_000_000, "endNs": 1_000_001_000},
        )

    def test_shorter_timeout_refresh_is_not_unchanged_expiry(self):
        with self.assertRaises(EvidenceError):
            countdown_compatible(
                179,
                29,
                {"startNs": 0, "endNs": 1000},
                {"startNs": 1_000_000_000, "endNs": 1_000_001_000},
            )

    def test_extended_timeout_is_not_ordinary_countdown(self):
        with self.assertRaises(EvidenceError):
            countdown_compatible(
                28,
                30,
                {"startNs": 0, "endNs": 1000},
                {"startNs": 1_000_000_000, "endNs": 1_000_001_000},
            )


class MaintenancePortTests(unittest.TestCase):
    def test_captured_ephemeral_port_remains_an_exact_maintenance_tuple(self):
        links = [
            {"ifname": "syncl", "ifindex": 7},
            {"ifname": "car", "ifindex": 3},
            {"ifname": "sar", "ifindex": 5},
        ]
        rules = expected_guard("a", links, True, 51350)
        self.assertEqual(rules[0]["header"]["sourcePort"], 51350)
        self.assertEqual(rules[0]["header"]["destinationPort"], 3780)
        self.assertEqual(rules[0]["ifindex"], 7)
        self.assertEqual([rule["header"]["destinationPort"] for rule in rules[1:-1]], [8080, 40000])


if __name__ == "__main__":
    unittest.main()
