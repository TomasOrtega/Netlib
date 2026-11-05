"""Check the passive -450 importer without treating fixtures as a native run."""

import copy
import unittest

from capture_evidence import EvidenceError
from check_fragment_attachment_capture import (
    CHAIN,
    TABLE,
    canonical_fragment_guard,
    compare_current,
    installed_allows,
    maintenance_separated,
)

LINKS = [
    {"ifname": "car", "ifindex": 7},
    {"ifname": "sar", "ifindex": 8},
    {"ifname": "syncl", "ifindex": 9},
]
ORIGINAL = {"source": "192.0.2.2", "destination": "203.0.113.2", "protocol": 17}
REPLY = {"source": "198.51.100.2", "destination": "203.0.113.1", "protocol": 17}
SYNC = {"source": "10.10.0.2", "destination": "10.10.0.1", "protocol": 17}


def guard_document(*, exported=False):
    def rule(role, index=None, envelope=None):
        expressions = []
        if index is not None:
            selected = (
                next(row["ifname"] for row in LINKS if row["ifindex"] == index)
                if exported
                else index
            )
            expressions.append(
                {"match": {"op": "==", "left": {"meta": {"key": "iif"}}, "right": selected}}
            )
            for field, key in (
                ("saddr", "source"),
                ("daddr", "destination"),
                ("protocol", "protocol"),
            ):
                expressions.append(
                    {
                        "match": {
                            "op": "==",
                            "left": {"payload": {"protocol": "ip", "field": field}},
                            "right": envelope[key],
                        }
                    }
                )
        if role != "SYNC":
            expressions.append(
                {
                    "log": {
                        "prefix": "FRAG_DROP" if role == "FALLBACK" else "FRAG_ALLOW",
                        "group": 42,
                        "snaplen": 65531,
                        "queue-threshold": 1,
                    }
                }
            )
        expressions.append({"drop" if role == "FALLBACK" else "accept": None})
        return {
            "rule": {
                "family": "ip",
                "table": TABLE,
                "chain": CHAIN,
                "comment": role,
                "expr": expressions,
            }
        }

    return {
        "nftables": [
            {
                "metainfo": {"version": "1.1.3", "json_schema_version": 1}
                if exported
                else {"json_schema_version": 1}
            },
            {"table": {"family": "ip", "name": TABLE}},
            {
                "chain": {
                    "family": "ip",
                    "table": TABLE,
                    "name": CHAIN,
                    "type": "filter",
                    "hook": "prerouting",
                    "prio": -450,
                    "policy": "drop",
                }
            },
            rule("SYNC", 9, SYNC),
            rule("ORIGINAL", 7, ORIGINAL),
            rule("REPLY", 8, REPLY),
            rule("FALLBACK"),
        ]
    }


class EarlyGuardTests(unittest.TestCase):
    def test_numeric_install_and_actual_export_name_mean_the_same_current_index(self):
        actual = canonical_fragment_guard(guard_document(exported=True), LINKS)
        transaction = canonical_fragment_guard(guard_document(), LINKS, transaction=True)
        self.assertEqual(actual, transaction)
        self.assertTrue(installed_allows(actual, 7, ORIGINAL))
        self.assertFalse(installed_allows(actual, 12, ORIGINAL))

    def test_allow_does_not_read_a_udp_selector_from_a_noninitial_fragment(self):
        rules = canonical_fragment_guard(guard_document(), LINKS, transaction=True)
        self.assertTrue(
            installed_allows(
                rules, 7, {**ORIGINAL, "offsetBytes": 16, "payloadHex": "0000000000000000"}
            )
        )

    def test_actual_protocol_name_export_keeps_ipv4_protocol_semantics(self):
        document = guard_document(exported=True)
        for row in document["nftables"]:
            for expression in row.get("rule", {}).get("expr", []):
                match = expression.get("match", {})
                if match.get("left") == {"payload": {"protocol": "ip", "field": "protocol"}}:
                    match["right"] = "udp"
        self.assertEqual(
            canonical_fragment_guard(document, LINKS),
            canonical_fragment_guard(guard_document(), LINKS, transaction=True),
        )

    def test_stale_installed_allow_is_computed_and_reported_as_a_mismatch(self):
        rules = canonical_fragment_guard(guard_document(), LINKS, transaction=True)
        self.assertEqual(
            compare_current(rules, 7, ORIGINAL, False),
            {"actualAllowed": True, "expectedAllowed": False, "mismatch": True},
        )

    def test_reused_numeric_index_still_matches_the_installed_rule(self):
        rules = canonical_fragment_guard(guard_document(), LINKS, transaction=True)
        replacement = {"ns": {"id": 10, "birth": 20}, "ifindex": 7, "birth": 999}
        self.assertTrue(
            compare_current(rules, replacement["ifindex"], ORIGINAL, False)["actualAllowed"]
        )

    def test_name_based_iif_is_rejected(self):
        document = guard_document()
        document["nftables"][4]["rule"]["expr"][0]["match"]["left"]["meta"]["key"] = "iifname"
        with self.assertRaises(EvidenceError):
            canonical_fragment_guard(document, LINKS, transaction=True)

    def test_installation_requires_captured_numeric_rhs(self):
        with self.assertRaises(EvidenceError):
            canonical_fragment_guard(guard_document(exported=True), LINKS, transaction=True)

    def test_fine_guard_priority_cannot_claim_to_prevent_reassembly_effects(self):
        document = guard_document()
        document["nftables"][2]["chain"]["prio"] = -300
        with self.assertRaises(EvidenceError):
            canonical_fragment_guard(document, LINKS, transaction=True)

    def test_udp_sport_dport_and_meta_l4proto_are_rejected_at_this_hook(self):
        for left in (
            {"payload": {"protocol": "udp", "field": "sport"}},
            {"payload": {"protocol": "udp", "field": "dport"}},
            {"meta": {"key": "l4proto"}},
        ):
            document = guard_document()
            document["nftables"][4]["rule"]["expr"].insert(
                1, {"match": {"op": "==", "left": left, "right": 17}}
            )
            with self.subTest(left=left), self.assertRaises(EvidenceError):
                canonical_fragment_guard(document, LINKS, transaction=True)

    def test_missing_coarse_protocol_or_address_is_rejected(self):
        for index in (1, 2, 3):
            document = guard_document()
            document["nftables"][4]["rule"]["expr"].pop(index)
            with self.subTest(index=index), self.assertRaises(EvidenceError):
                canonical_fragment_guard(document, LINKS, transaction=True)

    def test_log_label_cannot_disagree_with_actual_verdict(self):
        document = guard_document()
        document["nftables"][4]["rule"]["expr"][-2]["log"]["prefix"] = "FRAG_DROP"
        with self.assertRaises(EvidenceError):
            canonical_fragment_guard(document, LINKS, transaction=True)

    def test_fallback_cannot_accept_or_skip_the_early_drop_observation(self):
        for change in ("accept", "log"):
            document = guard_document()
            rule = document["nftables"][-1]["rule"]
            if change == "accept":
                rule["expr"][-1] = {"accept": None}
            else:
                rule["expr"].pop(0)
            with self.subTest(change=change), self.assertRaises(EvidenceError):
                canonical_fragment_guard(document, LINKS, transaction=True)

    def test_unmodeled_flowtable_or_side_effect_is_rejected(self):
        document = guard_document()
        document["nftables"].append(
            {"flowtable": {"family": "ip", "table": TABLE, "name": "bypass"}}
        )
        with self.assertRaises(EvidenceError):
            canonical_fragment_guard(document, LINKS, transaction=True)

    def test_maintenance_separation_is_checked_after_port_erasure(self):
        rules = canonical_fragment_guard(guard_document(), LINKS, transaction=True)
        self.assertTrue(maintenance_separated(rules, [ORIGINAL, REPLY]))
        overlapping = copy.deepcopy(rules)
        overlapping[0]["envelope"] = ORIGINAL
        with self.assertRaises(EvidenceError):
            maintenance_separated(overlapping, [ORIGINAL, REPLY])

    def test_replacement_requires_actual_explicit_table_deletion(self):
        document = guard_document()
        with self.assertRaises(EvidenceError):
            canonical_fragment_guard(document, LINKS, transaction=True, replace=True)
        document["nftables"].insert(1, {"delete": {"table": {"family": "ip", "name": TABLE}}})
        self.assertTrue(canonical_fragment_guard(document, LINKS, transaction=True, replace=True))

    def test_replacement_cannot_delete_the_new_guard_after_creating_it(self):
        document = guard_document()
        document["nftables"].append({"delete": {"table": {"family": "ip", "name": TABLE}}})
        with self.assertRaises(EvidenceError):
            canonical_fragment_guard(document, LINKS, transaction=True, replace=True)

    def test_transaction_must_create_the_table_before_its_chain(self):
        document = guard_document()
        document["nftables"][1:3] = document["nftables"][1:3][::-1]
        with self.assertRaises(EvidenceError):
            canonical_fragment_guard(document, LINKS, transaction=True)

    def test_transaction_schema_version_requires_an_exact_integer(self):
        for value in (True, 1.0):
            document = guard_document()
            document["nftables"][0]["metainfo"]["json_schema_version"] = value
            with self.subTest(value=value), self.assertRaises(EvidenceError):
                canonical_fragment_guard(document, LINKS, transaction=True)

    def test_log_numeric_metadata_requires_exact_integers(self):
        for field, value in (
            ("queue-threshold", True),
            ("queue-threshold", 1.0),
            ("group", 42.0),
            ("snaplen", 65531.0),
        ):
            document = guard_document()
            document["nftables"][4]["rule"]["expr"][-2]["log"][field] = value
            with self.subTest(field=field, value=value), self.assertRaises(EvidenceError):
                canonical_fragment_guard(document, LINKS, transaction=True)


if __name__ == "__main__":
    unittest.main()
