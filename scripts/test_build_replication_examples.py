"""Check source bindings in the native handoff projection."""

import json
import unittest
from unittest.mock import patch

import build_replication_examples as builder


class ReplicationProjectionTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.evidence, cls.replay = builder.build()
        cls.native = builder.DIRECTORY / "native"
        cls.capture = json.loads((cls.native / "capture.json").read_text())

    def test_route_version_matches_lean_schema(self):
        for routing in self.replay["routing"].values():
            self.assertEqual(routing["version"], "6.19.0")

    def test_empty_initial_tables_cannot_be_seeded(self):
        self.assertNotIn("initial", self.replay)
        self.assertEqual(self.evidence["initial"], {"a": [], "b": []})

    def test_control_and_packet_inventory(self):
        self.assertEqual(len(self.replay["events"]), 11)
        self.assertEqual(
            [row["type"] for row in self.replay["events"]],
            [
                "packet",
                "stage",
                "handoff",
                "handoff",
                "fence",
                "packet",
                "commit",
                "packet",
                "packet",
                "packet",
                "packet",
            ],
        )
        packets = [row for row in self.replay["events"] if row["type"] == "packet"]
        self.assertEqual(
            [row["observed"]["disposition"] for row in packets],
            [
                "forwarded",
                "routeDrop",
                "forwardDrop",
                "forwarded",
                "forwarded",
                "forwarded",
            ],
        )
        self.assertEqual(sum(row["observed"]["output"] is not None for row in packets), 4)

    def test_staging_uses_primary_and_received_cache_attributes(self):
        staged = self.replay["events"][1]
        source = self.evidence["events"][1]["before"]["a"][0]
        self.assertEqual(staged["key"], source["original"])
        self.assertEqual(staged["cache"][0]["sourceNAT"], {"address": "203.0.113.1", "port": 40000})
        self.assertEqual(
            staged["cache"][0]["destinationNAT"], {"address": "198.51.100.2", "port": 9000}
        )
        self.assertFalse(staged["cache"][0]["seenReply"])
        self.assertTrue(self.evidence["events"][1]["sourceSync"])
        self.assertTrue(
            all(row["cache"] is None for i, row in enumerate(self.replay["events"]) if i != 1)
        )

    def test_route_changes_and_fence_remain_separate(self):
        controls = self.replay["events"][2:5]
        self.assertEqual(controls[0]["leg"], "client")
        self.assertEqual(controls[1]["leg"], "server")
        self.assertEqual(controls[0]["gateway"], "standby")
        self.assertEqual(controls[1]["gateway"], "standby")
        self.assertEqual(controls[2]["gateway"], "primary")

    def test_kernel_observations_keep_actual_raw_dump(self):
        for source in self.evidence["projection"]["events"]:
            event = self.capture["events"][source["nativeEvent"]]
            projected = self.replay["events"][source["event"]]
            for actor, gateway in builder.GATEWAYS.items():
                path = self.native / event["after"]["conntrack"][actor]["file"]
                self.assertEqual(projected["states"][gateway], json.loads(path.read_text()))

    def test_policy_tables_retain_exact_objects_and_current_boundary(self):
        configs = {row["id"]: row for row in self.replay["configs"]}
        for projected in self.evidence["projection"]["tables"]:
            document = json.loads((self.native / projected["source"]).read_text())
            expected = [document["nftables"][i] for i in projected["objectIndices"]]
            self.assertEqual(
                configs[projected["config"]][projected["field"]], {"nftables": expected}
            )
            self.assertEqual(
                projected["source"],
                f"{projected['config']}-before-{'a' if projected['config'] == 'establish' else 'b'}-nftables.json",
            )
        self.assertEqual(
            [row["id"] for row in self.evidence["projection"]["omittedPolicyEvents"]],
            ["install-deny", "install-permit"],
        )

    def test_route_bindings_keep_gateway_and_direct_variants(self):
        bindings = self.replay["routing"]["standby"]["bindings"]
        self.assertIn({"device": "cbr", "nextNode": "client", "gateway": "192.0.3.2"}, bindings)
        self.assertIn({"device": "cbr", "nextNode": "client", "gateway": None}, bindings)
        self.assertEqual(len(bindings), 5)

    def test_gate_failure_stops_projection(self):
        with patch.object(builder, "check_capture", side_effect=ValueError("native mismatch")):
            with self.assertRaisesRegex(ValueError, "native mismatch"):
                builder.build()


if __name__ == "__main__":
    unittest.main()
