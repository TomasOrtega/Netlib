"""Check early-source and current-configuration bindings in safe handoff projection."""

import json
import unittest
from unittest.mock import patch

import build_safe_handoff_examples as builder


class SafeHandoffProjectionTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.evidence, cls.replay = builder.build()
        cls.native = builder.DIRECTORY / "native"

    def test_initial_configuration_and_empty_state_interface(self):
        self.assertEqual(
            self.replay["initialConfigs"],
            {"primary": "initial-primary", "standby": "initial-standby"},
        )
        self.assertNotIn("initial", self.replay)
        self.assertEqual(self.evidence["initial"], {"a": [], "b": []})
        self.assertTrue(all(row["version"] == "6.19.0" for row in self.replay["routing"].values()))

    def test_source_bootstrap_then_install_before_handoff(self):
        kinds = [row["type"] for row in self.replay["events"]]
        self.assertEqual(kinds[:3], ["establish", "stage", "commit"])
        self.assertLess(kinds.index("commit"), kinds.index("handoff"))
        self.assertEqual(kinds.count("admit"), 6)
        self.assertEqual(kinds.count("serve"), 6)
        self.assertEqual(len(kinds), 20)

    def test_early_bytes_and_actual_gateway_input_stay_distinct_sources(self):
        source_events = self.evidence["projection"]["events"]
        for binding in source_events:
            event = self.replay["events"][binding["event"]]
            native = self.evidence["events"][binding["nativeEvent"]]
            if binding["phase"] in {"admit", "establish"}:
                self.assertEqual(event["rawIPv4"], native["packet"]["admission"]["raw"])
                self.assertEqual(native["packet"]["admission"]["point"], "endpoint-postrouting")
                self.assertEqual(native["packet"]["admission"]["mode"], "complete")
            if binding["phase"] == "serve":
                self.assertEqual(event["rawIPv4"], native["packet"]["inputHex"])
                self.assertEqual(event["observed"]["output"], native["packet"]["outputEthernetHex"])

    def test_fast_admission_does_not_fabricate_intermediate_kernel_dump(self):
        for binding in self.evidence["projection"]["events"]:
            native = self.evidence["events"][binding["nativeEvent"]]
            event = self.replay["events"][binding["event"]]
            if binding["phase"] == "admit" and native["type"] == "packet":
                self.assertEqual(event["states"], {"primary": None, "standby": None})
            else:
                for actor, gateway in builder.GATEWAYS.items():
                    expected = json.loads(
                        (self.native / native["snapshots"]["after"][actor]).read_text()
                    )
                    self.assertEqual(event["states"][gateway], expected)

    def test_arbitrary_service_order_and_old_gateway(self):
        assigned = [row["observedID"] for row in self.replay["events"] if row["type"] == "admit"]
        retired = [row["id"] for row in self.replay["events"] if row["type"] == "serve"]
        self.assertEqual(assigned, [0, 1, 2, 3, 4, 5])
        self.assertEqual(retired, [1, 2, 0, 3, 4, 5])
        old = next(row for row in self.evidence["events"] if row["id"] == "serve-primary")
        self.assertEqual(old["gateway"], "a")
        self.assertEqual(old["packet"]["admission"]["interface"], "cal")

    def test_current_policy_installations_remain_operations(self):
        installs = [row for row in self.replay["events"] if row["type"] == "install"]
        self.assertEqual(
            [(row["gateway"], row["config"]) for row in installs],
            [("standby", "install-deny"), ("standby", "install-permit")],
        )
        held = next(
            row for row in self.replay["events"] if row["type"] == "serve" and row["id"] == 3
        )
        self.assertEqual(held["observed"]["disposition"], "forwardDrop")
        self.assertEqual(held["observed"]["classification"], "established")
        self.assertIsNone(held["observed"]["output"])

    def test_tables_retain_exact_source_objects_and_indices(self):
        configs = {row["id"]: row for row in self.replay["configs"]}
        self.assertEqual(len(configs), 4)
        for binding in self.evidence["projection"]["tables"]:
            document = json.loads((self.native / binding["source"]).read_text())
            expected = [document["nftables"][i] for i in binding["objectIndices"]]
            self.assertEqual(configs[binding["config"]][binding["field"]], {"nftables": expected})
        deny = next(
            row for row in self.evidence["projection"]["tables"] if row["config"] == "install-deny"
        )
        self.assertEqual(deny["source"], "install-deny-after-b-nftables.json")

    def test_queue_evidence_is_retained_without_claiming_global_pending_count(self):
        omitted = self.evidence["projection"]["omittedQueueEvents"]
        self.assertEqual(
            [row["id"] for row in omitted],
            [
                "install-primary-delay",
                "primary-barrier",
                "install-standby-delay",
                "standby-barrier",
            ],
        )
        self.assertEqual(self.evidence["queuePendingCounts"], [1, 1, 1, 1, 0, 1, 1, 0])
        self.assertTrue(all("pending" not in event for event in self.replay["events"]))

    def test_gate_failure_stops_projection(self):
        with patch.object(
            builder, "check_capture", side_effect=ValueError("native evidence mismatch")
        ):
            with self.assertRaisesRegex(ValueError, "native evidence mismatch"):
                builder.build()


if __name__ == "__main__":
    unittest.main()
