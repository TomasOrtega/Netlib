"""Check the source joins and causal order of the joint deployment projection."""

import json
import unittest
from unittest.mock import patch

import build_campus_examples as builder


class CampusProjectionTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.evidence, cls.bundle = builder.build()

    def test_each_actual_stream_is_consumed_once(self):
        timeline = self.bundle["timeline"]
        for kind, count in (
            ("authentication", len(self.bundle["authentication"]["events"])),
            ("network", len(self.bundle["handoff"]["events"])),
        ):
            self.assertEqual(
                [row["event"] for row in timeline if row["type"] == kind], list(range(count))
            )
        self.assertEqual(sum(row["type"] == "withdraw" for row in timeline), 1)

    def test_authentication_uses_the_same_actual_frames(self):
        phase = self.evidence["eapEvidence"]["phases"][0]
        authentication = self.bundle["authentication"]
        self.assertEqual(
            [row["raw"] for row in authentication["events"] if row["type"] == "frame"],
            [row["raw"] for row in phase["frames"]],
        )
        self.assertEqual(
            authentication["context"]["consumer"], self.evidence["eapEvidence"]["subject"]
        )
        self.assertNotEqual(
            authentication["context"]["consumer"], self.evidence["eapEvidence"]["outerIdentity"]
        )
        self.assertEqual(authentication["link"], self.evidence["eapEvidence"]["link"])

    def test_method_and_credential_follow_the_actual_success(self):
        events = self.bundle["authentication"]["events"]
        method = next(i for i, row in enumerate(events) if row["type"] == "method")
        credential = next(i for i, row in enumerate(events) if row["type"] == "install")
        self.assertEqual(
            sum(row["type"] == "frame" for row in events[:method]),
            self.evidence["eapEvidence"]["phases"][0]["terminalFrame"],
        )
        self.assertLess(method, credential)
        self.assertEqual(events[credential]["credential"], self.evidence["credential"])
        self.assertTrue(
            all(
                row["scope"] == self.bundle["application"]
                for row in self.bundle["intent"]["requirements"]
            )
        )

    def test_current_policy_changes_are_causally_ordered(self):
        authenticated = 0
        logoff = None
        hold = serve = None
        events = self.bundle["handoff"]["events"]
        sources = self.evidence["projection"]["timeline"]
        self.assertEqual(len(sources), len(self.bundle["timeline"]))
        for index, row in enumerate(self.bundle["timeline"]):
            source = sources[index]
            self.assertEqual(source["timeline"], index)
            self.assertEqual(self.evidence["events"][source["nativeEvent"]]["id"], source["id"])
            if row["type"] == "authentication":
                authenticated += 1
                if source["id"] == "logoff":
                    logoff = index
            elif row["type"] == "network":
                event = events[row["event"]]
                if event["type"] == "install":
                    self.assertEqual(authenticated, 21 if event["config"].endswith("deny") else 19)
                if event["type"] == "admit" and event["observedID"] == 5:
                    hold = index
                if event["type"] == "serve" and event["id"] == 5:
                    serve = index
        self.assertLess(hold, logoff)
        self.assertLess(logoff, serve)

    def test_withdrawn_primary_has_no_fabricated_live_observation(self):
        withdrawn = False
        for row in self.bundle["timeline"]:
            if row["type"] == "withdraw":
                withdrawn = True
            elif withdrawn and row["type"] == "network":
                event = self.bundle["handoff"]["events"][row["event"]]
                self.assertIsNone(event["states"]["primary"])
                self.assertNotIn(
                    event["type"], {"stage", "commit", "establish", "handoff", "fence"}
                )
                if event["type"] == "install":
                    self.assertEqual(event["gateway"], "standby")

    def test_fast_admission_has_no_invented_intermediate_table(self):
        sources = self.evidence["projection"]["timeline"]
        for row in sources:
            if row.get("type") != "network":
                continue
            event = self.bundle["handoff"]["events"][row["event"]]
            native = self.evidence["events"][row["nativeEvent"]]
            if event["type"] == "admit" and native["type"] == "packet":
                self.assertEqual(event["states"], {"primary": None, "standby": None})

    def test_sources_retain_actual_early_and_gateway_bytes(self):
        for row in self.evidence["projection"]["timeline"]:
            if row.get("type") != "network":
                continue
            event = self.bundle["handoff"]["events"][row["event"]]
            native = self.evidence["events"][row["nativeEvent"]]
            if event["type"] in {"admit", "establish"}:
                self.assertEqual(event["rawIPv4"], native["packet"]["admission"]["raw"])
            elif event["type"] == "serve":
                self.assertEqual(event["rawIPv4"], native["packet"]["inputHex"])
                self.assertEqual(event["observed"]["output"], native["packet"]["outputEthernetHex"])

    def test_configurations_are_unchanged_native_object_slices(self):
        configs = {row["id"]: row for row in self.bundle["handoff"]["configs"]}
        for row in self.evidence["projection"]["tables"]:
            native = json.loads((builder.DIRECTORY / "native" / row["source"]).read_text())
            self.assertEqual(
                configs[row["config"]][row["field"]]["nftables"],
                [native["nftables"][i] for i in row["objectIndices"]],
            )

    def test_queue_observations_remain_separate_evidence(self):
        omitted = self.evidence["projection"]["omittedQueueEvents"]
        self.assertEqual(len(omitted), 4)
        self.assertEqual({row["type"] for row in omitted}, {"qdisc", "barrier"})
        self.assertNotIn("initial", self.bundle["handoff"])
        self.assertNotIn("pending", self.bundle)

    def test_native_gate_is_mandatory(self):
        with patch.object(
            builder, "check_capture", side_effect=ValueError("rejected raw evidence")
        ):
            with self.assertRaisesRegex(ValueError, "rejected raw evidence"):
                builder.build()


if __name__ == "__main__":
    unittest.main()
