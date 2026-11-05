"""Keep the checked native history and its Lean attachment projection aligned."""

import json
import os
import unittest
from pathlib import Path
from unittest.mock import patch

import build_attachment_bundle as builder
from capture_evidence import EvidenceError

CAPTURE = Path(os.environ.get("NETLIB_ATTACHMENT_CAPTURE", builder.DIRECTORY / "native"))


class AttachmentProjectionTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.evidence, cls.bundle = builder.build(CAPTURE.parent)

    def test_raw_gate_is_required_before_projection(self):
        with (
            patch.object(builder, "check_capture", side_effect=EvidenceError("contradiction")),
            patch.object(builder, "project") as projection,
            self.assertRaisesRegex(EvidenceError, "contradiction"),
        ):
            builder.build(CAPTURE.parent)
        projection.assert_not_called()

    def test_native_table_objects_keep_their_exact_source_indices(self):
        configs = {row["id"]: row for row in self.bundle["handoff"]["configs"]}
        guards = {row["id"]: row for row in self.bundle["guards"]}
        for source in self.evidence["projection"]["tables"]:
            raw = json.loads((CAPTURE / source["source"]).read_text())["nftables"]
            self.assertEqual(
                configs[source["config"]][source["field"]]["nftables"],
                [raw[index] for index in source["objectIndices"]],
            )
        for source in self.evidence["projection"]["guards"]:
            raw = json.loads((CAPTURE / source["source"]).read_text())["nftables"]
            self.assertEqual(
                guards[source["guard"]]["ruleset"]["nftables"],
                [raw[index] for index in source["objectIndices"]],
            )

    def test_attacker_routes_remain_in_the_full_native_route_inventory(self):
        for gateway, device in (("primary", "aar"), ("standby", "abr")):
            routing = self.bundle["handoff"]["routing"][gateway]
            self.assertIn(
                {"device": device, "nextNode": "attacker", "gateway": None},
                routing["bindings"],
            )
            source = self.evidence["projection"]["routing"][gateway]
            self.assertEqual(routing["routes"], json.loads((CAPTURE / source).read_text()))

    def test_authentication_consumes_every_actual_frame_in_order(self):
        phase = self.evidence["eapEvidence"]["phases"][0]
        projected = self.bundle["authentication"]["events"]
        self.assertEqual(
            [row["raw"] for row in projected if row["type"] == "frame"],
            [frame["raw"] for frame in phase["frames"]],
        )
        references = [
            row["event"] for row in self.bundle["timeline"] if row["type"] == "authentication"
        ]
        self.assertEqual(references, list(range(len(projected))))

    def test_unsafe_probe_precedes_reset_and_actual_protection(self):
        timeline = self.bundle["timeline"]
        probes = [index for index, row in enumerate(timeline) if row["type"] == "probe"]
        reset = next(index for index, row in enumerate(timeline) if row["type"] == "reset")
        protect = next(index for index, row in enumerate(timeline) if row["type"] == "protect")
        self.assertLess(probes[0], reset)
        self.assertLess(reset, protect)
        self.assertTrue(all(protect < index for index in probes[1:]))
        self.assertTrue(timeline[probes[0]]["guard"])
        self.assertEqual(timeline[probes[0]]["observed"]["disposition"], "forwarded")
        for index in probes[1:]:
            self.assertFalse(timeline[index]["guard"])
            self.assertTrue(all(value is None for value in timeline[index]["observed"].values()))

    def test_guard_interfaces_retain_validated_namespace_and_lifetime_labels(self):
        raw = self.evidence["interfaceRefs"]
        self.assertEqual(self.bundle["authenticationPort"], builder.interface(raw["auth"]["auth0"]))
        for guard in self.bundle["guards"]:
            actor = "a" if guard["gateway"] == "primary" else "b"
            self.assertEqual(guard["namespace"], self.evidence["namespaceRefs"][actor])
            self.assertEqual(
                guard["bindings"],
                [
                    {"name": name, "reference": builder.interface(reference)}
                    for name, reference in raw[actor].items()
                ],
            )

    def test_joint_queued_drops_have_no_invented_intermediate_table(self):
        pair = next(row for row in self.evidence["events"] if row["type"] == "serve-pair")
        sources = [
            row for row in self.evidence["projection"]["timeline"] if row["id"] == pair["id"]
        ]
        projected = [self.bundle["handoff"]["events"][row["event"]] for row in sources]
        self.assertEqual(
            [row["id"] for row in projected], [row["ticket"] for row in pair["packets"]]
        )
        self.assertEqual(projected[0]["states"], {"primary": None, "standby": None})
        self.assertIsNone(projected[1]["states"]["primary"])
        self.assertEqual(
            projected[1]["states"]["standby"],
            json.loads((CAPTURE / pair["snapshots"]["after"]["b"]).read_text()),
        )
        for source, packet, event in zip(sources, pair["packets"], projected, strict=True):
            self.assertEqual(source["ingress"], builder.interface(packet["ingress"]))
            self.assertFalse(source["guard"])
            self.assertTrue(all(value is None for value in event["observed"].values()))


if __name__ == "__main__":
    unittest.main()
