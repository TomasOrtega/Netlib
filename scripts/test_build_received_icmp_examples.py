"""Check native-to-model projection boundaries without constructing native observations."""

import copy
import json
import shutil
import tempfile
import unittest
from pathlib import Path

import build_received_icmp_examples as build
from check_received_icmp_capture import EvidenceError


class ProjectionTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.outputs = build.build()
        cls.evidence, cls.authentication, cls.session, cls.gateway, cls.host = cls.outputs
        cls.observed = json.loads((build.DIRECTORY / "native/observations.json").read_text())

    def rejected_native(self, change, pattern):
        with tempfile.TemporaryDirectory() as temporary:
            directory = Path(temporary) / "received-icmp"
            shutil.copytree(build.DIRECTORY, directory)
            path = directory / "native/observations.json"
            observations = json.loads(path.read_text())
            change(observations)
            path.write_text(json.dumps(observations))
            with self.assertRaisesRegex(EvidenceError, pattern):
                build.build(directory)

    def test_later_stage_snapshot_cannot_replace_permit_observation(self):
        self.rejected_native(
            lambda x: x["stages"][2].update(state=copy.deepcopy(x["stages"][3]["state"])),
            "snapshot|conntrack|state",
        )

    def test_only_terminal_events_receive_shared_episode_snapshots(self):
        expected = {
            0: "unauthenticated-conntrack.json",
            1: "authenticated-only-conntrack.json",
            3: "credential-permitted-conntrack.json",
            4: "logged-off-cached-conntrack.json",
            5: "erased-conntrack.json",
            7: "native-df-oversize-after-conntrack.json",
            9: "pmtu-small-roundtrip-after-conntrack.json",
            10: "unmatched-quote-after-conntrack.json",
            11: "wrong-outer-destination-after-conntrack.json",
            12: "ttl-one-control-after-conntrack.json",
            13: "full-bad-udp-checksum-after-conntrack.json",
            14: "bad-inner-ip-checksum-after-conntrack.json",
            15: "forged-outer-source-after-conntrack.json",
        }
        self.assertEqual(len(self.gateway["events"]), 16)
        self.assertEqual(sum(event["state"] is not None for event in self.gateway["events"]), 13)
        for index, event in enumerate(self.gateway["events"]):
            if index not in expected:
                self.assertIsNone(event["state"])
            else:
                snapshot = json.loads((build.DIRECTORY / "native" / expected[index]).read_text())
                self.assertEqual(event["state"], snapshot)
        self.assertEqual(
            [
                index
                for index, event in enumerate(self.gateway["events"])
                if event["type"] == "erase"
            ],
            [5],
        )
        self.assertEqual(self.gateway["events"][5]["state"]["entries"], [])

    def test_gateway_packets_and_outputs_are_unchanged_checked_bytes(self):
        packets = [event for event in self.gateway["events"] if event["type"] != "erase"]
        self.assertEqual(len(packets), 15)
        for event, sample in zip(packets, self.evidence["packetSamples"], strict=True):
            self.assertEqual(event["raw"], sample["raw"])
            self.assertEqual(event["observed"], sample["observed"])
            self.assertEqual(event["config"], sample["config"])
            self.assertEqual(event["zone"], sample["zone"])
            self.assertEqual(
                event["type"], "udp" if sample["ingress"]["protocol"] == 17 else "icmp"
            )

    def test_host_receives_exact_peer_side_nat_corrected_errors(self):
        rows = [
            json.loads(line)
            for line in (build.DIRECTORY / "native/frames-peer.jsonl").read_text().splitlines()
        ]
        records = [self.observed["hostFeedback"][0], *self.observed["receivedProbes"][3:]]
        expected = []
        for record in records:
            frames = [
                row
                for row in rows
                if record["startNs"] < row["timeNs"] < record["endNs"]
                and bytes.fromhex(row["hex"])[23] == 1
            ]
            self.assertEqual(len(frames), 1)
            self.assertLess(frames[0]["timeNs"], record["error"]["startNs"])
            self.assertEqual(record["error"]["result"]["ancillary"][0]["origin"], 2)
            expected.append(frames[0]["hex"])
        receives = [event for event in self.host["events"] if event["type"] == "receive"]
        self.assertEqual([event["raw"] for event in receives], expected)
        forwarded = {
            raw
            for event in self.gateway["events"]
            if event["type"] == "icmp"
            for raw in event["observed"]["forwarded"]
        }
        self.assertEqual(set(expected), forwarded)

    def test_host_event_times_follow_native_rpc_ends(self):
        feedback, probes = self.observed["hostFeedback"], self.observed["receivedProbes"]
        anchors = [
            ("query", feedback[0]["mtuBefore"]),
            ("send", feedback[0]["sent"]),
            ("receive", feedback[0]["error"]),
            ("query", feedback[0]["mtu"]),
            ("query", feedback[1]["mtuBefore"]),
            ("send", feedback[1]["sent"]),
            ("query", feedback[1]["mtu"]),
            ("query", feedback[2]["mtuBefore"]),
            ("send", feedback[2]["sent"]),
            ("query", feedback[2]["mtu"]),
            ("query", probes[0]["mtu"]),
            ("query", probes[1]["mtu"]),
            ("query", probes[2]["mtu"]),
            ("receive", probes[3]["error"]),
            ("query", probes[3]["mtu"]),
            ("receive", probes[4]["error"]),
            ("query", probes[4]["mtu"]),
            ("receive", probes[5]["error"]),
            ("query", probes[5]["mtu"]),
        ]
        self.assertEqual(len(self.host["events"]), 19)
        self.assertEqual(
            [(event["type"], event["at"]) for event in self.host["events"]],
            [(kind, record["endNs"] // 1_000_000_000) for kind, record in anchors],
        )
        self.assertTrue(
            all(
                first[1]["endNs"] < second[1]["endNs"]
                for first, second in zip(anchors, anchors[1:])
            )
        )
        sends = [event for event in self.host["events"] if event["type"] == "send"]
        self.assertEqual([event["payloadLength"] for event in sends], [1200, 1200, 500])
        self.assertEqual(
            [event["observed"] for event in sends], ["accepted", "messageSize", "accepted"]
        )
        self.assertTrue(all(event["df"] and event["errorsDrained"] for event in sends))
        self.assertLess(feedback[0]["error"]["endNs"], feedback[1]["sent"]["startNs"])
        self.assertLess(feedback[1]["error"]["endNs"], feedback[2]["sent"]["startNs"])

    def test_coarse_host_times_do_not_bypass_native_causality(self):
        def mutate(observations):
            episode = observations["hostFeedback"][0]
            episode["error"].update(startNs=episode["startNs"] + 1, endNs=episode["startNs"] + 2)

        self.rejected_native(mutate, "RPC|order")

    def test_probe_policy_has_no_extra_session_checkpoint(self):
        self.assertEqual(
            [snapshot["after"] for snapshot in self.session["snapshots"]], [1, 18, 19, 21]
        )
        self.assertEqual(
            [config["id"] for config in self.gateway["configs"]],
            [
                "unauthenticated",
                "authenticated-only",
                "credential-permitted",
                "logged-off-cached",
                "received-probes",
            ],
        )
        self.assertEqual(
            self.gateway["routing"]["routes"],
            json.loads((build.DIRECTORY / "native/network-auth-routes.json").read_text()),
        )
        self.assertIn(
            {"device": "service0", "nextNode": "service", "gateway": "198.51.101.254"},
            self.gateway["routing"]["bindings"],
        )
        self.assertIn({"nextHop": "service", "mtu": 1500}, self.gateway["mtus"])

    def test_saved_projection_is_exactly_reproducible(self):
        for name, value in zip(
            ("checked-evidence", "authentication", "session", "replay", "host"),
            self.outputs,
            strict=True,
        ):
            self.assertEqual(
                (build.DIRECTORY / f"{name}.json").read_text(),
                json.dumps(value, indent=2) + "\n",
                name,
            )


if __name__ == "__main__":
    unittest.main()
