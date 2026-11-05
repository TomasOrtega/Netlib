"""Check native reassembly projection sources, timing, and observation boundaries."""

import copy
import hashlib
import ipaddress
import json
import shutil
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

import build_reassembly_examples as build


def read_json(path):
    return json.loads(path.read_text())


class ProjectionTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.outputs = build.build()
        cls.evidence, cls.authentication, cls.session, cls.replay, cls.timeout = cls.outputs
        cls.native = build.DIRECTORY / "native"
        cls.observations = read_json(cls.native / cls.evidence["observationsFile"])
        cls.rows = {}

    def source_row(self, source):
        filename = source["file"]
        if filename not in self.rows:
            self.rows[filename] = [
                json.loads(line) for line in (self.native / filename).read_text().splitlines()
            ]
        return self.rows[filename][source["line"] - 1]

    def nflog(self, source):
        return build.capture.decode_nflog(self.source_row(source), source["line"])

    def rejected_native(self, change, pattern):
        with tempfile.TemporaryDirectory(prefix="netlib-reassembly-projection-") as temporary:
            directory = Path(temporary) / "reassembly"
            shutil.copytree(build.DIRECTORY, directory)
            change(directory)
            with self.assertRaisesRegex(build.capture.EvidenceError, pattern):
                build.build(directory)

    def test_all_actual_arrivals_and_controls_are_projected_once(self):
        events = self.evidence["events"]
        self.assertEqual(len(events), 82)
        self.assertEqual(len(self.replay["events"]), len(events))
        self.assertEqual(len(self.timeout["controls"]), len(events))
        self.assertEqual(sum(event["type"] == "fragment" for event in events), 79)
        self.assertEqual(sum(event["type"] == "wait" for event in events), 2)
        self.assertEqual(sum(event["type"] == "erase" for event in events), 1)
        for native, projected in zip(events, self.replay["events"], strict=True):
            self.assertEqual((projected["type"], projected["at"]), (native["type"], native["at"]))
            if native["type"] == "fragment":
                self.assertEqual(projected["rawIPv4"], native["rawIPv4"])
                self.assertEqual(projected["observed"], native["observed"])
                self.assertEqual(projected["config"], native["config"])
                self.assertEqual(projected["queuePolicy"], native["queuePolicy"])
                self.assertEqual(
                    (projected["zone"], projected["vif"]), (native["zone"], native["vif"])
                )
                self.assertNotIn("raw", projected)
            elif native["type"] == "erase":
                self.assertEqual(projected["rawIPv4"], native["rawIPv4"])
                self.assertEqual(projected["zone"], native["zone"])
                prior = self.nflog(native["source"])
                self.assertEqual(prior["prefix"], "POST_DEFRAG")
                self.assertEqual(projected["rawIPv4"], prior["packet"]["raw"])

    def test_ingress_and_completion_are_exact_nflog_ipv4_bytes(self):
        seen = set()
        previous_sequence = -1
        for event in self.evidence["events"]:
            if event["type"] != "fragment":
                continue
            source = event["source"]["pre"]
            identity = (source["file"], source["line"])
            self.assertNotIn(identity, seen)
            seen.add(identity)
            incoming = self.nflog(source)
            self.assertEqual(incoming["prefix"], "PRE_DEFRAG")
            self.assertEqual(event["rawIPv4"], incoming["packet"]["raw"])
            self.assertEqual(event["at"], incoming["timeNs"])
            self.assertEqual(source["globalSequence"], incoming["globalSequence"])
            self.assertGreater(incoming["globalSequence"], previous_sequence)
            previous_sequence = incoming["globalSequence"]
            raw = bytes.fromhex(event["rawIPv4"])
            self.assertEqual(raw[0], 0x45)
            self.assertEqual(len(raw), int.from_bytes(raw[2:4], "big"))
            post = event["source"]["post"]
            if post is None:
                self.assertIsNone(event["observed"]["reassembled"])
            else:
                completed = self.nflog(post)
                self.assertEqual(completed["prefix"], "POST_DEFRAG")
                self.assertEqual(event["observed"]["reassembled"], completed["packet"]["raw"])
            self.assertEqual(
                event["observed"]["forwarded"],
                [self.source_row(reference)["hex"] for reference in event["source"]["forwarded"]],
            )
        files = {
            event["source"]["pre"]["file"]
            for event in self.evidence["events"]
            if event["type"] == "fragment"
        }
        self.assertEqual(len(files), 1)
        filename = next(iter(files))
        all_arrivals = {
            (filename, line)
            for line, row in enumerate(self.rows[filename], 1)
            if build.capture.decode_nflog(row, line)["prefix"] == "PRE_DEFRAG"
        }
        self.assertEqual(seen, all_arrivals)

    def test_only_terminal_actual_step_events_receive_post_dumps(self):
        events = self.evidence["events"]
        last = {event["stepIndex"]: index for index, event in enumerate(events)}
        self.assertEqual(len(last), 73)
        self.assertEqual(sum(event["state"] is not None for event in self.replay["events"]), 73)
        self.assertEqual(sum(event["state"] is None for event in self.replay["events"]), 9)
        dumps = set()
        for index, (sample, event) in enumerate(zip(events, self.replay["events"], strict=True)):
            step = self.observations["steps"][sample["stepIndex"]]
            self.assertEqual(sample["stepName"], step["name"])
            if index != last[sample["stepIndex"]]:
                self.assertIsNone(sample["stateFile"])
                self.assertIsNone(event["state"])
                continue
            filename = step["after"]["file"]
            self.assertEqual(sample["stateFile"], filename)
            self.assertNotIn(filename, dumps)
            dumps.add(filename)
            self.assertEqual(event["state"], read_json(self.native / filename))
            self.assertLess(sample["at"], step["after"]["command"]["startNs"])
            self.assertLess(step["after"]["command"]["endNs"], step["endNs"])

    def test_clocks_and_queue_lifetimes_keep_nanosecond_precision(self):
        policies = {item["id"]: item["timeout"] for item in self.replay["reassembly"]["policies"]}
        self.assertEqual(policies, {"normal": 30_000_000_000, "short": 1_000_000_000})
        self.assertEqual(self.replay["reassembly"]["userBase"], 2)
        self.assertIn("net.ipv4.ipfrag_time = 30", self.observations["fragmentSettings"]["stdout"])
        short = next(
            item for item in self.observations["controls"] if item["kind"] == "queue-policy"
        )
        self.assertIn("net.ipv4.ipfrag_time = 1", short["readback"]["stdout"])
        times = [event["at"] for event in self.replay["events"]]
        self.assertEqual(times, sorted(times))
        self.assertTrue(any(at % 1_000_000_000 for at in times))
        for sample in self.evidence["events"]:
            if sample["type"] in ("wait", "erase"):
                step = self.observations["steps"][sample["stepIndex"]]
                self.assertEqual(sample["at"], step["sent"]["endNs"])
        first = next(
            event for event in self.evidence["events"] if event["label"] == "timeout-old-head"
        )
        wait = next(event for event in self.evidence["events"] if event["type"] == "wait")
        self.assertEqual(wait["expired"][0]["deadline"], first["at"] + policies["short"])
        self.assertLessEqual(wait["expired"][0]["deadline"], wait["at"])

    def test_eap_checkpoints_and_completion_policy_changes_remain_distinct(self):
        self.assertEqual(len(self.session["snapshots"]), 4)
        self.assertEqual(
            [stage["name"] for stage in self.evidence["stages"]],
            ["unauthenticated", "authenticated-only", "credential-permitted", "logged-off-cached"],
        )
        self.assertEqual([item["after"] for item in self.session["snapshots"]], [1, 18, 19, 21])
        self.assertEqual(self.observations["eap"]["phaseId"], 1)
        for snapshot, stage in zip(self.session["snapshots"], self.evidence["stages"], strict=True):
            self.assertEqual(snapshot["firewall"], read_json(self.native / stage["firewallFile"]))
        labels = {event["label"]: event for event in self.evidence["events"]}
        self.assertEqual(labels["logoff-split-head"]["config"], "credential-permitted")
        for label in ["logoff-split-middle", "logoff-split-tail", "permit-split-head"]:
            self.assertEqual(labels[label]["config"], "logged-off-cached")
        for label in ["permit-split-middle", "permit-split-tail"]:
            self.assertEqual(labels[label]["config"], "reassembly-probes")
        self.assertNotIn("reassembly-probes", [stage["name"] for stage in self.evidence["stages"]])
        self.assertEqual(len(self.authentication["events"]), 21)
        frames = [
            event["raw"] for event in self.authentication["events"] if event["type"] == "frame"
        ]
        self.assertEqual(
            frames, [frame["raw"] for frame in self.evidence["eapEvidence"]["phases"][0]["frames"]]
        )

    def test_policy_and_route_inputs_are_unchanged_native_readbacks(self):
        for value, source in zip(self.replay["configs"], self.evidence["configs"], strict=True):
            self.assertEqual(value["id"], source["id"])
            for key in ["forward", "nat", "late"]:
                self.assertEqual(value[key], read_json(self.native / source[f"{key}File"]))
        self.assertEqual(
            self.replay["routing"]["routes"],
            read_json(self.native / self.evidence["routing"]["routesFile"]),
        )
        self.assertEqual(self.replay["mtus"], self.evidence["mtus"])
        contexts = {context["id"]: context for context in self.timeout["contexts"]}
        for sample, control in zip(self.evidence["events"], self.timeout["controls"], strict=True):
            context = contexts[control["context"]]
            self.assertEqual(context["output"], read_json(self.native / sample["outputPolicyFile"]))
            self.assertEqual(context["late"], read_json(self.native / sample["latePolicyFile"]))
            for field in ["inputRoutes", "returns", "broadcasts"]:
                self.assertEqual(context[field], self.evidence["timeoutRouting"][field])
            chains = [row["chain"] for row in context["output"]["nftables"] if "chain" in row]
            self.assertTrue(any(chain["name"] == "before" for chain in chains))
            self.assertTrue(any(chain["name"] == "tracked" for chain in chains))
            selected = [chain for chain in chains if chain["name"] == "output"]
            self.assertEqual(len(selected), 1)
            self.assertEqual(
                (selected[0]["hook"], selected[0]["prio"], selected[0]["policy"]),
                ("output", 0, "drop"),
            )
            late = [row["chain"] for row in context["late"]["nftables"] if "chain" in row]
            self.assertEqual([(row["hook"], row["prio"]) for row in late], [("postrouting", 200)])

    def test_timeout_allocator_is_bound_to_checked_expired_first_source(self):
        self.assertEqual(self.timeout["forwarding"], self.replay)
        self.assertIsNot(self.timeout["forwarding"], self.replay)
        emissions = 0
        zones = []
        for index, (event, control) in enumerate(
            zip(self.evidence["events"], self.timeout["controls"], strict=True)
        ):
            self.assertEqual(control["event"], index)
            self.assertEqual(
                control["observed"], [item["rawEthernet"] for item in event["timeoutEmissions"]]
            )
            self.assertEqual(len(control["identifications"]), len(event["timeoutEmissions"]))
            for allocation, emission in zip(
                control["identifications"], event["timeoutEmissions"], strict=True
            ):
                expired = [
                    queue
                    for queue in event["expired"]
                    if queue["firstSource"] == emission["quotedFirstSource"]
                ]
                self.assertEqual(len(expired), 1)
                raw = bytes.fromhex(expired[0]["firstRawIPv4"])
                self.assertEqual(
                    allocation["key"],
                    {
                        "zone": expired[0]["zone"],
                        "vif": expired[0]["vif"],
                        "source": str(ipaddress.IPv4Address(raw[12:16])),
                        "destination": str(ipaddress.IPv4Address(raw[16:20])),
                        "protocol": raw[9],
                        "identification": int.from_bytes(raw[4:6], "big"),
                    },
                )
                self.assertEqual(allocation["identification"], emission["identification"])
                self.assertEqual(emission["templateZone"], allocation["key"]["zone"])
                self.assertEqual(emission["classification"], "invalid")
                zones.append(allocation["key"]["zone"])
                ethernet = bytes.fromhex(emission["rawEthernet"])
                size = int.from_bytes(ethernet[16:18], "big")
                self.assertEqual(ethernet[14 : 14 + size].hex(), emission["rawIPv4"])
                for name in ["before", "tracked", "egress"]:
                    self.assertEqual(
                        self.nflog(emission["source"][name])["packet"]["raw"], emission["rawIPv4"]
                    )
                self.assertEqual(
                    self.source_row(emission["source"]["frame"])["hex"], emission["rawEthernet"]
                )
                emissions += 1
        self.assertEqual(emissions, 2)
        self.assertEqual(zones, [0, 10])

    def test_failed_native_gate_prevents_projection(self):
        with patch.object(
            build.capture,
            "check_capture",
            side_effect=build.capture.EvidenceError("native gate rejected"),
        ):
            with self.assertRaisesRegex(build.capture.EvidenceError, "native gate rejected"):
                build.build()

    def test_intermediate_snapshot_cannot_be_fabricated(self):
        evidence = copy.deepcopy(self.evidence)
        first = next(
            index for index, event in enumerate(evidence["events"]) if event["stateFile"] is None
        )
        step = evidence["events"][first]["stepIndex"]
        evidence["events"][first]["stateFile"] = next(
            event["stateFile"]
            for event in evidence["events"]
            if event["stepIndex"] == step and event["stateFile"]
        )
        with patch.object(build.capture, "check_capture", return_value=evidence):
            with self.assertRaisesRegex(build.capture.EvidenceError, "terminal actual event"):
                build.build()

    def test_reused_pre_source_cannot_create_another_arrival(self):
        evidence = copy.deepcopy(self.evidence)
        fragments = [event for event in evidence["events"] if event["type"] == "fragment"]
        fragments[1]["source"]["pre"] = copy.deepcopy(fragments[0]["source"]["pre"])
        with patch.object(build.capture, "check_capture", return_value=evidence):
            with self.assertRaisesRegex(
                build.capture.EvidenceError, "PRE arrival source is repeated"
            ):
                build.build()

    def test_timeout_allocation_requires_unique_exact_checked_first_source(self):
        for change in ["missing", "ambiguous", "repeated"]:
            evidence = copy.deepcopy(self.evidence)
            event = next(event for event in evidence["events"] if event["timeoutEmissions"])
            if change == "missing":
                event["timeoutEmissions"][0]["quotedFirstSource"] = {"file": "missing", "line": 1}
            elif change == "ambiguous":
                event["expired"].append(copy.deepcopy(event["expired"][0]))
            else:
                event["timeoutEmissions"].append(copy.deepcopy(event["timeoutEmissions"][0]))
            with patch.object(build.capture, "check_capture", return_value=evidence):
                with self.assertRaisesRegex(
                    build.capture.EvidenceError, "exact expired first|allocation is repeated"
                ):
                    build.build()

    def test_native_post_dump_reuse_is_rejected_before_projection(self):
        def change(directory):
            path = directory / "native/observations.json"
            observations = read_json(path)
            observations["steps"][2]["after"] = copy.deepcopy(observations["steps"][3]["after"])
            path.write_text(json.dumps(observations))

        self.rejected_native(change, "snapshot|conntrack|state|dump|command|time|checkpoint")

    def test_rewritten_native_route_readback_is_rejected(self):
        self.rejected_native(
            lambda directory: (
                directory / "native" / self.evidence["routing"]["routesFile"]
            ).write_text("[]\n"),
            "route|export|readback|changed|copy|stdout",
        )

    def test_nflog_read_after_post_dump_cannot_keep_earlier_attribution(self):
        def change(directory):
            path = directory / "native/nflog.jsonl"
            rows = [json.loads(line) for line in path.read_text().splitlines()]
            first = next(event for event in self.evidence["events"] if event["type"] == "fragment")
            row = rows[first["source"]["pre"]["line"] - 1]
            row["timeNs"] = (
                self.observations["steps"][first["stepIndex"]]["after"]["command"]["endNs"] + 1
            )
            path.write_text("".join(json.dumps(row) + "\n" for row in rows))

        self.rejected_native(change, "NFLOG|time|step|window|read|snapshot|order")

    def test_saved_projection_is_exactly_reproducible(self):
        for name, value in zip(build.OUTPUTS, self.outputs, strict=True):
            self.assertEqual(
                (build.DIRECTORY / f"{name}.json").read_text(),
                json.dumps(value, indent=2) + "\n",
                name,
            )

    def test_build_does_not_change_native_artifacts(self):
        def hashes():
            return {
                path.relative_to(self.native).as_posix(): hashlib.sha256(
                    path.read_bytes()
                ).hexdigest()
                for path in self.native.rglob("*")
                if path.is_file()
            }

        before = hashes()
        self.assertEqual(build.build(), self.outputs)
        self.assertEqual(hashes(), before)


class ProjectionContractTests(unittest.TestCase):
    @staticmethod
    def events():
        return [
            {
                "type": "fragment",
                "stepIndex": 0,
                "at": 1000000001,
                "namespace": "auth",
                "stateFile": None,
                "source": {"pre": {"file": "nflog.jsonl", "line": 1}},
            },
            {
                "type": "fragment",
                "stepIndex": 0,
                "at": 1000000002,
                "namespace": "auth",
                "stateFile": "after-0.json",
                "source": {"pre": {"file": "nflog.jsonl", "line": 2}},
            },
            {
                "type": "wait",
                "stepIndex": 1,
                "at": 2000000003,
                "namespace": "auth",
                "stateFile": "after-1.json",
            },
        ]

    def test_subsecond_events_keep_their_order_without_rounding(self):
        events = self.events()
        before = copy.deepcopy(events)
        build._event_contract(events)
        self.assertEqual(events, before)

    def test_intermediate_and_missing_terminal_dumps_are_rejected(self):
        for index, value in [(0, "after-0.json"), (1, None)]:
            events = self.events()
            events[index]["stateFile"] = value
            with self.assertRaisesRegex(build.capture.EvidenceError, "terminal actual event"):
                build._event_contract(events)

    def test_reused_post_dump_and_pre_source_are_rejected(self):
        events = self.events()
        events[2]["stateFile"] = events[1]["stateFile"]
        with self.assertRaisesRegex(build.capture.EvidenceError, "reuse a post-dump"):
            build._event_contract(events)
        events = self.events()
        events[1]["source"] = copy.deepcopy(events[0]["source"])
        with self.assertRaisesRegex(build.capture.EvidenceError, "PRE arrival source is repeated"):
            build._event_contract(events)

    def test_clock_and_namespace_cannot_be_silently_projected(self):
        events = self.events()
        events[1]["at"] = events[0]["at"] - 1
        with self.assertRaisesRegex(build.capture.EvidenceError, "native time and step order"):
            build._event_contract(events)
        events = self.events()
        events[1]["namespace"] = "peer"
        with self.assertRaisesRegex(build.capture.EvidenceError, "gateway namespace"):
            build._event_contract(events)


if __name__ == "__main__":
    unittest.main()
