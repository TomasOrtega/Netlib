"""Contradiction tests use temporary synthetic copies; native packet bytes stay unchanged."""

import copy
import json
import re
import shutil
import tempfile
import unittest
from pathlib import Path

import check_received_icmp_capture as check

CAPTURE = check.DIRECTORY / "native"


def write(path, value):
    path.write_text(json.dumps(value, indent=2) + "\n")


def repair(frame):
    size = int.from_bytes(frame[16:18], "big")
    frame[24:26] = bytes(2)
    frame[24:26] = check.checksum(frame[14:34]).to_bytes(2, "big")
    frame[36:38] = bytes(2)
    frame[36:38] = check.checksum(frame[34 : 14 + size]).to_bytes(2, "big")


class ReceivedCaptureTests(unittest.TestCase):
    def reject(self, change, pattern="."):
        with tempfile.TemporaryDirectory() as temporary:
            directory = Path(temporary) / "native"
            shutil.copytree(CAPTURE, directory)
            change(directory)
            with self.assertRaisesRegex(check.EvidenceError, pattern):
                check.check_capture(directory)

    def observations(self, change, pattern="."):
        def mutate(directory):
            path = directory / "observations.json"
            value = json.loads(path.read_text())
            change(value)
            write(path, value)

        self.reject(mutate, pattern)

    def frames(self, namespace, change, pattern="."):
        def mutate(directory):
            path = directory / f"frames-{namespace}.jsonl"
            rows = [json.loads(line) for line in path.read_text().splitlines()]
            change(rows)
            path.write_text("".join(json.dumps(row) + "\n" for row in rows))

        self.reject(mutate, pattern)

    def export(self, selector, change, pattern="."):
        def mutate(directory):
            path = directory / "observations.json"
            observations = json.loads(path.read_text())
            record = selector(observations)
            original = copy.deepcopy(record["command"])
            document = json.loads((directory / record["file"]).read_text())
            change(document)
            encoded = json.dumps(document) + "\n"
            (directory / record["file"]).write_text(encoded)
            record["command"]["stdout"] = encoded
            commands = json.loads((directory / "commands.json").read_text())
            commands[commands.index(original)]["stdout"] = encoded
            write(directory / "commands.json", commands)
            write(path, observations)

        self.reject(mutate, pattern)

    def command(self, selector, change, pattern="."):
        def mutate(directory):
            path = directory / "observations.json"
            observations = json.loads(path.read_text())
            record = selector(observations)
            original = copy.deepcopy(record)
            change(record, observations)
            commands = json.loads((directory / "commands.json").read_text())
            commands[commands.index(original)] = copy.deepcopy(record)
            write(directory / "commands.json", commands)
            write(path, observations)

        self.reject(mutate, pattern)

    def trace(self, change, pattern="."):
        def mutate(directory):
            path = directory / "trace.txt"
            path.write_text(change(path.read_text()))

        self.reject(mutate, pattern)

    def outgoing_error(self, name, change, pattern="."):
        def mutate(directory):
            observations = json.loads((directory / "observations.json").read_text())
            episode = next(row for row in observations["receivedProbes"] if row["name"] == name)
            for namespace, interface, kind in (("auth", "auth0", 4), ("peer", "peer0", 0)):
                path = directory / f"frames-{namespace}.jsonl"
                rows = [json.loads(line) for line in path.read_text().splitlines()]
                row = next(
                    row
                    for row in rows
                    if episode["startNs"] < row["timeNs"] < episode["endNs"]
                    and row["interface"] == interface
                    and row["packetType"] == kind
                )
                frame = bytearray.fromhex(row["hex"])
                change(frame)
                repair(frame)
                row["hex"] = frame.hex()
                path.write_text("".join(json.dumps(row) + "\n" for row in rows))

        self.reject(mutate, pattern)

    def test_native_capture_and_host_feedback(self):
        evidence = check.check_capture(CAPTURE)
        self.assertEqual(
            (evidence["frameCount"], evidence["icmpFrameCount"], evidence["udpFragmentCount"]),
            (60, 22, 38),
        )
        self.assertEqual(len(evidence["packetSamples"]), 15)
        self.assertEqual(
            [row["eapFramesBeforeSend"] for row in evidence["stages"]], [0, 16, 16, 18]
        )
        self.assertEqual(
            [row["mtu"]["result"]["mtu"] for row in evidence["hostFeedback"]], [600, 600, 600]
        )
        samples = {row["label"]: row for row in evidence["packetSamples"]}
        self.assertEqual(
            samples["full-bad-udp-checksum"]["outputFamily"]["quotedUdpChecksum"]["status"],
            "invalid",
        )
        self.assertEqual(
            samples["bad-inner-ip-checksum"]["outputFamily"]["quotedIpChecksum"], "invalid"
        )
        self.assertEqual(evidence["receivedProbes"][-1]["mtu"]["result"]["mtu"], 576)

    def test_trace_identifiers_can_repeat_across_episodes(self):
        with tempfile.TemporaryDirectory() as temporary:
            directory = Path(temporary)
            path = directory / "trace.txt"
            path.write_text(
                re.sub(
                    r"trace id [0-9a-f]{8}",
                    "trace id 00000001",
                    (CAPTURE / "trace.txt").read_text(),
                )
            )
            traces = check.parse_traces(path)
        self.assertEqual(len(traces), 15)
        self.assertEqual({row["id"] for row in traces}, {"00000001"})

    def test_new_gateway_must_be_explicit(self):
        self.export(
            lambda x: x["networkExports"]["auth-routes"],
            lambda rows: next(row for row in rows if row["dst"] == "198.51.100.0/24").pop(
                "gateway"
            ),
            "gateway",
        )

    def test_old_gateway_shape_is_rejected(self):
        self.export(
            lambda x: x["networkExports"]["auth-routes"],
            lambda rows: next(row for row in rows if row["dst"] == "198.51.100.0/24").update(
                gateway="198.51.100.1"
            ),
            "gateway",
        )

    def test_missing_router_export(self):
        self.observations(lambda x: x["networkExports"].pop("router-routes"), "four namespace")

    def test_wrong_downstream_mtu(self):
        self.export(
            lambda x: x["networkExports"]["router-links"],
            lambda rows: next(row for row in rows if row["ifname"] == "srvlink").update(mtu=1500),
            "MTU",
        )

    def test_per_send_mtu_export_is_not_a_declared_constant(self):
        self.export(
            lambda x: x["hostFeedback"][0]["links"]["auth"],
            lambda rows: next(row for row in rows if row["ifname"] == "service0").update(mtu=600),
            "MTU",
        )

    def test_required_per_send_link_exports_cannot_be_omitted(self):
        for group, index, key in (
            ("hostFeedback", 0, "links"),
            ("receivedProbes", 0, "links"),
            ("stages", 0, "requestLinks"),
            ("stages", 2, "replyLinks"),
        ):
            with self.subTest(group=group, key=key):
                self.observations(
                    lambda x, group=group, index=index, key=key: x[group][index].pop(key),
                    "per-send",
                )

    def test_required_per_send_link_exports_cannot_be_null(self):
        self.observations(
            lambda x: x["hostFeedback"][0].update(links=None),
            "per-send",
        )

    def test_reply_cannot_reuse_request_link_commands(self):
        self.observations(
            lambda x: x["stages"][2].update(replyLinks=x["stages"][2]["requestLinks"]),
            "per-send",
        )

    def test_link_readback_requires_native_link_command(self):
        self.command(
            lambda x: x["hostFeedback"][0]["links"]["auth"]["command"],
            lambda record, x: record["command"].__setitem__(4, "address"),
            "command",
        )

    def test_link_readback_must_precede_its_send(self):
        self.command(
            lambda x: x["hostFeedback"][0]["links"]["auth"]["command"],
            lambda record, x: record.update(
                startNs=x["hostFeedback"][0]["sent"]["endNs"] + 1,
                endNs=x["hostFeedback"][0]["sent"]["endNs"] + 2,
            ),
            "per-send",
        )

    def test_raw_sender_command_is_bound_to_router_namespace(self):
        self.command(
            lambda x: x["receivedProbes"][0]["sent"],
            lambda record, x: record["command"].__setitem__(3, "peer"),
            "command",
        )

    def test_network_error_read_cannot_precede_send(self):
        self.observations(
            lambda x: x["hostFeedback"][0]["error"].update(
                startNs=x["hostFeedback"][0]["startNs"] + 1,
                endNs=x["hostFeedback"][0]["startNs"] + 2,
            ),
            "RPC|order",
        )

    def test_mtu_query_cannot_precede_error_read(self):
        self.observations(
            lambda x: x["hostFeedback"][0]["mtu"].update(
                startNs=x["hostFeedback"][0]["sent"]["endNs"] + 1,
                endNs=x["hostFeedback"][0]["sent"]["endNs"] + 2,
            ),
            "RPC|order",
        )

    def test_related_trace_comment_cannot_hide_invalid_match(self):
        self.trace(
            lambda text: text.replace(
                'ct state related counter packets 0 bytes 0 comment "RECEIVED_RELATED"',
                'ct state invalid counter packets 0 bytes 0 comment "RECEIVED_RELATED"',
                1,
            ),
            "class trace",
        )

    def test_gateway_udp_tos_is_preserved(self):
        def mutate(directory):
            observations = json.loads((directory / "observations.json").read_text())
            episode = observations["stages"][2]
            for namespace, interface, kind in (("auth", "service0", 4), ("router", "router0", 0)):
                path = directory / f"frames-{namespace}.jsonl"
                rows = [json.loads(line) for line in path.read_text().splitlines()]
                row = next(
                    row
                    for row in rows
                    if episode["startNs"] < row["timeNs"] < episode["endNs"]
                    and row["interface"] == interface
                    and row["packetType"] == kind
                )
                frame = bytearray.fromhex(row["hex"])
                frame[15] = 1
                frame[24:26] = bytes(2)
                frame[24:26] = check.checksum(frame[14:34]).to_bytes(2, "big")
                row["hex"] = frame.hex()
                path.write_text("".join(json.dumps(row) + "\n" for row in rows))

        self.reject(mutate, "UDP.*metadata|UDP.*forwarding")

    def test_connected_udp_df_is_observed(self):
        def mutate(directory):
            observations = json.loads((directory / "observations.json").read_text())
            episode = observations["hostFeedback"][2]
            for namespace, interface, kind in (("peer", "peer0", 4), ("auth", "auth0", 0)):
                path = directory / f"frames-{namespace}.jsonl"
                rows = [json.loads(line) for line in path.read_text().splitlines()]
                row = next(
                    row
                    for row in rows
                    if episode["startNs"] < row["timeNs"] < episode["endNs"]
                    and row["interface"] == interface
                    and row["packetType"] == kind
                )
                frame = bytearray.fromhex(row["hex"])
                frame[20:22] = bytes(2)
                frame[24:26] = bytes(2)
                frame[24:26] = check.checksum(frame[14:34]).to_bytes(2, "big")
                row["hex"] = frame.hex()
                path.write_text("".join(json.dumps(row) + "\n" for row in rows))

        self.reject(mutate, "DF|UDP.*forwarding")

    def test_nat_cannot_turn_udp_checksum_into_omission(self):
        def mutate(directory):
            observations = json.loads((directory / "observations.json").read_text())
            episode = observations["stages"][2]
            for namespace in ("auth", "router", "server"):
                path = directory / f"frames-{namespace}.jsonl"
                rows = [json.loads(line) for line in path.read_text().splitlines()]
                for row in rows:
                    frame = bytearray.fromhex(row["hex"])
                    if (
                        episode["startNs"] < row["timeNs"] < episode["endNs"]
                        and frame[23] == 17
                        and frame[26:30] == bytes((203, 0, 113, 1))
                        and not int.from_bytes(frame[20:22], "big") & 8191
                    ):
                        frame[40:42] = bytes(2)
                        row["hex"] = frame.hex()
                path.write_text("".join(json.dumps(row) + "\n" for row in rows))

        self.reject(mutate, "UDP.*checksum|UDP.*forwarding")

    def test_export_must_equal_actual_stdout(self):
        self.observations(
            lambda x: x["networkExports"]["auth-links"]["command"].update(stdout="[]\n"),
            "command history",
        )

    def test_initial_socket_mtu_is_observed(self):
        self.observations(
            lambda x: x["connectedSocket"]["result"].update(initialMTU=600), "initial IP_MTU"
        )

    def test_per_send_socket_mtu_is_observed(self):
        self.observations(
            lambda x: x["hostFeedback"][0]["mtuBefore"]["result"].update(mtu=600), "per-send"
        )

    def test_outer_ipv4_checksum(self):
        def mutate(rows):
            row = next(row for row in rows if bytes.fromhex(row["hex"])[23] == 1)
            frame = bytearray.fromhex(row["hex"])
            frame[24] ^= 1
            row["hex"] = frame.hex()

        self.frames("auth", mutate, "IPv4 checksum")

    def test_outer_icmp_checksum(self):
        def mutate(rows):
            row = next(row for row in rows if bytes.fromhex(row["hex"])[23] == 1)
            frame = bytearray.fromhex(row["hex"])
            frame[36] ^= 1
            row["hex"] = frame.hex()

        self.frames("auth", mutate, "ICMP error checksum")

    def test_checksum_valid_nat_quote_payload_tamper(self):
        self.outgoing_error(
            "forged-outer-source",
            lambda frame: frame.__setitem__(-1, frame[-1] ^ 1),
            "quoted payload",
        )

    def test_nat_does_not_repair_bad_inner_ip_checksum(self):
        def mutate(frame):
            frame[52:54] = bytes(2)
            frame[52:54] = check.checksum(frame[42:62]).to_bytes(2, "big")

        self.outgoing_error("bad-inner-ip-checksum", mutate, "whole quote")

    def test_output_outer_ttl_must_decrement(self):
        self.outgoing_error(
            "forged-outer-source", lambda frame: frame.__setitem__(22, 64), "outer forwarding"
        )

    def test_output_quote_udp_port_tamper(self):
        self.outgoing_error(
            "full-bad-udp-checksum",
            lambda frame: frame.__setitem__(63, frame[63] ^ 1),
            "whole quote",
        )

    def test_whole_udp_hook_checksum_is_recomputed(self):
        def mutate(text):
            lines = text.splitlines()
            index = next(
                i
                for i, line in enumerate(lines)
                if "netlib_trace afterDestination packet:" in line and " udp " in line
            )
            lines[index] = re.sub(r"udp checksum [0-9]+", "udp checksum 1", lines[index])
            return "\n".join(lines) + "\n"

        self.trace(mutate, "whole UDP hook checksum")

    def test_missing_native_hook(self):
        self.trace(
            lambda text: (
                "\n".join(
                    line for line in text.splitlines() if "netlib_trace afterSource" not in line
                )
                + "\n"
            ),
            "hook order",
        )

    def test_added_native_hook(self):
        self.trace(
            lambda text: text.replace("netlib_late late packet:", "untrusted late packet:", 1),
            "Orphan",
        )

    def test_reordered_trace_episodes(self):
        def mutate(text):
            groups = re.split(r"(?=trace id [0-9a-f]{8} ip netlib_trace before packet:)", text)[1:]
            groups[0], groups[1] = groups[1], groups[0]
            return "".join(groups)

        self.trace(mutate, "metadata")

    def test_related_trace_class_is_required(self):
        self.trace(
            lambda text: text.replace(
                'comment "RECEIVED_RELATED"', 'comment "RECEIVED_INVALID"', 1
            ),
            "class trace",
        )

    def test_accepting_trace_handle_resolves_to_exported_rule(self):
        self.trace(
            lambda text: text.replace("unknown rule handle 4", "unknown rule handle 999", 1),
            "rule handle",
        )

    def test_extra_trace_episode_is_not_ignored(self):
        self.trace(lambda text: text + text[: text.index("trace id", 10)], "trace count")

    def test_error_frame_read_must_precede_post_state(self):
        def mutate(rows):
            observations = json.loads((CAPTURE / "observations.json").read_text())
            episode = observations["receivedProbes"][-1]
            row = rows[-1]
            row["timeNs"] = episode["after"]["command"]["endNs"] + 1

        self.frames("auth", mutate, "post-state fences")

    def test_local_pmtu_must_reject_oversize_send(self):
        self.observations(
            lambda x: x["hostFeedback"][1]["sent"]["result"].update(errno=11), "cached PMTU"
        )

    def test_host_mtu_feedback_is_not_inferred_from_icmp_only(self):
        self.observations(
            lambda x: x["hostFeedback"][0]["mtu"]["result"].update(mtu=4096), "IP_MTU readback"
        )

    def test_error_queue_mtu_must_match_raw_ancillary(self):
        self.observations(
            lambda x: x["hostFeedback"][0]["error"]["result"]["ancillary"][0].update(info=1500),
            "raw errno",
        )

    def test_network_error_origin_is_not_local_errno(self):
        def mutate(x):
            value = x["hostFeedback"][0]["error"]["result"]["ancillary"][0]
            raw = bytearray.fromhex(value["hex"])
            raw[4] = 1
            value.update(hex=raw.hex(), origin=1)

        self.observations(mutate, "raw errno")

    def test_received_error_does_not_mark_udp_seen_reply(self):
        def mutate(directory):
            path = directory / "native-df-oversize-after-conntrack.json"
            value = json.loads(path.read_text())
            old = "08000300000001b8"
            new = "08000300000001ba"
            value["entries"][0]["status"] = 442
            value["entries"][0]["raw"] = value["entries"][0]["raw"].replace(old, new)
            value["messages"] = [row.replace(old, new) for row in value["messages"]]
            write(path, value)

        self.reject(mutate, "seen-reply")

    def test_reply_socket_payload_must_match_capture(self):
        self.observations(
            lambda x: x["hostFeedback"][2]["client"]["result"].update(payload="synthetic"),
            "reply payload",
        )

    def test_raw_probe_is_explicitly_labeled(self):
        self.observations(lambda x: x["receivedProbes"][0].update(origin="native-host"), "origin")

    def test_unrelated_control_cannot_bypass_explicit_policy(self):
        def mutate(document):
            rule = next(
                row["rule"]
                for row in document["nftables"]
                if row.get("rule", {}).get("comment") == "RECEIVED_CONTROL"
            )
            rule["expr"].pop(1)

        self.export(lambda x: x["finalExports"]["firewall"], mutate, "RELATED scope")

    def test_exclusive_ruleset_rejects_added_base_hook(self):
        self.export(
            lambda x: x["finalExports"]["ruleset"],
            lambda document: document["nftables"].append(
                {
                    "chain": {
                        "family": "ip",
                        "table": "netlib_trace",
                        "name": "extra",
                        "type": "filter",
                        "hook": "output",
                        "prio": -400,
                        "policy": "accept",
                    }
                }
            ),
            "Additional hook",
        )

    def test_related_counters_account_for_ttl_drop(self):
        def mutate(document):
            rule = next(
                row["rule"]
                for row in document["nftables"]
                if row.get("rule", {}).get("comment") == "RECEIVED_RELATED"
            )
            rule["expr"][-1]["counter"]["packets"] -= 1

        self.export(lambda x: x["finalExports"]["ruleset"], mutate, "table export")

    def test_extra_native_frame_is_not_ignored(self):
        def mutate(rows):
            row = copy.deepcopy(rows[-1])
            row["timeNs"] += 1
            rows.append(row)

        self.frames("peer", mutate, "endpoint captures")

    def test_capture_producer_source_bytes_are_bound(self):
        def mutate(directory):
            path = directory / "helper-sha256.txt"
            path.write_text(path.read_text().replace("/task/received-icmp/", "/task/unbound/"))

        self.reject(mutate, "source bytes")

    def test_host_route_exception_is_native_stdout(self):
        self.observations(
            lambda x: x["hostFeedback"][0]["routeAfter"].update(stdout="[]\n"),
            "command history",
        )

    def test_pending_network_error_is_drained_before_next_send(self):
        self.observations(
            lambda x: x["hostFeedback"][0]["error"].update(
                endNs=x["hostFeedback"][1]["sent"]["startNs"] + 1
            ),
            "interval|outside|snapshot",
        )


if __name__ == "__main__":
    unittest.main()
