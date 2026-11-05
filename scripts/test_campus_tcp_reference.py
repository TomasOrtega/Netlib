"""Static tests for constructed campus TCP execution."""

import copy
import json
import unittest

import campus_tcp_reference as reference
import check_campus_tcp_examples as comparison


class ComponentTests(unittest.TestCase):
    def setUp(self):
        self.authentication = reference.load("authentication")
        self.requirements = reference.load("requirements")
        self.scope = self.requirements["requirements"][0]["scope"]
        self.routing = reference.load("routing")
        self.configs = {row["id"]: row for row in reference.load("configs")}
        self.client = reference.handshake.Local(
            reference.handshake.Socket("192.0.2.2", 41000), 1000, 8, 16, 576
        )
        self.server = reference.handshake.Local(
            reference.handshake.Socket("198.51.100.2", 9000), 5000, 8, 16, 576
        )
        self.public = reference.handshake.Socket("203.0.113.2", 8080)
        self.syn = reference.handshake.control_output(self.client, self.public, 1000, 0, 2)

    def test_authentication_comes_from_correlated_frames_and_bound_evidence(self):
        state = reference.Authentication()
        observed = []
        for event in self.authentication["events"]:
            state, matched = reference.authentication_step(
                state, self.authentication["context"], self.authentication["link"], event
            )
            self.assertTrue(matched)
            observed.append(state.authorized)
        self.assertEqual(observed, [False, False, False, False, True, True, True, False])
        self.assertFalse(state.authenticated)
        self.assertIsNone(state.credential)

    def test_observed_authorization_does_not_set_authentication(self):
        state, matched = reference.authentication_step(
            reference.Authentication(),
            self.authentication["context"],
            self.authentication["link"],
            {"type": "begin", "authorized": True},
        )
        self.assertFalse(matched)
        self.assertFalse(state.authorized)

    def test_wrong_method_round_does_not_authorize_the_client(self):
        state = reference.Authentication()
        for event in self.authentication["events"][:5]:
            event = {**event, "round": 0} if event["type"] == "method" else event
            state, _ = reference.authentication_step(
                state, self.authentication["context"], self.authentication["link"], event
            )
        self.assertFalse(state.authorized)

    def test_credential_scope_and_clock_remain_separate_from_method_acceptance(self):
        state = reference.Authentication()
        for event in self.authentication["events"][:6]:
            state, _ = reference.authentication_step(
                state, self.authentication["context"], self.authentication["link"], event
            )
        self.assertTrue(state.authorized)
        self.assertTrue(state.permits(self.authentication["context"], self.scope))
        self.assertFalse(
            state.permits(
                self.authentication["context"], {"resource": "management", "operation": "use"}
            )
        )
        later, _ = reference.authentication_step(
            state,
            self.authentication["context"],
            self.authentication["link"],
            {"type": "advance", "now": 100, "authorized": True},
        )
        self.assertTrue(later.authorized)
        self.assertFalse(later.permits(self.authentication["context"], self.scope))

    def test_fresh_syn_uses_imported_nat_and_route_inputs(self):
        result = reference.forward((), self.routing, self.configs["permit"], self.syn["rawIPv4Hex"])
        self.assertEqual(
            (result.classification, result.fresh, result.disposition, result.next_hop),
            ("new", True, "forwarded", "server"),
        )
        self.assertEqual(
            (result.after_destination.source, result.after_destination.destination),
            ("192.0.2.2", "198.51.100.2"),
        )
        self.assertEqual(
            (result.after_destination.source_port, result.after_destination.destination_port),
            (41000, 9000),
        )
        self.assertEqual(
            (result.after_source.source, result.after_source.destination),
            ("203.0.113.1", "198.51.100.2"),
        )
        self.assertEqual(
            (result.after_source.source_port, result.after_source.destination_port), (40000, 9000)
        )
        self.assertEqual(len(result.records), 1)
        self.assertEqual(result.output["decoded"]["ttl"], 63)

    def test_denied_fresh_syn_does_not_confirm_a_record(self):
        result = reference.forward((), self.routing, self.configs["deny"], self.syn["rawIPv4Hex"])
        self.assertEqual(result.disposition, "forwardDrop")
        self.assertEqual(result.records, ())
        self.assertIsNone(result.output)

    def test_reply_uses_the_same_record_and_inverse_nat(self):
        first = reference.forward((), self.routing, self.configs["permit"], self.syn["rawIPv4Hex"])
        reply = reference.handshake.control_output(
            self.server, reference.handshake.Socket("203.0.113.1", 40000), 5000, 1001, 18
        )
        result = reference.forward(
            first.records, self.routing, self.configs["permit"], reply["rawIPv4Hex"]
        )
        self.assertEqual(
            (result.classification, result.fresh, result.direction, result.next_hop),
            ("established", False, "reply", "client"),
        )
        self.assertTrue(result.records[0].seen_reply)
        self.assertEqual(
            result.output["decoded"]["header"],
            reference.wire.Header("203.0.113.2", "192.0.2.2", 6, 8080, 41000).to_dict(),
        )

    def test_valid_denied_reply_marks_seen_reply_before_filtering(self):
        first = reference.forward((), self.routing, self.configs["permit"], self.syn["rawIPv4Hex"])
        reply = reference.handshake.control_output(
            self.server, reference.handshake.Socket("203.0.113.1", 40000), 5000, 1001, 18
        )
        result = reference.forward(
            first.records, self.routing, self.configs["deny"], reply["rawIPv4Hex"]
        )
        self.assertEqual(result.disposition, "forwardDrop")
        self.assertTrue(result.records[0].seen_reply)
        self.assertIsNone(result.output)

    def test_late_filter_sees_the_translated_source(self):
        config = copy.deepcopy(self.configs["permit"])
        for item in config["late"]["nftables"]:
            if "chain" in item:
                item["chain"]["policy"] = "drop"
        result = reference.forward((), self.routing, config, self.syn["rawIPv4Hex"])
        self.assertEqual(result.disposition, "lateDrop")
        self.assertEqual(result.after_source.source, "203.0.113.1")
        self.assertEqual(result.records, ())

    def test_route_role_is_computed_without_an_authorization_override(self):
        routing = copy.deepcopy(self.routing)
        next(row for row in routing["bindings"] if row["nextNode"] == "server")["nextNode"] = (
            "management"
        )
        result = reference.forward((), routing, self.configs["permit"], self.syn["rawIPv4Hex"])
        self.assertEqual(result.next_hop, "management")
        self.assertEqual(result.disposition, "forwarded")
        self.assertIsNotNone(result.output)

    def startup(self):
        state = reference.Admission()
        records = ()
        outputs = [self.syn]
        server_reply = reference.handshake.control_output(
            self.server, reference.handshake.Socket("203.0.113.1", 40000), 5000, 1001, 18
        )
        final_ack = reference.handshake.control_output(self.client, self.public, 1001, 5001, 16)
        for output in [self.syn, server_reply, final_ack]:
            raw = output["rawIPv4Hex"]
            packet = reference.wire.decode_packet(raw)
            _, record, direction, fresh = reference.attachment(
                records, self.configs["permit"], packet.header
            )
            candidate, reason = reference.admit(state, record, direction, fresh, raw)
            self.assertIsNone(reason)
            result = reference.forward(records, self.routing, self.configs["permit"], raw)
            state, reason = reference.commit_admission(candidate, record, fresh, result.records)
            self.assertIsNone(reason)
            records = result.records
            outputs.append(output)
        return state, records

    def test_admission_startup_uses_three_observed_control_segments(self):
        state, records = self.startup()
        self.assertEqual(state.phase, "data")
        self.assertEqual(len(state.observations), 3)
        self.assertEqual((state.original.base, state.reply.base), (1001, 5001))
        self.assertEqual((state.original.peer_window, state.reply.peer_window), (8, 8))
        self.assertTrue(records[0].seen_reply)

    def test_directional_mss_changes_only_the_peer_lane_data_bound(self):
        h = reference.handshake
        self.client = h.Local.from_dict(
            {
                **self.client.to_dict(),
                "capacity": 4096,
                "ipSendLimit": 1000,
                "receiveMSS": {"ipReceiveLimit": 1240, "value": 1200},
            }
        )
        self.server = h.Local.from_dict(
            {
                **self.server.to_dict(),
                "capacity": 4096,
                "ipSendLimit": 1500,
                "receiveMSS": {"ipReceiveLimit": 840, "value": 800},
            }
        )
        self.syn = h.control_output(self.client, self.public, 1000, 0, 2)
        state, _ = self.startup()
        segment = reference.wire.decode_packet(
            h.control_output(self.client, self.public, 1001, 5001, 16)["rawIPv4Hex"]
        ).segment
        accepted, reason = reference.data_admission(
            state.original, state.reply, reference.replace(segment, payload=bytes(800))
        )
        self.assertIsNone(reason)
        self.assertEqual(accepted[0].observed, 800)
        _, reason = reference.data_admission(
            state.original, state.reply, reference.replace(segment, payload=bytes(801))
        )
        self.assertEqual(reason, "data")
        reply = reference.replace(segment, sequence=5001, acknowledgment=1001)
        accepted, reason = reference.data_admission(
            state.reply, state.original, reference.replace(reply, payload=bytes(1200))
        )
        self.assertIsNone(reason)
        self.assertEqual(accepted[0].observed, 1200)

    def test_admission_missing_syn_history_does_not_create_a_data_lane(self):
        state, records = self.startup()
        raw = state.observations[-1][1].hex()
        _, reason = reference.admit(reference.Admission(), records[0], "original", False, raw)
        self.assertEqual(reason, "missingHistory")

    def test_invalid_reply_does_not_commit_prepared_seen_reply(self):
        first = reference.forward((), self.routing, self.configs["permit"], self.syn["rawIPv4Hex"])
        state, reason = reference.admit(
            reference.Admission(), first.record, "original", True, self.syn["rawIPv4Hex"]
        )
        self.assertIsNone(reason)
        wrong = reference.handshake.control_output(
            self.server, reference.handshake.Socket("203.0.113.1", 40000), 5000, 1002, 18
        )
        _, reason = reference.admit(state, first.record, "reply", False, wrong["rawIPv4Hex"])
        self.assertEqual(reason, "acknowledgment")
        self.assertFalse(first.records[0].seen_reply)

    def test_fresh_dropped_syn_discards_admission_history(self):
        result = reference.forward((), self.routing, self.configs["deny"], self.syn["rawIPv4Hex"])
        admitted, _ = reference.admit(
            reference.Admission(), result.record, "original", True, self.syn["rawIPv4Hex"]
        )
        after, reason = reference.commit_admission(admitted, result.record, True, result.records)
        self.assertIsNone(reason)
        self.assertEqual(after, reference.Admission())

    def test_admission_data_preserves_an_old_ack_without_updating_the_window(self):
        state, _ = self.startup()
        original = reference.replace(state.original, observed=3, acknowledged=3)
        reply = reference.replace(state.reply, observed=1)
        segment = reference.wire.decode_packet(
            reference.handshake.control_output(self.client, self.public, 1004, 5001, 16)[
                "rawIPv4Hex"
            ]
        ).segment
        segment = reference.replace(segment, payload=b"d", acknowledgment=5001, window=0)
        lanes, reason = reference.data_admission(original, reply, segment)
        self.assertIsNone(reason)
        self.assertEqual(lanes[1].peer_window, 0)
        reply = reference.replace(reply, acknowledged=1, peer_window=8)
        lanes, reason = reference.data_admission(original, reply, segment)
        self.assertIsNone(reason)
        self.assertEqual(lanes[1].peer_window, 8)

    def test_admission_zero_window_denies_data_but_accepts_empty_ack(self):
        state, _ = self.startup()
        segment = reference.wire.decode_packet(
            reference.handshake.control_output(self.client, self.public, 1001, 5001, 16)[
                "rawIPv4Hex"
            ]
        ).segment
        sender = reference.replace(state.original, peer_window=0)
        _, reason = reference.data_admission(
            sender, state.reply, reference.replace(segment, payload=b"a")
        )
        self.assertEqual(reason, "window")
        lanes, reason = reference.data_admission(sender, state.reply, segment)
        self.assertIsNone(reason)
        self.assertEqual(lanes[0].observed, 0)

    def test_admission_uses_serial_coordinates_across_wrap(self):
        sender = reference.Lane(0xFFFFFFFF, 1, 0, 8, 42, 0xFFFFFFFF)
        peer = reference.Lane(43, 0, 0, 8, 0xFFFFFFFF, 43)
        segment = reference.wire.decode_packet(
            reference.handshake.control_output(self.client, self.public, 0, 43, 16)["rawIPv4Hex"]
        ).segment
        lanes, reason = reference.data_admission(
            sender, peer, reference.replace(segment, payload=b"a")
        )
        self.assertIsNone(reason)
        self.assertEqual(lanes[0].next, 1)

    def test_admission_cannot_retain_a_missing_confirmed_binding(self):
        state, records = self.startup()
        _, reason = reference.commit_admission(state, records[0], False, ())
        self.assertEqual(reason, "historyLost")

    def test_forward_comparison_uses_predicates_across_all_tracker_states(self):
        allowed = [row["match"] for row in self.requirements["requirements"]]
        source = self.configs["permit"]["forward"]
        self.assertTrue(reference.forward_equivalent(json.dumps(source), json.dumps(allowed)))
        changed = copy.deepcopy(source)
        rule = next(item["rule"] for item in changed["nftables"] if "rule" in item)
        rule["expr"].insert(
            0, {"match": {"left": {"ct": {"key": "state"}}, "op": "==", "right": "established"}}
        )
        self.assertFalse(reference.forward_equivalent(json.dumps(changed), json.dumps(allowed)))

    def test_ingress_comparison_uses_the_actual_numeric_rules(self):
        guards = {row["id"]: row["source"] for row in reference.load("guards")}
        specifications = reference.load("specifications")
        self.assertTrue(
            reference.ingress_equivalent(json.dumps(guards["permit"]), json.dumps(specifications))
        )
        self.assertTrue(reference.ingress_equivalent(json.dumps(guards["deny"]), "[]"))
        changed = copy.deepcopy(guards["permit"])
        rule = next(item["rule"] for item in changed["ruleset"]["nftables"] if "rule" in item)
        rule["expr"][0]["match"]["right"] = "server0"
        self.assertFalse(
            reference.ingress_equivalent(json.dumps(changed), json.dumps(specifications))
        )

    def test_ingress_comparison_includes_unbound_numeric_rule_indices(self):
        guards = {row["id"]: row["source"] for row in reference.load("guards")}
        source = copy.deepcopy(guards["deny"])
        source["ruleset"]["nftables"].append(
            {
                "rule": {
                    "family": "ip",
                    "table": "campus_ingress",
                    "chain": "ingress",
                    "handle": 3,
                    "expr": [
                        {"match": {"op": "==", "left": {"meta": {"key": "iif"}}, "right": 123}},
                        {"accept": None},
                    ],
                }
            }
        )
        self.assertFalse(reference.ingress_equivalent(json.dumps(source), "[]"))

    def test_supported_native_predicate_spellings_have_the_same_meaning(self):
        header = reference.wire.Header("192.0.2.2", "198.51.100.2", 6, 41000, 9000)
        rows = [
            ({"meta": {"key": "l4proto"}}, "==", "tcp", "new"),
            ({"payload": {"protocol": "ip", "field": "protocol"}}, "==", 6, "new"),
            ({"ct": {"key": "state"}}, "==", 8, "new"),
            ({"ct": {"key": "state"}}, "in", 10, "established"),
            ({"payload": {"protocol": "ip", "field": "saddr"}}, "==", "192.0.2.0/24", "new"),
            (
                {"payload": {"protocol": "ip", "field": "saddr"}},
                "==",
                {"prefix": {"addr": "192.0.2.2", "len": 24}},
                "new",
            ),
        ]
        for left, operator, right, classification in rows:
            with self.subTest(left=left, right=right):
                expression = {"match": {"left": left, "op": operator, "right": right}}
                self.assertTrue(reference.expression_match(expression, header, classification))

    def test_eap_inner_padding_does_not_change_the_decoded_method_packet(self):
        raw = bytes.fromhex(self.authentication["events"][1]["raw"])
        padded = raw[:16] + (8).to_bytes(2, "big") + raw[18:] + b"\x00\x01"
        self.assertEqual(
            reference.eap_frame(self.authentication["link"], padded.hex()),
            reference.eap_frame(self.authentication["link"], raw.hex()),
        )


def projection(report):
    return {
        **{
            key: report[key]
            for key in (
                "supported",
                "compliant",
                "evaluatedEvents",
                "final",
                "outputs",
                "services",
                "reads",
                "remainingEvents",
            )
        },
        "decisions": [step["decision"] for step in report["steps"]],
    }


class FixtureTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.cases = json.loads(reference.FIXTURES.read_text())["cases"]

    def test_frozen_independent_expectations(self):
        for case in self.cases:
            with self.subTest(case=case["id"]):
                self.assertEqual(projection(reference.replay(case["input"])), case["expected"])

    def test_byte_path_audit_uses_actual_earlier_outputs_and_receipts(self):
        for case in self.cases:
            with self.subTest(case=case["id"]):
                comparison.audit_bytes(reference.replay(case["input"]), case["id"])
        report = reference.replay(self.cases[0]["input"])
        report["services"][3]["inputHex"] = report["outputs"][0]["rawIPv4Hex"]
        with self.assertRaisesRegex(AssertionError, "immutable bytes"):
            comparison.audit_bytes(report, "replaced source")

    def test_native_source_spellings_and_eap_padding_preserve_the_trace(self):
        case = self.cases[0]
        report = reference.replay(comparison.native_spellings(case["input"]))
        self.assertEqual(projection(report), case["expected"])

    def test_received_bytes_remain_readable_after_logoff_and_current_denial(self):
        value = next(
            case["input"]
            for case in self.cases
            if case["id"] == "received-bytes-remain-readable-after-logoff"
        )
        report = reference.replay(value)
        self.assertTrue(report["supported"])
        self.assertTrue(report["compliant"])
        self.assertEqual(report["final"]["after"], 8)
        self.assertEqual(report["final"]["configuration"], "deny")
        self.assertEqual(report["final"]["guard"], "deny")
        read = report["steps"][-1]
        self.assertEqual(read["event"], {"kind": "read", "actor": "server", "count": 3})
        self.assertEqual(read["before"]["server"]["core"]["receivedHex"], "616263")
        self.assertEqual(read["readHex"], "616263")
        self.assertEqual(read["state"]["server"]["core"]["receivedHex"], "")
        service = report["services"][-1]
        self.assertLess(service["index"], read["index"])
        self.assertTrue(all(service["checks"].values()))

    def test_dropped_synack_retains_the_actual_reply_and_gate_history(self):
        value = next(
            case["input"]
            for case in self.cases
            if case["id"] == "dropped-synack-retains-reply-and-admission-history"
        )
        report = reference.replay(value)
        self.assertTrue(report["supported"])
        self.assertTrue(report["compliant"])
        self.assertEqual(report["final"]["admissionPhase"], "synAck")
        self.assertEqual(report["final"]["admissionObservations"], 2)
        self.assertEqual(len(report["final"]["records"]), 1)
        self.assertTrue(report["final"]["records"][0]["seenReply"])
        self.assertEqual(report["final"]["activePhase"], "SYN-SENT")
        self.assertEqual(report["final"]["passivePhase"], "SYN-RECEIVED")
        self.assertIsNone(report["final"]["client"])
        self.assertIsNone(report["final"]["server"])
        service = report["services"][-1]
        self.assertEqual(service["disposition"], "lateDrop")
        self.assertEqual(service["direction"], "reply")
        self.assertIsNone(service["output"])

    def test_failed_install_comparisons_are_supported_actual_state_changes(self):
        value = copy.deepcopy(self.cases[0]["input"])
        value["events"] = [
            {"kind": "install", "configuration": "permit"},
            {"kind": "installGuard", "guard": "permit"},
        ]
        report = reference.replay(value)
        self.assertTrue(report["supported"])
        self.assertFalse(report["compliant"])
        for step in report["steps"]:
            self.assertTrue(step["supported"])
            self.assertFalse(step["passed"])
            self.assertEqual(step["decision"]["kind"], "accepted")
        self.assertEqual(report["final"]["configuration"], "permit")
        self.assertEqual(report["final"]["guard"], "permit")

    def test_unsupported_rows_do_not_imply_a_failed_comparison(self):
        for case in self.cases:
            report = reference.replay(case["input"])
            if not report["supported"]:
                with self.subTest(case=case["id"]):
                    last = report["steps"][-1]
                    self.assertFalse(last["supported"])
                    self.assertTrue(last["passed"])
                    self.assertEqual(last["decision"]["kind"], "unsupported")

    def test_assurance_counts_follow_actual_operations_and_receipts(self):
        report = reference.replay(self.cases[0]["input"])
        self.assertEqual(
            comparison.expected_assurance(report),
            {
                "status": "checked",
                "startupReceipts": 3,
                "clientWrittenBytes": 6,
                "serverWrittenBytes": 3,
                "clientReadBytes": 3,
                "serverReadBytes": 3,
                "clientReceives": 1,
                "serverReceives": 2,
            },
        )
        buffered = next(
            case
            for case in self.cases
            if case["id"] == "received-bytes-remain-readable-after-logoff"
        )
        status = comparison.expected_assurance(reference.replay(buffered["input"]))
        self.assertEqual(status["status"], "checked")
        self.assertEqual(status["serverReadBytes"], 3)
        self.assertEqual(status["serverReceives"], 1)
        self.assertEqual(status["clientWrittenBytes"], 3)

    def test_assurance_does_not_claim_checked_startup_or_failed_comparisons(self):
        pending = next(
            case
            for case in self.cases
            if case["id"] == "dropped-synack-retains-reply-and-admission-history"
        )
        self.assertEqual(
            comparison.expected_assurance(reference.replay(pending["input"])),
            {"status": "pendingStartup"},
        )
        for case in self.cases:
            if not case["expected"]["compliant"]:
                with self.subTest(case=case["id"]):
                    self.assertEqual(
                        comparison.expected_assurance(reference.replay(case["input"])),
                        {"status": "failed"},
                    )

    def test_authorized_reads_have_actual_prior_packet_emissions(self):
        report = reference.replay(self.cases[0]["input"])
        self.assertTrue(report["compliant"])
        self.assertEqual(
            [(row["actor"], row["readHex"]) for row in report["reads"]],
            [("server", "616263"), ("client", "78797a")],
        )
        self.assertEqual(report["final"]["activeEstablishedAt"], 17)
        self.assertEqual(report["final"]["passiveEstablishedAt"], 20)
        self.assertEqual(len(report["final"]["records"]), 1)
        self.assertTrue(report["final"]["records"][0]["seenReply"])
        self.assertEqual(report["services"][-1]["disposition"], "earlyDrop")
        self.assertEqual(report["final"]["admissionObservations"], 6)

    def test_stale_allow_after_logoff_preserves_computed_bytes(self):
        report = reference.replay(self.cases[1]["input"])
        self.assertTrue(report["supported"])
        self.assertFalse(report["compliant"])
        last = report["services"][-1]
        self.assertFalse(last["checks"]["forward"])
        self.assertFalse(last["checks"]["ingress"])
        self.assertEqual(last["disposition"], "forwarded")
        self.assertEqual(last["output"]["decoded"]["segment"]["payloadHex"], "646566")

    def test_delivery_cannot_replace_the_computed_emission(self):
        value = copy.deepcopy(self.cases[0]["input"])
        next(event for event in value["events"] if event["kind"] == "deliver")["rawIPv4Hex"] = "00"
        with self.assertRaisesRegex(ValueError, "actual earlier service emission"):
            reference.replay(value)

    def test_service_consumes_the_immutable_ticket_once(self):
        value = copy.deepcopy(self.cases[0]["input"])
        value["events"] = value["events"][:14] + [{"kind": "serve", "ticket": 0, "observed": None}]
        with self.assertRaisesRegex(ValueError, "pending immutable ticket"):
            reference.replay(value)

    def test_startup_copy_stops_before_later_events(self):
        value = copy.deepcopy(
            next(
                case["input"]
                for case in self.cases
                if case["id"] == "startup-copy-stops-before-application-receive"
            )
        )
        value["events"].append({"kind": "read", "actor": "server", "count": 0})
        report = reference.replay(value)
        self.assertFalse(report["supported"])
        self.assertEqual(
            report["steps"][-1]["decision"], {"kind": "unsupported", "reason": "startupCopy"}
        )
        self.assertEqual(
            report["remainingEvents"], [{"kind": "read", "actor": "server", "count": 0}]
        )

    def test_an_open_after_startup_cannot_create_an_application_origin(self):
        value = copy.deepcopy(self.cases[0]["input"])
        value["events"] = value["events"][:21] + [copy.deepcopy(value["events"][11])]
        report = reference.replay(value)
        self.assertEqual(
            report["steps"][-1]["decision"], {"kind": "unsupported", "reason": "startupCopy"}
        )


if __name__ == "__main__":
    unittest.main()
