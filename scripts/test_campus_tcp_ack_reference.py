"""Independent tests for ACK reactions and receiver window suppression."""

import copy
import json
import unittest
from pathlib import Path

import campus_tcp_ack_reference as reference
import check_tcp_ack_examples as comparison


class ReceiveWindowTests(unittest.TestCase):
    def test_receive_keeps_the_offered_right_edge_fixed(self):
        initial = reference.ReceiveWindow.initial(4096, 800)
        after = initial.receive(1200)
        self.assertEqual((after.frontier, after.edge, after.width), (1200, 4096, 2896))
        self.assertEqual((after.free, after.withheld), (2896, 0))
        self.assertTrue(after.valid)

    def test_small_reads_stay_hidden_on_every_output(self):
        received = reference.ReceiveWindow.initial(4096, 800).receive(1200)
        small = received.read(799)
        self.assertEqual((small.free, small.width, small.withheld), (3695, 2896, 799))
        self.assertEqual(small.output_width, 2896)
        self.assertEqual(small.commit_output(), small)
        self.assertFalse(small.window_update)

    def test_threshold_uses_own_outgoing_mss_and_commits_only_on_output(self):
        client = reference.ReceiveWindow.initial(4096, 800).receive(1200).read(800)
        server = reference.ReceiveWindow.initial(4096, 1200).receive(1200).read(800)
        self.assertEqual((client.threshold, server.threshold), (800, 1200))
        self.assertEqual((client.output_width, server.output_width), (3696, 2896))
        self.assertEqual(client.edge, 4096)
        emitted = client.commit_output()
        self.assertEqual((emitted.edge, emitted.width, emitted.withheld), (4896, 3696, 0))
        self.assertTrue(client.window_update)
        self.assertFalse(emitted.window_update)

    def test_half_buffer_threshold_rounds_up(self):
        initial = reference.ReceiveWindow.initial(9, 800).receive(9)
        four = initial.read(4)
        self.assertEqual(four.threshold, 5)
        self.assertEqual(four.output_width, 0)
        five = four.read(1)
        self.assertEqual(five.output_width, 5)
        self.assertEqual(five.commit_output().edge, 14)

    def test_zero_length_read_and_zero_capacity_grant_no_growth(self):
        received = reference.ReceiveWindow.initial(4096, 800).receive(800)
        self.assertEqual(received.read(0), received)
        empty = reference.ReceiveWindow.initial(0, 800)
        self.assertEqual(empty.threshold, 0)
        self.assertEqual(empty.output_width, 0)
        self.assertFalse(empty.window_update)
        self.assertEqual(empty.commit_output(), empty)

    def test_zero_window_reopens_at_the_accumulated_threshold(self):
        full = reference.ReceiveWindow.initial(4096, 1200).receive(4096)
        self.assertEqual((full.width, full.free), (0, 0))
        small = full.read(1)
        self.assertEqual((small.width, small.free, small.output_width), (0, 1, 0))
        ready = small.read(1199)
        self.assertEqual((ready.width, ready.free, ready.output_width), (0, 1200, 1200))
        reopened = ready.commit_output()
        self.assertEqual((reopened.width, reopened.free, reopened.edge), (1200, 1200, 5296))

    def test_new_data_cannot_use_space_withheld_after_a_read(self):
        state = reference.ReceiveWindow.initial(8, 800).receive(8).read(3)
        self.assertEqual(state.free, 3)
        with self.assertRaisesRegex(ValueError, "offered"):
            state.receive(1)
        opened = state.read(1).commit_output()
        self.assertEqual(opened.receive(4).width, 0)

    def test_receiving_while_update_pending_preserves_withheld_credit(self):
        ready = reference.ReceiveWindow.initial(4096, 800).receive(1200).read(800)
        later = ready.receive(400)
        self.assertEqual((later.width, later.free, later.withheld), (2496, 3296, 800))
        emitted = later.commit_output()
        self.assertEqual((emitted.edge, emitted.width, emitted.withheld), (4896, 3296, 0))

    def test_serial_projection_wraps_without_moving_the_coordinate_edge(self):
        base = (1 << 32) - 32
        state = reference.ReceiveWindow.initial(4096, 800).receive(1200).read(800)
        self.assertEqual(state.sequence(base), 1168)
        self.assertEqual(state.right_edge(base), 4064)
        emitted = state.commit_output()
        self.assertEqual(emitted.right_edge(base), 4864)
        self.assertEqual(emitted.frontier, state.frontier)

    def test_invalid_counts_and_configurations_are_rejected(self):
        for capacity, smss in ((-1, 800), (65536, 800), (4096, 0)):
            with self.subTest(capacity=capacity, smss=smss):
                with self.assertRaises(ValueError):
                    reference.ReceiveWindow.initial(capacity, smss)
        initial = reference.ReceiveWindow.initial(9, 800)
        for operation, count in ((initial.receive, -1), (initial.read, 1)):
            with self.assertRaises(ValueError):
                operation(count)


class ReactionTests(unittest.TestCase):
    def test_coalescing_preserves_the_first_deadline(self):
        first = reference.Reaction().issue(100, 800, 499)
        second = first.issue(200, 1200, 499)
        self.assertEqual(second.deadline, 599)
        self.assertEqual([cause.id for cause in second.pending], [0, 1])
        self.assertEqual([cause.demand for cause in second.pending], [800, 1200])
        self.assertEqual(second.pending[0], first.pending[0])

    def test_one_output_retires_every_covered_cause(self):
        issued = reference.Reaction().issue(100, 400, 499).issue(120, 800, 0)
        completed = issued.complete(120, 7, 800)
        self.assertEqual(completed.pending, ())
        self.assertIsNone(completed.deadline)
        self.assertEqual(completed.next_id, 2)
        self.assertEqual(completed.completed[0].output, 7)
        self.assertEqual(completed.completed[0].causes, issued.pending)
        with self.assertRaisesRegex(ValueError, "noCredit"):
            completed.complete(120, 8, 800)

    def test_last_permitted_millisecond_passes_but_the_next_fails(self):
        issued = reference.Reaction().issue(100, 800, 499)
        self.assertEqual(issued.complete(599, 7, 800).completed[0].time, 599)
        with self.assertRaisesRegex(ValueError, "deadline"):
            issued.complete(600, 7, 800)
        with self.assertRaisesRegex(ValueError, "clock"):
            issued.complete(99, 7, 800)

    def test_actual_output_must_cover_each_cumulative_demand(self):
        issued = reference.Reaction().issue(100, 400, 499).issue(120, 800, 499)
        with self.assertRaisesRegex(ValueError, "coverage"):
            issued.complete(200, 7, 799)
        self.assertEqual(len(issued.complete(200, 7, 800).completed), 1)

    def test_an_immediate_cause_tightens_the_existing_group(self):
        delayed = reference.Reaction().issue(100, 800, 499)
        duplicate = delayed.issue(200, 800, 0)
        self.assertEqual(duplicate.deadline, 200)
        with self.assertRaisesRegex(ValueError, "deadline"):
            duplicate.complete(201, 7, 800)
        self.assertEqual(len(duplicate.complete(200, 7, 800).completed[0].causes), 2)

    def test_new_credit_after_discharge_gets_distinct_identities(self):
        first = reference.Reaction().issue(100, 800, 499).complete(200, 7, 800)
        later = first.issue(300, 1600, 499).complete(400, 8, 1600)
        self.assertEqual([row.id for row in later.completed], [0, 1])
        self.assertEqual([row.causes[0].id for row in later.completed], [0, 1])
        self.assertEqual(later.next_discharge, 2)


class OfferedReceiveTests(unittest.TestCase):
    def setUp(self):
        self.core = reference.wire.State(
            reference.wire.Header("192.0.2.1", "192.0.2.2", 6, 4000, 8080),
            1000,
            16,
            b"abcdefgh",
            2000,
            2000,
            b"",
        )

    def packet(self, sequence=1000, acknowledgment=2000, payload=b""):
        return reference.wire.Packet(
            self.core.inbound,
            reference.wire.Segment(sequence, acknowledgment, 16, payload=payload),
        )

    def test_physical_free_space_does_not_expand_the_offered_interval(self):
        result = reference.receive_offered(self.core, self.packet(sequence=1004), 4)
        self.assertEqual(result.decision, {"kind": "reject", "reason": "sequence"})
        self.assertEqual(result.ack["window"], 4)
        self.assertEqual(result.state, self.core)

    def test_right_overrun_stops_before_partial_delivery(self):
        result = reference.receive_offered(self.core, self.packet(payload=b"12345"), 4)
        self.assertEqual(result.decision, {"kind": "unsupported", "reason": "trimming"})
        self.assertEqual(result.state, self.core)
        bad_ack = reference.receive_offered(
            self.core, self.packet(acknowledgment=3000, payload=b"12345"), 4
        )
        self.assertEqual(bad_ack.decision, {"kind": "reject", "reason": "acknowledgment"})
        self.assertEqual(bad_ack.ack["window"], 4)

    def test_supported_data_request_uses_remaining_offered_width(self):
        result = reference.receive_offered(self.core, self.packet(payload=b"123"), 4)
        self.assertEqual(result.decision, {"kind": "accepted", "acknowledged": 0, "received": 3})
        self.assertEqual(result.state.received, b"abcdefgh123")
        self.assertEqual(result.state.window, 5)
        self.assertEqual(result.ack["window"], 1)

    def test_zero_offered_window_accepts_pure_ack_without_creating_feedback(self):
        accepted = reference.receive_offered(self.core, self.packet(), 0)
        self.assertEqual(accepted.decision["kind"], "accepted")
        self.assertIsNone(accepted.ack)
        old = reference.receive_offered(self.core, self.packet(sequence=999, payload=b"x"), 0)
        self.assertEqual(old.decision, {"kind": "reject", "reason": "sequence"})
        self.assertEqual(old.ack["window"], 0)


class AckRuleTests(unittest.TestCase):
    def test_partial_segments_coalesce_without_postponing_the_first_due(self):
        state = reference.AckState.initial(1000, 4096, 1200, 800)
        first = state.receive_data(100, 1400, 400)
        second = first.receive_data(150, 1800, 400)
        self.assertEqual((second.full_segments, second.data_bytes), (0, 800))
        self.assertEqual(second.work.deadline, 599)
        self.assertEqual(len(second.work.pending), 2)
        output = second.complete(200, 1800)
        self.assertEqual(len(output.work.completed[0].causes), 2)
        self.assertEqual(output.work.completed[0].output.cursor, 1800)
        self.assertEqual((output.full_segments, output.data_bytes), (0, 0))

    def test_rmss_sized_second_packet_requests_immediate_feedback(self):
        state = reference.AckState.initial(1000, 4096, 1200, 800)
        second = state.receive_data(100, 1800, 800).receive_data(150, 2600, 800)
        self.assertEqual((second.full_segments, second.data_bytes), (2, 1600))
        self.assertEqual(second.work.deadline, 150)
        self.assertEqual(second.complete(150, 2600).window.edge, 4096)

    def test_byte_threshold_uses_own_receive_offer(self):
        state = reference.AckState.initial(1000, 4096, 800, 1200)
        two = state.receive_data(100, 1800, 800).receive_data(150, 2600, 800)
        self.assertEqual((two.full_segments, two.data_bytes, two.work.deadline), (0, 1600, 599))
        third = two.receive_data(200, 3400, 800)
        self.assertEqual(
            (third.full_segments, third.data_bytes, third.work.deadline), (0, 2400, 200)
        )

    def test_actual_read_grants_only_new_candidate_growth(self):
        received = reference.AckState.initial(1000, 4096, 800, 1200).receive_data(100, 2200, 1200)
        small = received.read(150, 2200, 799)
        self.assertEqual(len(small.work.pending), 1)
        opened = small.read(150, 2200, 1)
        self.assertEqual(len(opened.work.pending), 2)
        self.assertEqual(opened.work.pending[-1].demand.kind, "window")
        self.assertEqual(opened.work.pending[-1].demand.minimum_edge, 4896)
        self.assertEqual(opened.work.deadline, 150)
        self.assertEqual(opened.read(150, 2200, 0), opened)
        emitted = opened.complete(150, 2200)
        self.assertEqual(emitted.window.width, 3696)
        self.assertEqual(emitted.work.completed[0].output.window, 3696)

    def test_old_sequence_cause_does_not_advance_receive_position(self):
        state = reference.AckState.initial(1000, 4096, 1200, 800)
        received = state.receive_data(100, 1800, 800).complete(200, 1800)
        repeated = received.receive_sequence(300, 1800)
        self.assertEqual(repeated.window, received.window)
        self.assertEqual(repeated.work.deadline, 300)
        self.assertEqual(repeated.work.pending[0].demand.kind, "sequence")
        self.assertEqual(repeated.work.pending[0].demand.bytes, 0)


class EndpointTests(unittest.TestCase):
    def setUp(self):
        core = reference.wire.State(
            reference.wire.Header("192.0.2.1", "192.0.2.2", 6, 4000, 8080),
            1000,
            4096,
            b"",
            2000,
            2000,
            b"",
        )
        self.initial = reference.Endpoint(
            core, b"", 4096, 4096, 1000, 2000, 800, 1000, local_receive_mss=1200
        )
        recovered = reference.evaluate(self.initial, {"kind": "enableRecovery"}).state
        self.enabled = reference.evaluate(recovered, {"kind": "enableAck"}).state

    def incoming(self, state, payload=b"", sequence=None, acknowledgment=2000):
        segment = reference.wire.Segment(
            state.core.receive_next if sequence is None else sequence,
            acknowledgment,
            16,
            window=4096,
            payload=payload,
        )
        raw = reference.wire.fixture_packet(state.core.inbound, segment)
        return reference.evaluate(state, {"kind": "receive", "rawIPv4Hex": raw.hex()})

    def test_dispatch_uses_actual_credit_and_the_last_permitted_clock(self):
        received = self.incoming(self.enabled, b"x" * 1200).state
        early = reference.evaluate(received, {"kind": "dispatchAck", "policyPermitted": True})
        self.assertEqual(early.decision, {"kind": "reject", "reason": "ack.early"})
        due = reference.evaluate(received, {"kind": "advanceClock", "millis": 499}).state
        sent = reference.evaluate(due, {"kind": "dispatchAck", "policyPermitted": True})
        packet = reference.wire.decode_packet(sent.output["rawIPv4Hex"])
        self.assertEqual((packet.segment.acknowledgment, packet.segment.window), (2200, 2896))
        self.assertEqual(sent.state.ack_state.work.pending, ())
        extra = reference.evaluate(sent.state, {"kind": "emitAck", "policyPermitted": True})
        self.assertEqual(extra.decision, {"kind": "reject", "reason": "ack.noCredit"})
        self.assertIsNone(extra.output)

    def test_deadline_jump_and_local_denial_preserve_the_owed_group(self):
        received = self.incoming(self.enabled, b"x" * 1200).state
        late = reference.evaluate(received, {"kind": "advanceClock", "millis": 500})
        self.assertEqual(late.decision, {"kind": "unsupported", "reason": "ack.deadline"})
        self.assertEqual(late.state, received)
        denied = reference.evaluate(received, {"kind": "dispatchAck", "policyPermitted": False})
        self.assertEqual(denied.decision, {"kind": "reject", "reason": "policy"})
        self.assertEqual(denied.state, received)

    def test_piggyback_uses_suppressed_window_and_retires_the_same_credit(self):
        received = self.incoming(self.enabled, b"x" * 1200).state
        read = reference.evaluate(received, {"kind": "read", "count": 799}).state
        written = reference.evaluate(read, {"kind": "write", "payloadHex": "79" * 800}).state
        sent = reference.evaluate(written, {"kind": "send", "count": 800, "policyPermitted": True})
        packet = reference.wire.decode_packet(sent.output["rawIPv4Hex"])
        self.assertEqual(packet.segment.window, 2896)
        self.assertEqual(sent.state.core.window, 3695)
        self.assertEqual(sent.state.ack_state.work.pending, ())
        self.assertEqual(sent.state.recovery.flight, 800)

    def test_whole_duplicate_issues_immediate_feedback_without_new_bytes(self):
        received = self.incoming(self.enabled, b"x" * 1200).state
        answered = reference.evaluate(received, {"kind": "emitAck", "policyPermitted": True}).state
        repeated = self.incoming(answered, b"x" * 1200, sequence=1000)
        self.assertEqual(repeated.decision, {"kind": "reject", "reason": "input.sequence"})
        self.assertEqual(repeated.state.core, answered.core)
        self.assertEqual(repeated.state.ack_state.work.deadline, 0)
        reply = reference.evaluate(repeated.state, {"kind": "dispatchAck", "policyPermitted": True})
        self.assertIsNotNone(reply.output)
        self.assertEqual(reply.state.core.received, b"x" * 1200)

    def test_pure_ack_has_no_response_cause_and_challenge_is_a_scope_stop(self):
        pure = self.incoming(self.enabled)
        self.assertEqual(pure.state.ack_state.work.pending, ())
        challenge = self.incoming(self.enabled, acknowledgment=3000)
        self.assertEqual(challenge.decision, {"kind": "unsupported", "reason": "ack.challenge"})
        self.assertEqual(challenge.state, self.enabled)

    def test_recovery_clock_is_required_and_own_offer_is_derived(self):
        missing = reference.evaluate(self.initial, {"kind": "enableAck"})
        self.assertEqual(missing.decision, {"kind": "reject", "reason": "ack.disabled"})
        self.assertEqual(self.enabled.ack_state.rmss, 1200)
        self.assertEqual(self.enabled.ack_state.window.outgoing_mss, 800)


class DriverTests(unittest.TestCase):
    def test_actual_dispatch_output_is_deliverable_in_both_campus_variants(self):
        original = json.loads(
            (
                Path(__file__).resolve().parent.parent / "examples/tcp-recovery/trace.json"
            ).read_text()
        )
        for standby in (False, True):
            with self.subTest(standby=standby):
                value = copy.deepcopy(original)
                events = value["events"] = value["events"][:25]
                if not standby:
                    del value["standby"]
                    events[:] = [row for row in events if row.get("gateway") != "standby"]
                for kind in ("enableRecovery", "enableAck"):
                    for actor in ("client", "server"):
                        events.append({"kind": kind, "actor": actor})
                ingress = {row["id"]: row["ingress"] for row in value["specifications"]}

                def deliver(service):
                    report = reference.replay(value)
                    events.append(
                        {
                            "kind": "deliver",
                            "service": service,
                            "rawIPv4Hex": report["services"][service]["output"]["rawIPv4Hex"],
                            "policyPermitted": True,
                        }
                    )

                events.extend(
                    [
                        {"kind": "write", "actor": "client", "payloadHex": "61"},
                        {"kind": "send", "actor": "client", "count": 1, "policyPermitted": True},
                        {"kind": "assign", "output": 3, "ingress": ingress["client"]},
                        {"kind": "serve", "ticket": 3, "observed": None},
                    ]
                )
                deliver(3)
                for actor in ("client", "server"):
                    events.append({"kind": "advanceClock", "actor": actor, "millis": 499})
                events.extend(
                    [
                        {"kind": "dispatchAck", "actor": "server", "policyPermitted": True},
                        {"kind": "assign", "output": 4, "ingress": ingress["server"]},
                        {"kind": "serve", "ticket": 4, "observed": None},
                    ]
                )
                deliver(4)
                report = reference.replay(value)
                self.assertEqual(report["services"][-1]["sourceKind"], "dispatchAck")
                self.assertTrue(report["supported"])
                self.assertEqual(report["final"]["client"]["core"]["sentHex"], "")


class CampusTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.data = reference.load_fixtures()
        cls.report = reference.replay(cls.data["input"])
        cls.cases = {row["id"]: row for row in cls.data["cases"]}

    def step(self, label):
        return self.report["steps"][self.data["labels"][label]]

    def test_frozen_expectations_and_actual_cause_audit(self):
        for case in self.data["cases"]:
            with self.subTest(case=case["id"]):
                report = reference.replay(case["input"])
                self.assertEqual(reference.projection(report), case["expected"])
                comparison.audit(report, case["id"])

    def test_partial_causes_coalesce_and_actual_data_output_discharges_both(self):
        first = self.step("a-first-receipt")["state"]["server"]["ackReaction"]
        second = self.step("a-second-receipt")["state"]["server"]["ackReaction"]
        self.assertEqual((first["work"]["pendingDue"], second["work"]["pendingDue"]), (599, 599))
        self.assertEqual((second["work"]["credit"], second["dataBytes"]), (2, 800))
        piggyback = self.step("b-piggyback")["state"]["server"]["ackReaction"]
        self.assertEqual(piggyback["work"]["pending"], [])
        self.assertEqual(len(piggyback["work"]["completed"][0]["causes"]), 2)
        self.assertEqual(piggyback["work"]["completed"][0]["time"], 150)

    def test_transfer_preserves_the_actual_local_obligation_and_deadline(self):
        installed = self.step("install")
        self.assertEqual(installed["before"]["client"], installed["state"]["client"])
        pending = installed["state"]["client"]["ackReaction"]["work"]
        self.assertEqual((pending["credit"], pending["pendingDue"]), (1, 649))
        self.assertEqual(
            self.step("stale-stage")["state"]["transfer"]["cache"]["historyTransitions"], 6
        )
        self.assertEqual(installed["state"]["transfer"]["installation"]["historyTransitions"], 7)
        self.assertEqual(self.step("ack-b")["before"]["client"]["recovery"]["now"], 649)

    def test_retry_feedback_does_not_duplicate_application_bytes(self):
        for actor, label, count in (
            ("server", "c-duplicate-receipt", 1600),
            ("client", "d-duplicate-receipt", 2400),
        ):
            step = self.step(label)
            self.assertEqual(step["decision"], {"kind": "reject", "reason": "input.sequence"})
            self.assertEqual(step["before"][actor]["core"], step["state"][actor]["core"])
            self.assertEqual(len(bytes.fromhex(step["state"][actor]["core"]["receivedHex"])), count)
            pending = step["state"][actor]["ackReaction"]["work"]
            self.assertEqual(pending["pendingDue"], step["before"][actor]["recovery"]["now"])
        self.assertEqual(self.report["final"]["client"]["recovery"]["frontier"], 1600)
        self.assertEqual(self.report["final"]["server"]["recovery"]["frontier"], 3600)

    def test_small_reads_stay_hidden_on_data_and_pure_ack_outputs(self):
        sent = self.step("f-suppressed-window")
        self.assertEqual(sent["before"]["server"]["core"]["window"], 3695)
        self.assertEqual(sent["output"]["decoded"]["segment"]["window"], 2496)
        opening = self.step("server-threshold-read")["state"]["server"]["ackReaction"]
        self.assertEqual(opening["work"]["pending"][0]["demand"]["kind"], "window")
        self.assertEqual(opening["advertisement"]["candidate"], 3696)
        denied = self.step("ack-f-denied")
        self.assertEqual(denied["before"]["client"]["core"]["window"], 1295)
        self.assertEqual(denied["output"]["decoded"]["segment"]["window"], 496)

    def test_current_denial_preserves_local_generation_and_buffered_reads(self):
        self.assertEqual(self.report["evaluatedEvents"], 153)
        self.assertEqual((len(self.report["outputs"]), len(self.report["services"])), (21, 22))
        self.assertEqual(
            [row["disposition"] for row in self.report["services"][-2:]], ["earlyDrop"] * 2
        )
        self.assertTrue(all(row["output"] is None for row in self.report["services"][-2:]))
        self.assertGreater(
            self.data["labels"]["client-buffered-read"], self.data["labels"]["logoff"]
        )
        reads = {actor: b"" for actor in ("client", "server")}
        for row in self.report["reads"]:
            reads[row["actor"]] += bytes.fromhex(row["readHex"])

        def pattern(start, count):
            return bytes((start + index) % 251 for index in range(count))

        self.assertEqual(reads["server"], pattern(17, 800) + pattern(33, 800))
        self.assertEqual(
            reads["client"], pattern(81, 1200) + pattern(97, 1200) + pattern(113, 1200)
        )
        self.assertEqual(self.report["final"]["server"]["recovery"]["flight"], 1200)
        for actor, count in (("client", 5), ("server", 4)):
            work = self.report["final"][actor]["ackReaction"]["work"]
            self.assertEqual((work["nextID"], work["nextDischarge"], work["credit"]), (5, count, 0))

    def test_zero_window_response_then_actual_read_origin_reopening(self):
        report = reference.replay(self.cases["zero-window-response-and-sws-reopening"]["input"])
        server = report["final"]["server"]
        self.assertEqual(server["ackReaction"]["advertisement"]["window"], 200)
        self.assertEqual(report["final"]["client"]["sendWindow"], 200)
        self.assertEqual(len(bytes.fromhex(server["core"]["receivedHex"])), 200)
        self.assertEqual(
            [row["output"]["window"] for row in server["ackReaction"]["work"]["completed"]],
            [0, 0, 200],
        )

    def test_ack_dispatch_and_rto_share_actual_credit_without_duplicate_response(self):
        for name in (
            "ack-dispatch-preserves-due-rto",
            "retry-piggyback-discharges-before-dispatch",
        ):
            report = reference.replay(self.cases[name]["input"])
            timeout = next(row for row in report["steps"] if row["event"]["kind"] == "timeout")
            self.assertEqual(
                timeout["state"]["client"]["core"], timeout["before"]["client"]["core"]
            )
            self.assertEqual(timeout["state"]["client"]["recovery"]["rto"], 2000)
            self.assertEqual(timeout["state"]["client"]["recovery"]["deadline"], 3500)
            self.assertEqual(
                report["steps"][-1]["decision"], {"kind": "reject", "reason": "ack.noCredit"}
            )
            if name == "ack-dispatch-preserves-due-rto":
                dispatch = next(
                    row for row in report["steps"] if row["event"]["kind"] == "dispatchAck"
                )
                self.assertEqual(
                    dispatch["before"]["client"]["recovery"],
                    dispatch["state"]["client"]["recovery"],
                )

    def test_activation_input_errors_use_actual_history_even_after_supported_rejection(self):
        errors = {row["id"]: row for row in self.data["inputErrors"]}
        for name in (
            "activation-rejects-earlier-supported-rejected-send",
            "activation-rejects-earlier-receive-history",
        ):
            with self.subTest(case=name):
                with self.assertRaisesRegex(ValueError, "before this endpoint"):
                    reference.replay(errors[name]["input"])
        policy = errors["dispatch-policy-is-strict-boolean"]["input"]["events"][64][
            "policyPermitted"
        ]
        self.assertIs(type(policy), int)
        self.assertEqual(policy, 1)
        self.assertTrue(all(row.get("replacements") for row in self.data["inputErrors"]))

    def test_assurance_counts_covered_causes_and_actual_discharge_outputs_separately(self):
        expected = {
            "scope": "local-ack-generation",
            "status": "checked",
            "clientEnabled": True,
            "clientCauses": 5,
            "clientDischarges": 5,
            "clientPending": 0,
            "serverEnabled": True,
            "serverCauses": 5,
            "serverDischarges": 4,
            "serverPending": 0,
        }
        self.assertEqual(comparison.expected_ack(self.report), expected)
        comparison.check_ack_assurance({"ackAssurance": expected}, self.report, "exact")
        with self.assertRaises(AssertionError):
            comparison.check_ack_assurance({}, self.report, "missing")
        extra = {**expected, "ackSent": True}
        with self.assertRaises(AssertionError):
            comparison.check_ack_assurance({"ackAssurance": extra}, self.report, "extra")
        wrong_type = {**expected, "clientPending": False}
        with self.assertRaises(AssertionError):
            comparison.check_ack_assurance({"ackAssurance": wrong_type}, self.report, "Boolean")
        pending = reference.replay(self.cases["pending-ack-survives-transfer"]["input"])
        value = comparison.expected_ack(pending)
        self.assertEqual((value["status"], value["clientPending"]), ("pending", 1))
        failed = reference.replay(self.cases["stale-allow-retains-actual-acks"]["input"])
        self.assertEqual(
            comparison.expected_ack(failed), {"scope": "local-ack-generation", "status": "failed"}
        )

    def test_only_enabled_endpoints_get_assurance_and_disabled_counts_are_zero(self):
        single = reference.replay(
            self.cases["single-enabled-endpoint-has-zero-disabled-peer-counts"]["input"]
        )
        value = comparison.expected_ack(single)
        self.assertEqual(value["status"], "checked")
        self.assertIs(value["clientEnabled"], True)
        self.assertIs(value["serverEnabled"], False)
        self.assertTrue(
            all(
                count == 0
                for key, count in value.items()
                if key.endswith(("Causes", "Discharges", "Pending"))
            )
        )
        disabled = reference.replay(self.cases["ack-enable-requires-recovery-clock"]["input"])
        self.assertIsNone(comparison.expected_ack(disabled))
        comparison.check_ack_assurance({}, disabled, "disabled")


if __name__ == "__main__":
    unittest.main()
