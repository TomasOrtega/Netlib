"""Test independent receive gaps, retained packet origins, and queued ACK clocks."""

import copy
import json
import unittest
from dataclasses import replace

import campus_tcp_gap_reference as reference
import check_tcp_gap_examples as checks

Store = reference.Store
Scope = reference.Scope
MODULUS = reference.MODULUS
wire = reference.wire
ack = reference.ack
recovery = reference.recovery
evaluate = reference.evaluate
wrapped = reference.wrapped


def packet(state, sequence, payload, acknowledgment=None, window=4096, flags=16):
    segment = wire.Segment(
        sequence,
        state.core.send_una if acknowledgment is None else acknowledgment,
        flags,
        window=window,
        payload=payload,
    )
    raw = wire.fixture_packet(state.core.inbound, segment)
    return {"kind": "receive", "rawIPv4Hex": raw.hex()}


def failure_summary(result):
    failure = result.reassembly["failure"]
    return {
        "receipt": failure["receipt"]["receiptID"],
        "reason": "input." + failure["reason"]["reason"],
    }


class ReceiptClockTests(unittest.TestCase):
    def test_partial_ack_cannot_precede_its_original_send(self):
        timer = recovery.Recovery.initial(800).advance(150).sent(400).advance(200)
        with self.assertRaisesRegex(recovery.Stop, "ledger"):
            reference.acknowledge_at(timer, 100, 100)

    def test_cumulative_ack_cannot_precede_a_later_touched_send(self):
        timer = (
            recovery.Recovery.initial(800).advance(50).sent(200).advance(150).sent(200).advance(200)
        )
        with self.assertRaisesRegex(recovery.Stop, "ledger"):
            reference.acknowledge_at(timer, 400, 100)

    def test_karn_exclusion_does_not_remove_send_time_order(self):
        timer = recovery.Recovery.initial(800).advance(150).sent(400).advance(200)
        timer = replace(timer, outstanding=(replace(timer.outstanding[0], retried=True),))
        with self.assertRaisesRegex(recovery.Stop, "ledger"):
            reference.acknowledge_at(timer, 400, 100)


class StoreTests(unittest.TestCase):
    def initial(self, **changes):
        return Store(**dict(origin=100, capacity=4096, outgoing_mss=1200, **changes))

    def test_real_two_receipt_release(self):
        start = self.initial()
        held = start.receive(500, b"b" * 400, ("primary", 7), 100)
        self.assertEqual((held.novel, len(held.released), held.immediate), (400, 0, True))
        self.assertEqual((held.state.position, held.state.width), (0, 4096))
        self.assertEqual((held.state.physical_free, held.state.reservation_free), (3696, 4096))
        complete = held.state.receive(100, b"a" * 400, ("standby", 3), 1100)
        self.assertEqual(
            (complete.novel, len(complete.released), complete.immediate), (400, 800, True)
        )
        values, after = complete.state.read(800)
        self.assertEqual(bytes(row.value for row in values), b"a" * 400 + b"b" * 400)
        self.assertEqual({row.receipt for row in values[:400]}, {1})
        self.assertEqual({row.receipt for row in values[400:]}, {0})
        self.assertEqual((after.held_size, after.physical_free, after.position), (0, 4096, 800))
        for cell in values:
            self.assertLessEqual(after.origin_for(cell).arrived_at, 1100)

    def test_partial_gap_fill_remains_immediate(self):
        state = self.initial().receive(500, b"b" * 400).state
        result = state.receive(100, b"a" * 200)
        self.assertEqual(
            (result.novel, len(result.released), result.state.held_size), (200, 200, 400)
        )
        self.assertTrue(result.immediate)
        self.assertEqual((result.state.width, result.state.physical_free), (3896, 3496))

    def test_exact_duplicate_preserves_first_header_time_and_owner(self):
        state = self.initial().receive(500, b"b" * 400, ("old-ack", 12), 100).state
        result = state.receive(500, b"b" * 400, ("new-ack", 33), 200)
        self.assertTrue(result.duplicate and result.immediate)
        self.assertEqual((result.novel, len(result.released), result.state.held_size), (0, 0, 400))
        self.assertEqual(result.state.held, state.held)
        self.assertEqual(result.state.origin_for(result.state.held[0][1]).header, ("old-ack", 12))
        self.assertEqual(result.state.origin_for(result.state.held[0][1]).arrived_at, 100)

    def test_queued_suffix_cannot_be_read(self):
        state = self.initial().receive(500, b"b" * 400).state
        with self.assertRaisesRegex(Scope, "read"):
            state.read(1)
        self.assertEqual(state.read(0)[1], state)

    def test_wrapped_origin(self):
        start = Store(MODULUS - 200, 4096, 1200)
        held = start.receive(200, b"b" * 400).state
        result = held.receive(MODULUS - 200, b"a" * 400)
        self.assertEqual(result.state.sequence, 600)
        self.assertEqual(result.state.position, 800)
        self.assertEqual(bytes(cell.value for cell in result.released), b"a" * 400 + b"b" * 400)

    def test_multiple_held_spans_release_in_sequence_order(self):
        start = self.initial()
        state = start.receive(700, b"d" * 200).state
        state = state.receive(300, b"b" * 200).state
        state = state.receive(500, b"c" * 200).state
        result = state.receive(100, b"a" * 200)
        self.assertEqual(
            bytes(cell.value for cell in result.released),
            b"a" * 200 + b"b" * 200 + b"c" * 200 + b"d" * 200,
        )
        self.assertEqual([cell.receipt for cell in result.released[::200]], [3, 1, 2, 0])

    def test_right_edge_stays_fixed_on_held_data_and_output(self):
        start = self.initial()
        state = start.receive(500, b"b" * 400).state
        self.assertEqual(state.output().edge, start.edge)
        self.assertGreater(state.output().width, state.physical_free)

    def test_small_read_keeps_edge(self):
        state = self.initial().receive(500, b"b" * 400).state
        state = state.receive(100, b"a" * 400).state
        _, state = state.read(799)
        self.assertEqual(state.output().edge, 4096)
        self.assertEqual((state.width, state.reservation_free), (3296, 4095))

    def test_threshold_read_uses_outgoing_mss(self):
        state = Store(100, 4096, 800).receive(500, b"b" * 400).state
        state = state.receive(100, b"a" * 400).state
        _, state = state.read(800)
        self.assertEqual(state.output().edge, 4896)
        self.assertEqual(state.output().width, 4096)

    def test_overlap_and_conflict_scope(self):
        state = self.initial().receive(500, b"b" * 400).state
        with self.assertRaisesRegex(Scope, "overlap"):
            state.receive(700, b"b" * 400)
        with self.assertRaisesRegex(Scope, "conflict"):
            state.receive(500, b"x" * 400)
        self.assertEqual(state.held_size, 400)

    def test_window_overrun_and_old_overlap_scope(self):
        state = Store(100, 800, 800)
        with self.assertRaisesRegex(Scope, "trimming"):
            state.receive(800, b"a" * 200)
        state = state.receive(100, b"a" * 400).state
        with self.assertRaisesRegex(Scope, "trimming"):
            state.receive(300, b"a" * 400)
        with self.assertRaisesRegex(Scope, "sequence"):
            state.receive(100, b"a" * 400)

    def test_every_order_of_four_actual_spans_releases_same_bytes(self):
        import itertools

        payloads = [bytes([17 + number]) * 40 for number in range(4)]
        for order in itertools.permutations(range(4)):
            state = Store(100, 320, 80)
            for number in order:
                state = state.receive(
                    100 + 40 * number, payloads[number], ("actual", number), number
                ).state
                self.assertTrue(state.valid)
            self.assertEqual(state.held_size, 0)
            self.assertEqual(state.position, 160)
            self.assertEqual(bytes(cell.value for cell in state.unread), b"".join(payloads))


class EndpointTests(unittest.TestCase):
    def state(self, sent=b""):
        inbound = wire.Header("10.0.0.1", "10.0.0.2", 6, 4000, 80)
        core = wire.State(inbound, 100, 4096, b"", 1000, 1000 + len(sent), sent)
        initial = ack.Endpoint(core, b"", 4096, 4096, 100, 1000, 800, 1500)
        return wrapped(initial)

    def enabled(self, sent=b""):
        state = self.state(sent)
        state = ack.evaluate(state, {"kind": "enableRecovery"}).state if not sent else state
        if sent:
            timer = (
                recovery.Recovery.initial(800)
                .advance(50)
                .sent(200)
                .sent(len(sent) - 200)
                .advance(200)
            )
            state = replace(state, recovery=timer, last_ack_window=4096)
        state = ack.evaluate(state, {"kind": "enableAck"}).state
        return state

    def test_data_gap_without_optional_ack_mode(self):
        state = self.state()
        held = evaluate(state, packet(state, 500, b"b" * 400)).state
        self.assertEqual((held.core.received, held.core.receive_next), (b"", 100))
        received = evaluate(held, packet(held, 100, b"a" * 400))
        self.assertEqual(received.decision["received"], 400)
        self.assertEqual(len(bytes.fromhex(received.reassembly["releasedHex"])), 800)
        self.assertEqual(received.state.core.received, b"a" * 400 + b"b" * 400)

    def test_one_gap_fill_cause_with_distinct_novel_and_released_sizes(self):
        state = self.enabled()
        held = evaluate(state, packet(state, 500, b"b" * 400)).state
        self.assertEqual(len(held.ack_state.work.pending), 1)
        self.assertEqual(
            (held.ack_state.work.pending[0].demand.bytes, held.ack_state.window.frontier), (400, 0)
        )
        self.assertEqual(held.ack_state.work.deadline, 0)
        held = evaluate(held, {"kind": "dispatchAck", "policyPermitted": True}).state
        received = evaluate(held, packet(held, 100, b"a" * 400)).state
        self.assertEqual(
            (received.ack_state.window.frontier, received.ack_state.window.buffered), (800, 800)
        )
        self.assertEqual(len(received.ack_state.work.pending), 1)
        self.assertEqual(received.ack_state.work.pending[0].demand.bytes, 400)
        self.assertEqual(received.ack_state.work.deadline, 0)

    def test_deferred_ack_sample_uses_original_arrival_and_current_restart(self):
        state = self.state(b"x" * 400)
        timer = recovery.Recovery.initial(800).advance(50).sent(200).sent(200).advance(100)
        state = replace(state, recovery=timer, last_ack_window=4096)
        held = evaluate(state, packet(state, 500, b"b" * 400, 1200)).state
        self.assertEqual(held.core.send_una, 1000)
        self.assertEqual(held.recovery.flight, 400)
        state = replace(held, recovery=held.recovery.advance(200))
        received = evaluate(state, packet(state, 100, b"a" * 400, 1000)).state
        self.assertEqual(received.core.send_una, 1200)
        self.assertEqual(received.recovery.last_sample, (0, 50, 100))
        self.assertEqual((received.recovery.now, received.recovery.deadline), (200, 1200))

    def test_failed_deferred_header_keeps_original_queue_and_state(self):
        state = self.state()
        held = evaluate(state, packet(state, 500, b"b" * 400, 1000)).state
        moved = replace(held, core=replace(held.core, send_una=71000, send_next=71000))
        result = evaluate(moved, packet(moved, 100, b"a" * 400, 71000))
        self.assertEqual(result.decision, {"kind": "unsupported", "reason": "queuedHeader"})
        self.assertEqual(failure_summary(result), {"receipt": 0, "reason": "input.acknowledgment"})
        self.assertEqual(result.state, moved)
        self.assertEqual(
            (result.state.core.received, result.state.receive_store.held_size), (b"", 400)
        )
        self.assertEqual(result.state.receive_store.next_id, 1)

    def test_pure_ack_in_window_keeps_its_existing_immediate_path(self):
        state = self.state(b"x" * 400)
        held = evaluate(state, packet(state, 500, b"b" * 400, 1000)).state
        result = evaluate(held, packet(held, 200, b"", 1200))
        self.assertEqual((result.state.core.send_una, len(result.state.core.sent)), (1200, 200))
        self.assertEqual(result.state.receive_store, held.receive_store)

    def test_queued_data_cannot_create_a_second_response_credit_on_release(self):
        state = self.enabled()
        held = evaluate(state, packet(state, 500, b"b" * 400)).state
        held = evaluate(held, {"kind": "dispatchAck", "policyPermitted": True}).state
        filled = evaluate(held, packet(held, 100, b"a" * 400)).state
        first = evaluate(filled, {"kind": "dispatchAck", "policyPermitted": True})
        second = evaluate(first.state, {"kind": "dispatchAck", "policyPermitted": True})
        self.assertEqual(second.decision, {"kind": "reject", "reason": "ack.noCredit"})
        self.assertEqual(first.state.ack_state.work.next_id, 2)
        self.assertEqual(len(first.state.ack_state.work.completed), 2)

    def test_missing_ack_above_gap_is_checked_on_release(self):
        state = self.state()
        queued = evaluate(state, packet(state, 500, b"b" * 400, flags=0))
        self.assertEqual(queued.decision["kind"], "accepted")
        self.assertEqual(queued.state.receive_store.held_size, 400)
        released = evaluate(queued.state, packet(queued.state, 100, b"a" * 400))
        self.assertEqual(released.decision, {"kind": "unsupported", "reason": "queuedHeader"})
        self.assertEqual(failure_summary(released), {"receipt": 0, "reason": "input.missingAck"})
        self.assertEqual(released.state, queued.state)

    def test_unacceptable_ack_above_gap_is_checked_on_release(self):
        state = self.state()
        queued = evaluate(state, packet(state, 500, b"b" * 400, 100000))
        self.assertEqual(queued.decision["kind"], "accepted")
        released = evaluate(queued.state, packet(queued.state, 100, b"a" * 400))
        self.assertEqual(released.decision, {"kind": "unsupported", "reason": "queuedHeader"})
        self.assertEqual(
            failure_summary(released), {"receipt": 0, "reason": "input.acknowledgment"}
        )
        self.assertEqual(released.state, queued.state)

    def test_fresh_missing_ack_keeps_ordinary_rejection(self):
        state = self.enabled()
        result = evaluate(state, packet(state, 100, b"a" * 400, flags=0))
        self.assertEqual(result.decision, {"kind": "reject", "reason": "input.missingAck"})
        self.assertEqual(result.state, state)
        self.assertIsNone(getattr(result, "queue_failure", None))

    def test_fresh_header_failure_precedes_older_queued_header(self):
        state = self.state()
        held = evaluate(state, packet(state, 500, b"b" * 400, 100000)).state
        result = evaluate(held, packet(held, 100, b"a" * 400, flags=0))
        self.assertEqual(result.decision, {"kind": "reject", "reason": "input.missingAck"})
        self.assertEqual(result.state, held)

    def test_later_bad_duplicate_header_does_not_replace_first(self):
        state = self.state()
        held = evaluate(state, packet(state, 500, b"b" * 400)).state
        copied = evaluate(held, packet(held, 500, b"b" * 400, flags=0)).state
        result = evaluate(copied, packet(copied, 100, b"a" * 400))
        self.assertEqual(result.decision["kind"], "accepted")
        self.assertEqual(result.decision["received"], 400)
        self.assertEqual(len(bytes.fromhex(result.reassembly["releasedHex"])), 800)
        self.assertEqual(result.state.receive_store.next_id, 3)
        self.assertEqual({cell.receipt for cell in result.state.receive_store.unread[400:]}, {0})

    def test_later_good_duplicate_header_does_not_repair_first(self):
        state = self.state()
        held = evaluate(state, packet(state, 500, b"b" * 400, flags=0)).state
        copied = evaluate(held, packet(held, 500, b"b" * 400)).state
        result = evaluate(copied, packet(copied, 100, b"a" * 400))
        self.assertEqual(result.decision, {"kind": "unsupported", "reason": "queuedHeader"})
        self.assertEqual(failure_summary(result), {"receipt": 0, "reason": "input.missingAck"})
        self.assertEqual(result.state, copied)

    def test_duplicate_meta_is_not_substituted(self):
        state = self.state(b"x" * 400)
        timer = recovery.Recovery.initial(800).advance(50).sent(200).sent(200).advance(100)
        state = replace(state, recovery=timer, last_ack_window=4096)
        held = evaluate(state, packet(state, 500, b"b" * 400, 1200, 2000)).state
        held = replace(held, recovery=held.recovery.advance(150))
        copied = evaluate(held, packet(held, 500, b"b" * 400, 1400, 3000)).state
        self.assertEqual((copied.core.send_una, copied.last_ack_window), (1000, 4096))
        copied = replace(copied, recovery=copied.recovery.advance(200))
        received = evaluate(copied, packet(copied, 100, b"a" * 400, 1000)).state
        self.assertEqual((received.core.send_una, received.last_ack_window), (1200, 2000))
        self.assertEqual(received.recovery.last_sample, (0, 50, 100))


class LegacyMigrationTests(unittest.TestCase):
    def test_seeded_unread_bytes_reduce_the_initial_reservation(self):
        seed = {
            "core": {
                "inbound": {
                    "source": "192.0.2.1",
                    "destination": "198.51.100.2",
                    "protocol": 6,
                    "sourcePort": 12345,
                    "destinationPort": 80,
                },
                "receiveNext": 100,
                "capacity": 8,
                "receivedHex": "7879",
                "sendUna": 1000,
                "sendNext": 1000,
                "sentHex": "",
            },
            "pendingHex": "",
            "pendingLimit": 8,
            "sendWindow": 8,
            "sendWL1": 100,
            "sendWL2": 1000,
            "effectiveMSS": 536,
            "ipSendLimit": 576,
        }
        state = reference.raw_state(seed)
        self.assertTrue(state.valid)
        self.assertEqual((state.receive_store.width, state.receive_store.physical_free), (6, 6))

    def test_old_endpoint_geometry_inputs_move_to_gap_corpus(self):
        original = json.loads(
            (reference.recovery.transfer.ROOT / "examples/tcp-endpoint/fixtures.json").read_text()
        )
        self.assertNotIn(
            "unsupported-geometry-keeps-window", {row["name"] for row in original["cases"]}
        )
        self.assertNotIn(
            "geometry-stop-keeps-window-history", {row["name"] for row in original["traces"]}
        )

    def test_old_campus_geometry_reaches_its_actual_continuation_error(self):
        data = reference.ack.load_fixtures()
        name = "out-of-order-receipt-reaches-later-emission-mismatch"
        self.assertNotIn(name, {row["id"] for row in data["cases"]})
        migrated = next(row for row in data["inputErrors"] if row["id"] == name)
        with self.assertRaisesRegex(ValueError, "receipt differs"):
            reference.ack.replay(migrated["input"])


class CorpusAndAuditTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.data = reference.load_fixtures()
        cls.main = reference.replay(cls.data["input"])

    def test_frozen_functional_cases_and_source_audits(self):
        for case in self.data["cases"]:
            with self.subTest(case=case["id"]):
                report = reference.replay(case["input"])
                self.assertEqual(reference.projection(report), case["expected"])
                checks.audit(report, case["id"])

    def test_raw_cases_keep_their_frozen_results(self):
        for case in self.data["endpointCases"]:
            with self.subTest(case=case["id"]):
                self.assertEqual(reference.raw_replay(case["input"]), case["expected"])

    def test_canonical_deferred_clock_input_keeps_the_independent_case(self):
        checks.check_deferred_clock_input(self.data)
        changed = copy.deepcopy(self.data)
        case = next(
            case
            for case in changed["cases"]
            if case["id"] == "queued-header-retains-original-receipt-clock"
        )
        case["input"]["events"] = case["input"]["events"][:-1]
        with self.assertRaises(AssertionError):
            checks.check_deferred_clock_input(changed)

    def test_first_failed_run_keeps_its_recovery_reason(self):
        case = next(
            case
            for case in self.data["endpointCases"]
            if case["id"] == "earlier-recovery-failure-precedes-later-queued-bad-ack"
        )
        step = reference.raw_replay(case["input"])["steps"][-1]
        failure = step["reassembly"]["failure"]
        self.assertEqual((failure["check"], failure["receipt"]["receiptID"]), ("recovery", 0))
        self.assertEqual(failure["reason"], {"kind": "reject", "reason": "recovery.ledger"})
        self.assertEqual(step["state"], step["before"])
        self.assertEqual(step["state"]["receiveStore"]["nextID"], 2)
        self.assertIsNone(step["reassembly"]["receiptID"])

    def test_all_three_migrated_inputs_are_mandatory(self):
        raw = {case["id"] for case in self.data["endpointCases"] if case.get("migratedFrom")}
        self.assertEqual(
            raw, {"unsupported-geometry-keeps-window", "geometry-stop-keeps-window-history"}
        )
        campus = {case["id"] for case in self.data["inputErrors"] if case.get("migratedFrom")}
        self.assertEqual(campus, {"out-of-order-receipt-reaches-later-emission-mismatch"})
        migrated = next(case for case in self.data["inputErrors"] if case.get("migratedFrom"))
        self.assertEqual(migrated["previousID"], "actual-out-of-order-data-remains-outside-profile")

    def test_gap_assurance_counts_actual_receipts_releases_and_reads(self):
        self.assertEqual(
            reference.receive_gap_assurance(self.main),
            {
                "scope": "ordered-receive-storage",
                "status": "checked",
                "clientReceipts": 2,
                "serverReceipts": 2,
                "clientHeldBytes": 0,
                "serverHeldBytes": 0,
                "clientReleasedBytes": 1200,
                "serverReleasedBytes": 800,
                "clientReadBytes": 1200,
                "serverReadBytes": 800,
            },
        )

    def test_gap_assurance_is_mandatory_after_an_actual_gap(self):
        with self.assertRaises(AssertionError):
            checks.check_gap_assurance(self.main, self.main, "missing assurance")

    def test_held_suffix_cannot_claim_checked_closure(self):
        case = next(
            case for case in self.data["cases"] if case["id"] == "held-suffix-is-a-checked-prefix"
        )
        oracle = reference.replay(case["input"])
        report = {**oracle, "receiveGapAssurance": reference.receive_gap_assurance(oracle)}
        self.assertEqual(report["receiveGapAssurance"]["status"], "pending")
        checks.check_gap_assurance(report, oracle, "held suffix")
        report["receiveGapAssurance"]["status"] = "checked"
        with self.assertRaises(AssertionError):
            checks.check_gap_assurance(report, oracle, "false closure")

    def test_noncompliance_cannot_claim_gap_assurance(self):
        case = next(
            case
            for case in self.data["cases"]
            if case["id"] == "stale-permit-after-logoff-fails-gap-assurance"
        )
        oracle = reference.replay(case["input"])
        expected = reference.receive_gap_assurance(oracle)
        self.assertEqual(expected["status"], "failed")
        report = {**oracle, "receiveGapAssurance": expected}
        checks.check_gap_assurance(report, oracle, "stale permit")
        report["receiveGapAssurance"] = reference.receive_gap_assurance(self.main)
        with self.assertRaises(AssertionError):
            checks.check_gap_assurance(report, oracle, "false assurance")

    def test_no_gap_history_has_no_gap_assurance_field(self):
        case = reference.ack.load_fixtures()["cases"][0]
        oracle = reference.replay(case["input"])
        self.assertIsNone(reference.receive_gap_assurance(oracle))
        checks.check_gap_assurance(oracle, oracle, "old in-order history")
        report = {**oracle, "receiveGapAssurance": {"status": "absent"}}
        with self.assertRaises(AssertionError):
            checks.check_gap_assurance(report, oracle, "unexpected assurance")

    def test_raw_errors_are_not_unsupported_stops(self):
        for case in self.data["endpointInputErrors"]:
            with self.subTest(case=case["id"]), self.assertRaises(ValueError):
                reference.raw_replay(case["input"])

    def test_released_suffix_cannot_claim_the_current_receipt(self):
        report = copy.deepcopy(self.main)
        released = report["steps"][59]["reassembly"]["releasedRuns"]
        released[1]["receiptID"] = released[0]["receiptID"]
        with self.assertRaises(AssertionError):
            checks.audit(report, "changed receipt owner")

    def test_stored_arrival_cannot_be_replaced_with_release_time(self):
        report = copy.deepcopy(self.main)
        report["steps"][59]["reassembly"]["releasedRuns"][1]["receivedAt"] = 1100
        with self.assertRaises(AssertionError):
            checks.audit(report, "changed arrival clock")

    def test_released_bytes_cannot_be_replaced_with_current_payload(self):
        report = copy.deepcopy(self.main)
        frame = report["steps"][59]["reassembly"]
        frame["releasedHex"] = frame["releasedRuns"][0]["payloadHex"]
        with self.assertRaises(AssertionError):
            checks.audit(report, "changed released prefix")

    def test_deferred_rtt_sample_cannot_use_processing_time(self):
        case = next(
            case
            for case in self.data["cases"]
            if case["id"] == "queued-header-retains-original-receipt-clock"
        )
        report = reference.replay(case["input"])
        report["steps"][65]["state"]["server"]["recovery"]["lastSample"]["acknowledgedAt"] = 1100
        with self.assertRaises(AssertionError):
            checks.audit(report, "changed sample clock")

    def test_failure_schema_requires_source_and_check(self):
        case = next(
            case
            for case in self.data["endpointCases"]
            if case["id"] == "raw-queued-missing-ack-stop"
        )
        step = copy.deepcopy(case["expected"]["steps"][-1])
        del step["reassembly"]["failure"]["check"]
        with self.assertRaises(AssertionError):
            checks.check_frame(step["reassembly"], step["before"], "missing check")

    def test_failure_source_cannot_treat_an_old_tag_as_fresh(self):
        case = next(
            case
            for case in self.data["endpointCases"]
            if case["id"] == "raw-queued-missing-ack-stop"
        )
        step = copy.deepcopy(case["expected"]["steps"][-1])
        step["reassembly"]["failure"]["source"] = "current"
        with self.assertRaises(AssertionError):
            checks.check_frame(step["reassembly"], step["before"], "changed source")


if __name__ == "__main__":
    unittest.main()
