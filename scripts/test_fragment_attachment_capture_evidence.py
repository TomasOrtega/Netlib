"""Keep actual fragment keys and provenance distinct from attachment history."""

import copy
import ipaddress
import struct
import unittest

from capture_evidence import EvidenceError
from fragment_attachment_capture_evidence import (
    FragmentReplay,
    decode_ethernet,
    decode_fragment_af,
    decode_fragment_nflog,
    decode_udp,
    fragment_key,
    join_fragment_ingress,
    qualified_counter_delta,
)
from reassembly_reference import IPPacket, encode_packet

NS = {"id": 4026533000, "birth": 100}


def port(index, *, namespace=NS, birth=None):
    return {
        "ns": namespace,
        "ifindex": index,
        "birth": namespace["birth"] + 1 if birth is None else birth,
    }


def packet(payload, *, identification=123, offset=0, more=False):
    return encode_packet(
        IPPacket(
            int(ipaddress.IPv4Address("192.0.2.2")),
            int(ipaddress.IPv4Address("203.0.113.2")),
            payload,
            identification=identification,
            more_fragments=more,
            offset=offset,
        )
    ).hex()


def arrival(name, raw, tick, index=7, *, allow=True, namespace=NS, prefix=10):
    return {
        "id": name,
        "raw": raw,
        "timeNs": 1000 + tick,
        "ingress": port(index, namespace=namespace),
        "earlyAllowed": allow,
        "authenticationPrefix": prefix,
    }


class FragmentCodecTests(unittest.TestCase):
    def test_noninitial_fragment_decodes_without_inventing_udp_ports(self):
        raw = packet(b"attacker-tail", offset=16)
        value = decode_ethernet("0200000000010200000000020800" + raw)
        self.assertEqual(value["offsetBytes"], 16)
        self.assertNotIn("sourcePort", value)
        self.assertEqual(value["raw"], raw)
        with self.assertRaises(EvidenceError):
            decode_udp(raw)

    def test_omitted_udp_checksum_is_retained_as_actual_bytes(self):
        raw = packet(struct.pack("!HHHH", 41000, 8080, 16, 0) + b"abcdefgh")
        value = decode_udp(raw)
        self.assertEqual(value["udpChecksum"], {"value": 0, "status": "omitted"})
        self.assertEqual(value["dataHex"], b"abcdefgh".hex())

    def test_trailing_bytes_and_truncated_ipv4_cannot_be_repaired(self):
        raw = packet(b"abcdefgh", offset=8)
        for changed in (raw + "00", raw[:-2]):
            with self.subTest(changed=changed), self.assertRaises(EvidenceError):
                decode_ethernet("0200000000010200000000020800" + changed)

    def test_udp_length_and_nonzero_bad_checksum_are_rejected(self):
        for length, checksum in ((17, 0), (16, 1)):
            with self.subTest(length=length, checksum=checksum), self.assertRaises(EvidenceError):
                decode_udp(
                    packet(struct.pack("!HHHH", 41000, 8080, length, checksum) + b"abcdefgh")
                )


class FragmentDomainTests(unittest.TestCase):
    def setUp(self):
        self.replay = FragmentReplay()
        self.replay.open(NS)
        self.udp = struct.pack("!HHHH", 41000, 8080, 32, 0) + b"legit---" + b"attacker-payload"

    def test_actual_queue_key_does_not_include_physical_input_or_eap_round(self):
        tail = self.replay.arrive(
            arrival("attacker", packet(self.udp[16:], offset=16), 1, 12, prefix=0)
        )
        head = self.replay.arrive(
            arrival("legitimate", packet(self.udp[:16], more=True), 2, 7, prefix=10)
        )
        self.assertEqual(tail["status"], "buffered")
        self.assertEqual(head["status"], "complete")
        self.assertEqual(
            [item["arrival"] for item in head["contributors"]], ["legitimate", "attacker"]
        )
        self.assertEqual(head["completingIngress"], port(7))
        self.assertEqual(decode_udp(head["output"])["dataHex"], self.udp[8:].hex())
        self.assertEqual(tail["domain"], head["domain"])
        self.assertNotIn("ifindex", head["domain"])
        self.assertNotIn("authenticationPrefix", head["domain"])

    def test_early_drop_prevents_this_fragment_from_entering_the_oracle(self):
        dropped = self.replay.arrive(
            arrival("attacker", packet(self.udp[16:], offset=16), 1, 12, allow=False)
        )
        head = self.replay.arrive(arrival("legitimate", packet(self.udp[:16], more=True), 2))
        self.assertEqual(dropped["status"], "earlyDrop")
        self.assertEqual(head["status"], "buffered")
        self.assertIsNone(head["output"])
        self.assertEqual(len(self.replay.queues(NS)), 1)

    def test_rejected_piece_does_not_advance_or_expire_existing_model_queues(self):
        self.replay.arrive(arrival("head", packet(self.udp[:16], more=True), 1))
        before = self.replay.queues(NS)
        self.replay.arrive(
            arrival("denied-tail", packet(self.udp[16:], offset=16), 40_000_000_000, allow=False)
        )
        self.assertEqual(before, self.replay.queues(NS))

    def test_actual_user_and_l3_master_vif_partition_queues(self):
        self.replay.arrive(arrival("head", packet(self.udp[:16], more=True), 1), user=2, vif=0)
        for name, user, vif in (("zone", 3, 0), ("master", 2, 9)):
            result = self.replay.arrive(
                arrival(name, packet(self.udp[16:], offset=16), 2), user=user, vif=vif
            )
            self.assertEqual(result["status"], "buffered")
        self.assertEqual(len(self.replay.queues(NS)), 3)

    def test_retirement_preserves_old_state_and_same_namespace_cannot_reopen(self):
        self.replay.arrive(arrival("head", packet(self.udp[:16], more=True), 1))
        before = self.replay.queues(NS)
        self.replay.close(NS)
        self.assertEqual(before, self.replay.queues(NS))
        with self.assertRaises(EvidenceError):
            self.replay.open(copy.deepcopy(NS))
        with self.assertRaises(EvidenceError):
            self.replay.arrive(arrival("old-tail", packet(self.udp[16:], offset=16), 2))

    def test_fresh_namespace_does_not_inherit_archived_fragment_bytes(self):
        self.replay.arrive(arrival("old-head", packet(self.udp[:16], more=True), 1))
        self.replay.close(NS)
        fresh = {"id": NS["id"] + 1, "birth": 200}
        self.replay.open(fresh)
        result = self.replay.arrive(
            arrival("fresh-tail", packet(self.udp[16:], offset=16), 2, namespace=fresh)
        )
        self.assertEqual(result["status"], "buffered")
        self.assertIsNone(result["output"])
        self.assertEqual(len(self.replay.queues(NS)), 1)
        self.assertEqual(len(self.replay.queues(fresh)), 1)

    def test_different_namespace_births_cannot_alias_a_simultaneously_live_inode(self):
        with self.assertRaises(EvidenceError):
            self.replay.open({"id": NS["id"], "birth": 200})

    def test_duplicate_piece_does_not_replace_the_contributor_source(self):
        raw = packet(self.udp[:16], more=True)
        self.replay.arrive(arrival("first", raw, 1))
        duplicate = self.replay.arrive(arrival("duplicate", raw, 2))
        completed = self.replay.arrive(arrival("tail", packet(self.udp[16:], offset=16), 3))
        self.assertEqual(duplicate["status"], "duplicate")
        self.assertEqual([item["arrival"] for item in completed["contributors"]], ["first", "tail"])

    def test_fragment_key_keeps_only_actual_domain_and_ip_fields(self):
        value = decode_ethernet("0200000000010200000000020800" + packet(b"abcdefgh", offset=8))
        self.assertEqual(
            set(fragment_key(value, NS, 2, 0)),
            {"namespace", "user", "vif", "source", "destination", "protocol", "identification"},
        )

    def test_returned_fragment_key_is_a_historical_namespace_value(self):
        namespace = copy.deepcopy(NS)
        value = decode_ethernet("0200000000010200000000020800" + packet(b"abcdefgh", offset=8))
        result = fragment_key(value, namespace, 2, 0)
        namespace["birth"] += 1
        self.assertEqual(result["namespace"], NS)

    def test_arrival_cannot_precede_its_actual_interface_birth(self):
        value = arrival("future-port", packet(self.udp[:16], more=True), 1)
        value["ingress"]["birth"] = value["timeNs"] + 1
        with self.assertRaises(EvidenceError):
            self.replay.arrive(value)

    def test_rejected_arrival_still_cannot_reverse_actual_observation_order(self):
        self.replay.arrive(arrival("head", packet(self.udp[:16], more=True), 2))
        with self.assertRaises(EvidenceError):
            self.replay.arrive(
                arrival("denied-old", packet(self.udp[16:], offset=16), 1, allow=False)
            )

    def test_timeout_must_be_a_positive_integer_without_consuming_the_arrival(self):
        for timeout in (0.5, True, 0, -1):
            with self.subTest(timeout=timeout):
                replay = FragmentReplay()
                replay.open(NS)
                value = arrival("head", packet(self.udp[:16], more=True), 1)
                with self.assertRaises(EvidenceError):
                    replay.arrive(value, timeout=timeout)
                self.assertEqual(replay.seen_arrivals, set())
                self.assertEqual(replay.sources, {})
                self.assertEqual(
                    replay.domains[(NS["id"], NS["birth"])]["lastArrivalNs"], NS["birth"]
                )
                self.assertEqual(replay.queues(NS), {})


def attribute(kind, payload):
    size = len(payload) + 4
    return struct.pack("=HH", size, kind) + payload + bytes((-size) % 4)


class FragmentRawJoinTests(unittest.TestCase):
    def setUp(self):
        self.ip = packet(b"attacker-tail", offset=16)
        self.ethernet = "0200000000010200000000020800" + self.ip
        self.frame = {
            "namespace": "gateway",
            "interface": "car",
            "ifindex": 7,
            "timeNs": 1000,
            "packetType": 0,
            "hex": self.ethernet,
        }
        self.fields = {
            1: bytes((8, 0, 0, 0)),
            3: bytes(16),
            4: (7).to_bytes(4, "big"),
            8: bytes.fromhex("00060000") + bytes.fromhex(self.ethernet)[6:12] + bytes(2),
            9: bytes.fromhex(self.ip),
            10: b"FRAG_ALLOW\0",
            12: (1).to_bytes(4, "big"),
            13: (1).to_bytes(4, "big"),
            15: bytes((0, 1)),
            16: bytes.fromhex(self.ethernet)[:14],
            17: bytes((0, 14)),
        }

    def log(self, *, sender=None, flags=0):
        body = bytes((2, 0, 0, 42)) + b"".join(
            attribute(kind, value) for kind, value in self.fields.items()
        )
        raw = struct.pack("=IHHII", 16 + len(body), 0x400, 0, 0, 0) + body
        return decode_fragment_nflog(
            {
                "timeNs": 1001,
                "hex": raw.hex(),
                "sender": [0, 0] if sender is None else sender,
                "flags": flags,
            },
            NS,
            "gateway-nflog.jsonl:1",
            {"FRAG_ALLOW", "FRAG_DROP"},
        )

    def af(self):
        return decode_fragment_af(
            self.frame, "gateway", NS, {"car": port(7)}, "gateway-frames.jsonl:1"
        )

    def test_raw_noninitial_piece_joins_actual_iif_and_hardware_bytes(self):
        result = join_fragment_ingress(self.af(), self.log(), (900, 1100))
        self.assertEqual(result["ingress"], port(7))
        self.assertEqual(result["raw"], self.ip)
        self.assertEqual(result["observedDecision"], "FRAG_ALLOW")

    def test_boolean_sender_and_flags_cannot_impersonate_kernel_integer_metadata(self):
        for values in (
            {"sender": [False, False]},
            {"flags": False},
            {"sender": [False, False], "flags": False},
        ):
            with self.subTest(values=values), self.assertRaises(EvidenceError):
                self.log(**values)

    def test_claimed_legitimate_mac_does_not_override_actual_metadata_index(self):
        self.fields[4] = (12).to_bytes(4, "big")
        with self.assertRaises(EvidenceError):
            join_fragment_ingress(self.af(), self.log(), (900, 1100))

    def test_log_from_another_namespace_cannot_join_identical_piece_bytes(self):
        log = self.log()
        log["namespace"] = {"id": NS["id"] + 1, "birth": NS["birth"]}
        with self.assertRaises(EvidenceError):
            join_fragment_ingress(self.af(), log, (900, 1100))

    def test_pre_fragment_log_cannot_silently_supply_reassembled_bytes(self):
        self.fields[9] = bytes.fromhex(packet(b"attacker-tail"))
        with self.assertRaises(EvidenceError):
            join_fragment_ingress(self.af(), self.log(), (900, 1100))

    def test_packet_metadata_cannot_substitute_a_reused_or_unknown_index(self):
        self.frame["ifindex"] = 12
        with self.assertRaises(EvidenceError):
            self.af()

    def test_raw_arrival_cannot_predate_its_supplied_live_interface_instance(self):
        self.frame["timeNs"] = NS["birth"]
        with self.assertRaises(EvidenceError):
            self.af()

    def test_hardware_source_is_independent_evidence_and_must_match(self):
        self.fields[8] = self.fields[8][:4] + bytes.fromhex("02000000aaaa") + bytes(2)
        with self.assertRaises(EvidenceError):
            self.log()

    def test_physical_and_log_receipts_must_fit_the_same_operation_window(self):
        with self.assertRaises(EvidenceError):
            join_fragment_ingress(self.af(), self.log(), (1001, 1100))


class ReassemblyCounterTests(unittest.TestCase):
    def snmp(self, requests=0, complete=0, failures=0, timeouts=0):
        return f"Ip: Forwarding ReasmReqds ReasmOKs ReasmFails ReasmTimeout\nIp: 1 {requests} {complete} {failures} {timeouts}\n"

    def test_qualified_counter_delta_is_not_a_native_queue_inventory(self):
        result = qualified_counter_delta(
            self.snmp(), self.snmp(requests=1), namespace_before=NS, namespace_after=NS
        )
        self.assertEqual(
            result, {"ReasmReqds": 1, "ReasmOKs": 0, "ReasmFails": 0, "ReasmTimeout": 0}
        )
        self.assertNotIn("queueEmpty", result)
        self.assertNotIn("queues", result)

    def test_counter_reset_or_namespace_splice_is_rejected(self):
        with self.assertRaises(EvidenceError):
            qualified_counter_delta(
                self.snmp(requests=1), self.snmp(), namespace_before=NS, namespace_after=NS
            )

    def test_equal_counter_values_from_different_namespaces_are_not_one_interval(self):
        with self.assertRaises(EvidenceError):
            qualified_counter_delta(
                self.snmp(),
                self.snmp(),
                namespace_before=NS,
                namespace_after={"id": NS["id"] + 1, "birth": 200},
            )


if __name__ == "__main__":
    unittest.main()
