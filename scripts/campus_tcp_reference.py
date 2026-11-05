"""Independent static calculations for the selected campus TCP path.

The input files use native data formats. They contain constructed data, not captures.
This oracle does not execute Lean or send packets.
"""

import ipaddress
import json
import struct
from dataclasses import dataclass, replace
from functools import lru_cache
from itertools import product
from pathlib import Path

import tcp_endpoint_reference as endpoint
import tcp_handshake_reference as handshake
import tcp_receive_reference as wire

ROOT = Path(__file__).resolve().parent.parent
DIRECTORY = ROOT / "examples/campus-tcp"
FIXTURES = DIRECTORY / "fixtures.json"


def reverse(header):
    return wire.Header(
        header.destination,
        header.source,
        header.protocol,
        header.destination_port,
        header.source_port,
    )


def rewrite_packet(raw, target, ttl):
    packet = wire.decode_packet(raw)
    segment = packet.segment
    blank = (
        wire.TCP_HEADER.pack(
            target.source_port,
            target.destination_port,
            segment.sequence,
            segment.acknowledgment,
            (5 + len(segment.options) // 4) << 4 | segment.reserved,
            segment.flags,
            segment.window,
            0,
            segment.urgent_pointer,
        )
        + segment.options
        + segment.payload
    )
    tcp_crc = wire.checksum(wire.pseudoheader(target, len(blank)) + blank)
    tcp = blank[:16] + struct.pack("!H", tcp_crc) + blank[18:]
    ip = wire.IP_HEADER.pack(
        0x45,
        packet.tos,
        len(tcp) + 20,
        packet.identification,
        0x4000 if packet.dont_fragment else 0,
        ttl,
        6,
        0,
        int(ipaddress.IPv4Address(target.source)),
        int(ipaddress.IPv4Address(target.destination)),
    )
    raw = ip[:10] + struct.pack("!H", wire.checksum(ip)) + ip[12:] + tcp
    return {"rawIPv4Hex": raw.hex(), "decoded": wire.decode_packet(raw).to_dict()}


@dataclass(frozen=True)
class Authentication:
    round: int = 0
    authorized: bool = False
    request: tuple | None = None
    response: tuple | None = None
    success: int | None = None
    evidence: dict | None = None
    outer_identity: bytes | None = None
    authenticated: bool = False
    credential: dict | None = None
    now: int = 0
    admitted: dict | None = None

    def ready(self, context):
        return (
            bool(context["consumer"])
            and self.request is not None
            and self.response is not None
            and self.request[:2] == self.response[:2]
            and self.response[1] == 13
            and self.success == self.response[0]
            and self.evidence is not None
            and self.evidence["round"] == self.round
            and self.evidence["subject"] == context["consumer"]
            and self.evidence["method"] == 13
            and self.evidence["accepted"]
        )

    def permits(self, context, scope):
        token = self.credential
        return bool(
            self.authenticated
            and token is not None
            and token["integrity"]
            and token["issuer"] == context["issuer"]
            and token["subject"] == context["consumer"]
            and token["audience"] == context["producer"]
            and scope in token["scopes"]
            and self.now < token["expiresAt"]
        )

    def reset(self):
        return Authentication(
            round=self.round + 1,
            authenticated=self.authenticated,
            credential=self.credential,
            now=self.now,
            admitted=self.admitted,
        )

    def refresh(self, context):
        return replace(self, authorized=self.ready(context))


def eap_frame(binding, text):
    raw = wire.hex_bytes(text)
    if len(raw) < 18 or raw[12:14] != bytes.fromhex("888e"):
        raise ValueError("The EAPOL Ethernet header is invalid.")
    destination = raw[:6].hex(":")
    source = raw[6:12].hex(":")
    peer = binding["peer"].lower()
    authenticator = binding["authenticator"].lower()
    if source not in (peer, authenticator) or destination not in (
        "01:80:c2:00:00:03",
        peer if source == authenticator else authenticator,
    ):
        raise ValueError("The EAPOL frame does not match the selected link.")
    version, kind, length = struct.unpack_from("!BBH", raw, 14)
    if version not in (1, 2, 3) or len(raw) < 18 + length:
        raise ValueError("The EAPOL body is truncated.")
    if kind in (1, 2):
        if source != peer or length != 0:
            raise ValueError("The selected peer control frame is invalid.")
        return ("reset",)
    if kind != 0 or length < 4:
        raise ValueError("The EAPOL body is outside the selected profile.")
    code, identifier, declared = struct.unpack_from("!BBH", raw, 18)
    if not 4 <= declared <= length:
        raise ValueError("The declared EAP packet exceeds its enclosing body.")
    if code in (1, 2):
        if declared < 5 or (code == 2) != (source == peer):
            raise ValueError("The EAP message role is invalid.")
        method = raw[22]
        if not 0 < method < 254:
            raise ValueError("The EAP method is outside the selected profile.")
        return ("request" if code == 1 else "response", identifier, method, raw[23 : 18 + declared])
    if code not in (3, 4) or source != authenticator or declared != 4:
        raise ValueError("The terminal EAP packet is invalid.")
    return ("success" if code == 3 else "failure", identifier)


def authentication_step(before, context, binding, event):
    kind = event["type"]
    after = before
    if kind in ("begin", "restart", "disconnect", "close"):
        after = before.reset()
    elif kind == "frame":
        message = eap_frame(binding, event["raw"])
        action = message[0]
        if action == "reset":
            after = before.reset()
        elif action == "request":
            request = message[1:]
            if before.request is None or before.request[0] != request[0]:
                changed = (
                    before.request is not None
                    and before.request[1] >= 4
                    and before.request[1] != request[1]
                )
                base = before.reset() if before.success is not None or changed else before
                after = replace(base, request=request, response=None, success=None).refresh(context)
        elif action == "response":
            response = message[1:]
            if (
                before.request is not None
                and before.request[:2] == response[:2]
                and before.response is None
            ):
                after = replace(
                    before,
                    response=response,
                    success=None,
                    outer_identity=response[2] if response[1] == 1 else before.outer_identity,
                ).refresh(context)
        elif action == "success":
            identifier = message[1]
            if (
                before.response is not None
                and before.response[0] == identifier
                and before.response[1] == 13
            ):
                after = replace(before, success=identifier).refresh(context)
        elif before.response is not None and before.response[0] == message[1]:
            after = before.reset()
    elif kind == "method":
        evidence = {key: event[key] for key in ("round", "subject", "method", "accepted", "source")}
        if (
            evidence["round"] == before.round
            and evidence["subject"] == context["consumer"]
            and evidence["method"] == 13
        ):
            after = (
                replace(before, evidence=evidence).refresh(context)
                if evidence["accepted"]
                else before.reset()
            )
    elif kind == "install":
        after = replace(before, credential=event["credential"], admitted=None)
    elif kind == "advance":
        after = replace(before, now=max(before.now, event["now"]), admitted=None)
    elif kind == "revoke":
        after = replace(before, credential=None, admitted=None)
    elif kind == "request":
        after = replace(
            before, admitted=event["scope"] if before.permits(context, event["scope"]) else None
        )
    else:
        raise ValueError("The authentication event is unknown.")
    if before.round != after.round or before.authorized != after.authorized:
        after = replace(after, authenticated=after.authorized, credential=None, admitted=None)
    matched = event["authorized"] is None or event["authorized"] == after.authorized
    if kind == "request":
        matched = matched and event["accepted"] == (after.admitted == event["scope"])
    return after, matched


def selected_chain(snapshot, hook):
    chains = [
        item["chain"]
        for item in snapshot["nftables"]
        if "chain" in item and item["chain"].get("hook") == hook
    ]
    if len(chains) != 1:
        raise ValueError("The selected filter hook must have one chain.")
    chain = chains[0]
    rules = [
        item["rule"]
        for item in snapshot["nftables"]
        if "rule" in item and item["rule"]["chain"] == chain["name"]
    ]
    return chain, rules


def expression_match(expression, packet, classification):
    match = expression["match"]
    left = match["left"]
    if "payload" in left:
        protocol, field = left["payload"]["protocol"], left["payload"]["field"]
        if protocol == "ip":
            actual = {
                "saddr": packet.source,
                "daddr": packet.destination,
                "protocol": packet.protocol,
            }[field]
        else:
            if packet.protocol != {"tcp": 6, "udp": 17}[protocol]:
                return False
            actual = packet.source_port if field == "sport" else packet.destination_port
    elif "meta" in left:
        actual = packet.protocol
    elif "ct" in left:
        actual = classification
    else:
        raise ValueError("The match field is outside the selected input format.")
    right = match["right"]
    if "ct" in left:
        state_bit = {"invalid": 1, "established": 2, "related": 4, "new": 8, "untracked": 64}[
            classification
        ]
        if isinstance(right, int):
            return state_bit == right if match["op"] == "==" else bool(state_bit & right)
        choices = right.get("set") if isinstance(right, dict) else right
        choices = choices if isinstance(choices, list) else [choices]
        return any(choice == classification or choice == state_bit for choice in choices)
    if "meta" in left or left.get("payload", {}).get("field") == "protocol":
        if isinstance(right, str):
            right = {"tcp": 6, "udp": 17, "icmp": 1}[right]
    if left.get("payload", {}).get("field") in ("saddr", "daddr") and isinstance(right, str):
        result = ipaddress.IPv4Address(actual) in ipaddress.IPv4Network(right, strict=False)
    elif isinstance(right, dict) and "prefix" in right:
        prefix = right["prefix"]
        result = ipaddress.IPv4Address(actual) in ipaddress.IPv4Network(
            f"{prefix['addr']}/{prefix['len']}", strict=False
        )
    elif isinstance(right, dict) and "range" in right:
        result = right["range"][0] <= actual <= right["range"][1]
    elif isinstance(right, dict) and "set" in right:
        result = actual in right["set"]
    elif isinstance(right, list):
        result = actual in right
    else:
        result = actual == right
    return not result if match["op"] == "!=" else result


def filter_permits(snapshot, hook, packet, classification):
    chain, rules = selected_chain(snapshot, hook)
    for rule in rules:
        if all(
            expression_match(item, packet, classification)
            for item in rule["expr"]
            if "match" in item
        ):
            if any("accept" in item for item in rule["expr"]):
                return True
            if any("drop" in item for item in rule["expr"]):
                return False
    return chain["policy"] == "accept"


def translate(snapshot, hook, packet):
    _, rules = selected_chain(snapshot, hook)
    for rule in rules:
        if all(expression_match(item, packet, "new") for item in rule["expr"] if "match" in item):
            for item in rule["expr"]:
                if "dnat" in item:
                    return replace(
                        packet,
                        destination=item["dnat"]["addr"],
                        destination_port=item["dnat"].get("port", packet.destination_port),
                    )
                if "snat" in item:
                    return replace(
                        packet,
                        source=item["snat"]["addr"],
                        source_port=item["snat"].get("port", packet.source_port),
                    )
    return packet


def next_hop(routing, address):
    selected = None
    for route in routing["routes"]:
        block = ipaddress.IPv4Network("0.0.0.0/0" if route["dst"] == "default" else route["dst"])
        if ipaddress.IPv4Address(address) in block and (
            selected is None or block.prefixlen > selected[0]
        ):
            selected = block.prefixlen, route
    if selected is None or selected[1].get("type", "unicast") != "unicast":
        return None
    route = selected[1]
    binding = next(
        (
            item
            for item in routing["bindings"]
            if item["device"] == route["dev"] and item["gateway"] == route.get("gateway")
        ),
        None,
    )
    if binding is None:
        raise ValueError("The selected route has no declared device and gateway binding.")
    return binding["nextNode"]


@dataclass(frozen=True)
class Record:
    original: wire.Header
    translated: wire.Header
    zone: int = 0
    seen_reply: bool = False

    def input(self, direction):
        return self.original if direction == "original" else reverse(self.translated)

    def output(self, direction):
        return self.translated if direction == "original" else reverse(self.original)

    def after_destination(self, direction):
        packet = self.input(direction)
        output = self.output(direction)
        return replace(
            packet, destination=output.destination, destination_port=output.destination_port
        )


def attachment(records, config, packet, zone=0):
    for index, record in enumerate(records):
        if record.zone != zone:
            continue
        for direction in ("original", "reply"):
            if packet == record.input(direction):
                return index, record, direction, False
    destination = translate(config["nat"], "prerouting", packet)
    translated = translate(config["nat"], "postrouting", destination)
    return None, Record(packet, translated, zone), "original", True


@dataclass(frozen=True)
class Forwarded:
    records: tuple
    record: Record
    direction: str
    classification: str
    fresh: bool
    after_destination: wire.Header
    after_source: wire.Header | None
    next_hop: str | None
    disposition: str
    output: dict | None


def forward(records, routing, config, raw, zone=0):
    packet = wire.decode_packet(raw)
    index, record, direction, fresh = attachment(records, config, packet.header, zone)
    classification = "established" if direction == "reply" or record.seen_reply else "new"
    prepared = list(records)
    if direction == "reply":
        prepared[index] = replace(record, seen_reply=True)
    destination = record.after_destination(direction)
    hop = next_hop(routing, destination.destination)
    disposition = "routeDrop"
    source = output = None
    if hop is not None:
        if packet.ttl <= 1:
            disposition = "ttlExpired"
        elif not filter_permits(config["forward"], "forward", destination, classification):
            disposition = "forwardDrop"
        else:
            source = record.output(direction)
            if not filter_permits(config["late"], "postrouting", source, classification):
                disposition = "lateDrop"
            else:
                disposition = "forwarded"
                output = rewrite_packet(raw, source, packet.ttl - 1)
                if fresh:
                    prepared.append(record)
    return Forwarded(
        tuple(prepared),
        record,
        direction,
        classification,
        fresh,
        destination,
        source,
        hop,
        disposition,
        output,
    )


@dataclass(frozen=True)
class Lane:
    base: int
    observed: int
    acknowledged: int
    peer_window: int
    window_sequence: int
    window_acknowledgment: int
    peer_mss: int | None = None

    @property
    def data_limit(self):
        return handshake.DEFAULT_MSS if self.peer_mss is None else self.peer_mss

    @property
    def next(self):
        return (self.base + self.observed) % wire.MODULUS

    @property
    def outstanding(self):
        return self.observed - self.acknowledged

    @property
    def valid(self):
        return (
            self.acknowledged <= self.observed
            and self.observed + 2 < wire.HALF_SPACE
            and self.outstanding <= 65535
        )


@dataclass(frozen=True)
class Admission:
    phase: str = "empty"
    record: Record | None = None
    client_iss: int | None = None
    client_window: int | None = None
    server_iss: int | None = None
    server_window: int | None = None
    original: Lane | None = None
    reply: Lane | None = None
    observations: tuple = ()
    client_mss: int | None = None
    server_mss: int | None = None


def same_binding(left, right):
    return (left.original, left.translated, left.zone) == (
        right.original,
        right.translated,
        right.zone,
    )


def startup_failure(segment, flags):
    try:
        if flags & 2:
            handshake.startup_mss(segment.options)
        elif segment.options:
            raise ValueError("The final ACK options exceed the selected scope.")
    except ValueError:
        return "options"
    if segment.flags != flags:
        return "flags"
    if segment.payload:
        return "data"
    return None


def known_range(sender, segment, history):
    start = (segment.sequence - sender.base) % wire.MODULUS
    end = start + len(segment.payload)
    if not segment.payload or end > sender.observed:
        return False
    for earlier in history:
        left = (earlier.sequence - sender.base) % wire.MODULUS
        right = left + len(earlier.payload)
        if (
            earlier.flags in (16, 24)
            and not earlier.options
            and earlier.payload
            and left <= start < end <= right <= sender.observed
            and earlier.payload[start - left : end - left] == segment.payload
        ):
            return True
    return False


def data_admission(sender, peer, segment, history=()):
    if segment.options:
        return None, "options"
    if segment.flags not in (16, 24):
        return None, "flags"
    fresh = segment.sequence == sender.next
    if not fresh and not known_range(sender, segment, history):
        return None, "sequence"
    if len(segment.payload) > sender.data_limit:
        return None, "data" if fresh else "sequence"
    offset = endpoint.signed_offset(peer.base, segment.acknowledgment)
    if not 0 <= offset <= peer.observed or peer.acknowledged - offset > 65535:
        return None, "acknowledgment" if fresh else "sequence"
    if fresh and segment.payload and sender.outstanding + len(segment.payload) > sender.peer_window:
        return None, "window"
    after_sender = replace(
        sender, observed=sender.observed + (len(segment.payload) if fresh else 0)
    )
    after_peer = replace(peer, acknowledged=max(peer.acknowledged, offset))
    sequence_age = endpoint.signed_offset(peer.window_sequence, segment.sequence)
    ack_age = endpoint.signed_offset(peer.window_acknowledgment, segment.acknowledgment)
    if offset >= peer.acknowledged and (sequence_age > 0 or sequence_age == 0 and ack_age >= 0):
        after_peer = replace(
            after_peer,
            peer_window=segment.window,
            window_sequence=segment.sequence,
            window_acknowledgment=segment.acknowledgment,
        )
    if not after_sender.valid or not after_peer.valid:
        return None, "epoch" if fresh else "sequence"
    return (after_sender, after_peer), None


def admit(before, record, direction, fresh, raw):
    packet = wire.decode_packet(raw)
    segment = packet.segment
    if before.phase == "empty":
        if not fresh or direction != "original":
            return None, "missingHistory"
        reason = startup_failure(segment, 2)
        if reason:
            return None, reason
        after = replace(
            before,
            phase="syn",
            record=record,
            client_iss=segment.sequence,
            client_window=segment.window,
            client_mss=handshake.startup_mss(segment.options),
        )
    else:
        if fresh or not same_binding(before.record, record):
            return None, "replacement"
        if before.phase in ("syn", "synAck"):
            if direction != ("reply" if before.phase == "syn" else "original"):
                return None, "direction"
            reason = startup_failure(segment, 18 if before.phase == "syn" else 16)
            if reason:
                return None, reason
            if before.phase == "syn":
                if segment.acknowledgment != (before.client_iss + 1) % wire.MODULUS:
                    return None, "acknowledgment"
                after = replace(
                    before,
                    phase="synAck",
                    server_iss=segment.sequence,
                    server_window=segment.window,
                    server_mss=handshake.startup_mss(segment.options),
                )
            else:
                if segment.sequence != (before.client_iss + 1) % wire.MODULUS:
                    return None, "sequence"
                if segment.acknowledgment != (before.server_iss + 1) % wire.MODULUS:
                    return None, "acknowledgment"
                original = Lane(
                    (before.client_iss + 1) % wire.MODULUS,
                    0,
                    0,
                    before.server_window,
                    before.server_iss,
                    (before.client_iss + 1) % wire.MODULUS,
                    before.server_mss,
                )
                reply = Lane(
                    (before.server_iss + 1) % wire.MODULUS,
                    0,
                    0,
                    segment.window,
                    segment.sequence,
                    segment.acknowledgment,
                    before.client_mss,
                )
                after = replace(before, phase="data", original=original, reply=reply)
        else:
            sender, peer = (
                (before.original, before.reply)
                if direction == "original"
                else (before.reply, before.original)
            )
            history = tuple(row[3] for row in before.observations if row[4] == direction)
            lanes, reason = data_admission(sender, peer, segment, history)
            if reason:
                return None, reason
            after = (
                replace(before, original=lanes[0], reply=lanes[1])
                if direction == "original"
                else replace(before, original=lanes[1], reply=lanes[0])
            )
    observation = (record.zone, bytes.fromhex(raw), packet.header, segment, direction, fresh)
    return replace(after, observations=before.observations + (observation,)), None


def commit_admission(admitted, selected, fresh, records):
    if any(same_binding(record, selected) for record in records):
        return admitted, None
    return (Admission(), None) if fresh else (None, "historyLost")


def traffic_matches(traffic, header):
    for field, value in (("source", header.source), ("destination", header.destination)):
        if traffic.get(field) is not None:
            prefix = traffic[field]
            network = ipaddress.IPv4Network((prefix["address"], prefix["length"]), strict=False)
            if ipaddress.IPv4Address(value) not in network:
                return False
    if traffic.get("protocol") is not None and traffic["protocol"] != header.protocol:
        return False
    for field, value in (
        ("sourcePorts", header.source_port),
        ("destinationPorts", header.destination_port),
    ):
        if (
            traffic.get(field) is not None
            and not traffic[field]["first"] <= value <= traffic[field]["last"]
        ):
            return False
    return True


def ingress_permits(source, interface, header):
    chain, rules = selected_chain(source["ruleset"], "prerouting")
    indices = {binding["name"]: binding["reference"]["ifindex"] for binding in source["bindings"]}
    for rule in rules:
        accepted = True
        for expression in rule["expr"]:
            if "match" not in expression:
                continue
            match = expression["match"]
            if match["left"].get("meta", {}).get("key") == "iif":
                selected = match["right"]
                selected = indices[selected] if isinstance(selected, str) else selected
                accepted &= interface == selected
            else:
                accepted &= expression_match(expression, header, "new")
        if accepted:
            return any("accept" in expression for expression in rule["expr"])
    return chain["policy"] == "accept"


def representative_headers(*values):
    limits = [wire.MODULUS, wire.MODULUS, 256, 65536, 65536]
    cuts = [{0} for _ in limits]

    def interval(dimension, low, high):
        cuts[dimension].add(low)
        if high + 1 < limits[dimension]:
            cuts[dimension].add(high + 1)

    def visit(value):
        if isinstance(value, list):
            for row in value:
                visit(row)
        elif isinstance(value, dict):
            for field, dimension in (("source", 0), ("destination", 1)):
                prefix = value.get(field)
                if isinstance(prefix, dict) and "length" in prefix:
                    network = ipaddress.IPv4Network(
                        (prefix["address"], prefix["length"]), strict=False
                    )
                    interval(
                        dimension, int(network.network_address), int(network.broadcast_address)
                    )
            for field, dimension in (("sourcePorts", 3), ("destinationPorts", 4)):
                ports = value.get(field)
                if isinstance(ports, dict):
                    interval(dimension, ports["first"], ports["last"])
            if isinstance(value.get("protocol"), int):
                interval(2, value["protocol"], value["protocol"])
            if "left" in value and "right" in value:
                left, right = value["left"], value["right"]
                payload = left.get("payload", {})
                if payload.get("protocol") == "ip" and payload.get("field") in ("saddr", "daddr"):
                    dimension = 0 if payload["field"] == "saddr" else 1
                    if isinstance(right, str):
                        network = ipaddress.IPv4Network(right)
                        interval(
                            dimension, int(network.network_address), int(network.broadcast_address)
                        )
                    elif "prefix" in right:
                        prefix = right["prefix"]
                        network = ipaddress.IPv4Network(
                            (prefix["addr"], prefix["len"]), strict=False
                        )
                        interval(
                            dimension, int(network.network_address), int(network.broadcast_address)
                        )
                elif payload.get("protocol") in ("tcp", "udp"):
                    protocol = 6 if payload["protocol"] == "tcp" else 17
                    interval(2, protocol, protocol)
                    dimension = 3 if payload["field"] == "sport" else 4
                    if isinstance(right, int):
                        interval(dimension, right, right)
                    elif "range" in right:
                        interval(dimension, *right["range"])
                elif (
                    left.get("meta", {}).get("key") == "l4proto"
                    or payload.get("field") == "protocol"
                ):
                    protocol = {"tcp": 6, "udp": 17, "icmp": 1}.get(right, right)
                    if isinstance(protocol, int):
                        interval(2, protocol, protocol)
            for child in value.values():
                visit(child)

    for value in values:
        visit(value)
    for source, destination, protocol, source_port, destination_port in product(*map(sorted, cuts)):
        yield wire.Header(
            str(ipaddress.IPv4Address(source)),
            str(ipaddress.IPv4Address(destination)),
            protocol,
            source_port,
            destination_port,
        )


@lru_cache(maxsize=256)
def forward_equivalent(snapshot_json, allowed_json):
    snapshot, allowed = json.loads(snapshot_json), json.loads(allowed_json)
    for header in representative_headers(snapshot, allowed):
        expected = any(traffic_matches(traffic, header) for traffic in allowed)
        for classification in ("new", "established", "related", "invalid", "untracked"):
            if filter_permits(snapshot, "forward", header, classification) != expected:
                return False
    return True


@lru_cache(maxsize=256)
def ingress_equivalent(source_json, allowed_json):
    source, allowed = json.loads(source_json), json.loads(allowed_json)
    indices = {
        0,
        *(binding["reference"]["ifindex"] for binding in source["bindings"]),
        *(row["ingress"]["ifindex"] for row in allowed),
    }
    _, rules = selected_chain(source["ruleset"], "prerouting")
    for rule in rules:
        for expression in rule["expr"]:
            match = expression.get("match", {})
            if match.get("left", {}).get("meta", {}).get("key") == "iif" and isinstance(
                match["right"], int
            ):
                indices.add(match["right"])
    extra = next(index for index in range(len(indices) + 1) if index not in indices)
    indices.add(extra)
    for header in representative_headers(source, allowed):
        for index in indices:
            expected = any(
                row["ingress"]["ifindex"] == index and traffic_matches(row["match"], header)
                for row in allowed
            )
            if ingress_permits(source, index, header) != expected:
                return False
    return True


def canonical_event(event):
    event = dict(event)
    if "payloadHex" in event:
        event["payloadHex"] = wire.hex_bytes(event["payloadHex"]).hex()
    if "rawIPv4Hex" in event:
        event["rawIPv4Hex"] = wire.hex_bytes(event["rawIPv4Hex"]).hex()
    if event.get("observed") is not None:
        event["observed"] = {
            "inputHex": wire.hex_bytes(event["observed"]["inputHex"]).hex(),
            "outputHex": None
            if event["observed"]["outputHex"] is None
            else wire.hex_bytes(event["observed"]["outputHex"]).hex(),
        }
    return event


def replay(value, driver=None):
    authentication = value["authentication"]
    context, link = authentication["context"], authentication["link"]
    active, passive = (
        handshake.Local.from_dict(value["active"]),
        handshake.Local.from_dict(value["passive"]),
    )
    if not active.valid or not passive.valid:
        raise ValueError("The endpoint configuration is invalid.")
    configurations = {row["id"]: row for row in value["configs"]}
    guards = {row["id"]: row["source"] for row in value["guards"]}
    specifications = {row["id"]: row for row in value["specifications"]}
    canonical = canonical_event if driver is None else driver.canonical_event
    evaluate = endpoint.evaluate if driver is None else driver.evaluate
    wrap = (lambda state: state) if driver is None else driver.wrap
    events = [canonical(event) for event in value["events"]]
    auth = Authentication()
    after = 0
    configuration, guard = value["initialConfig"], value["initialGuard"]
    startup = handshake.State()
    endpoints = {"client": None, "server": None}
    established = {"client": None, "server": None}
    attachments = []
    records = ()
    admission = Admission()
    outputs, tickets, services, steps, reads = [], [], [], [], []
    supported = compliant = True

    def current_attachments():
        return [
            row["specification"]
            for row in attachments
            if row["round"] == auth.round
            and row["after"] <= after
            and value["authenticationPort"] in value["live"]
            and row["specification"]["ingress"] in value["live"]
            and row["specification"]["ingress"]["namespace"] == value["namespace"]
            and auth.permits(context, value["application"])
        ]

    def comparisons():
        allowed = [
            row["match"]
            for row in value["intent"]["requirements"]
            if auth.permits(context, row["scope"])
        ]
        forward_ok = forward_equivalent(
            json.dumps(configurations[configuration]["forward"], sort_keys=True),
            json.dumps(allowed, sort_keys=True),
        )
        ingress_ok = ingress_equivalent(
            json.dumps(guards[guard], sort_keys=True),
            json.dumps(current_attachments(), sort_keys=True),
        )
        return {"forward": forward_ok, "ingress": ingress_ok}

    def snapshot():
        return {
            "after": after,
            "configuration": configuration,
            "guard": guard,
            "activePhase": startup.active_phase,
            "passivePhase": startup.passive_phase,
            "activeEstablishedAt": established["client"],
            "passiveEstablishedAt": established["server"],
            "client": None if endpoints["client"] is None else endpoints["client"].to_dict(),
            "server": None if endpoints["server"] is None else endpoints["server"].to_dict(),
            "admissionPhase": admission.phase,
            "admissionObservations": len(admission.observations),
            "records": [
                {
                    "zone": row.zone,
                    "original": row.original.to_dict(),
                    "translated": row.translated.to_dict(),
                    "seenReply": row.seen_reply,
                }
                for row in records
            ],
            "outputs": len(outputs),
            "pendingTickets": [row["id"] for row in tickets if row["pending"]],
            "services": len(services),
        }

    initial = snapshot()
    for index, event in enumerate(events):
        kind, before = event["kind"], snapshot()
        before_endpoint = None
        decision = {"kind": "accepted", "operation": kind}
        passed = True
        output = decoded = service = None
        startup_operation = None
        read = b""
        actor = event.get("actor")
        if kind == "authentication":
            if event["index"] != after or after >= len(authentication["events"]):
                raise ValueError("Authentication events must follow their actual order.")
            auth, matched = authentication_step(
                auth, context, link, authentication["events"][after]
            )
            after += 1
            passed = matched
        elif kind == "install":
            configuration = event["configuration"]
            if configuration not in configurations:
                raise ValueError("The installed configuration has no source.")
            passed = comparisons()["forward"]
        elif kind == "installGuard":
            guard = event["guard"]
            if guard not in guards:
                raise ValueError("The installed ingress guard has no source.")
            passed = comparisons()["ingress"]
        elif kind == "stage":
            specification = specifications[event["specification"]]
            if (
                value["authenticationPort"] not in value["live"]
                or specification["ingress"] not in value["live"]
            ):
                raise ValueError("An attachment interface lifetime is not current.")
            if not auth.permits(context, value["application"]):
                raise ValueError("The current session does not permit attachment staging.")
            attachments.append(
                {"specification": specification, "after": after, "round": auth.round}
            )
        elif kind == "open":
            if startup.passive_phase == "ESTABLISHED":
                decision = {"kind": "unsupported", "reason": "startupCopy"}
            else:
                result = handshake.evaluate(
                    active,
                    passive,
                    startup,
                    {
                        "kind": "activeOpen",
                        "remote": event["remote"],
                        "policyPermitted": event["policyPermitted"],
                    },
                    index,
                )
                startup, decision, output = result.state, result.decision, result.output
            actor = "client"
            startup_operation = "activeOpen"
        elif kind in ("write", "send", "read", "emitAck") or (
            driver is not None and kind in driver.EVENTS
        ):
            if endpoints[actor] is None or startup.passive_phase != "ESTABLISHED":
                decision = {"kind": "unsupported", "reason": "phase"}
            else:
                before_endpoint = endpoints[actor]
                result = evaluate(
                    endpoints[actor], {key: item for key, item in event.items() if key != "actor"}
                )
                endpoints[actor], decision, output, read = (
                    result.state,
                    result.decision,
                    result.output,
                    result.read,
                )
                if kind == "read" and decision["kind"] == "accepted":
                    reads.append({"index": index, "actor": actor, "readHex": read.hex()})
        elif kind == "assign":
            if not 0 <= event["output"] < len(outputs):
                raise ValueError("The assignment has no earlier endpoint output.")
            tickets.append(
                {
                    "id": len(tickets),
                    "output": event["output"],
                    "ingress": event["ingress"],
                    "assignedAt": index,
                    "pending": True,
                }
            )
        elif kind == "serve":
            if not 0 <= event["ticket"] < len(tickets) or not tickets[event["ticket"]]["pending"]:
                raise ValueError("The service has no pending immutable ticket.")
            ticket = tickets[event["ticket"]]
            source = outputs[ticket["output"]]
            ingress, raw = ticket["ingress"], source["rawIPv4Hex"]
            if ingress not in value["live"] or ingress["namespace"] != value["namespace"]:
                raise ValueError("The service ingress lifetime is not current in this namespace.")
            packet = wire.decode_packet(raw)
            checks = comparisons()
            covered = any(
                traffic_matches(row["match"], packet.header) for row in value["specifications"]
            )
            checks["coverage"] = covered
            if not ingress_permits(guards[guard], ingress["ifindex"], packet.header):
                disposition, service_output, selected_direction, hop = "earlyDrop", None, None, None
            else:
                _, selected, selected_direction, fresh = attachment(
                    records, configurations[configuration], packet.header, value["zone"]
                )
                candidate, reason = admit(admission, selected, selected_direction, fresh, raw)
                if reason:
                    decision = {"kind": "unsupported", "reason": reason}
                    disposition, service_output, hop = "unsupported", None, None
                else:
                    result = forward(
                        records, value["routing"], configurations[configuration], raw, value["zone"]
                    )
                    next_admission, reason = commit_admission(
                        candidate, selected, fresh, result.records
                    )
                    if reason:
                        decision = {"kind": "unsupported", "reason": reason}
                        disposition, service_output, hop = "unsupported", None, None
                    else:
                        records, admission = result.records, next_admission
                        disposition, service_output, hop = (
                            result.disposition,
                            result.output,
                            result.next_hop,
                        )
            if decision["kind"] != "unsupported":
                matched = event["observed"] is None or event["observed"] == {
                    "inputHex": raw,
                    "outputHex": None if service_output is None else service_output["rawIPv4Hex"],
                }
                role_ok = service_output is None or hop == (
                    "server" if source["actor"] == "client" else "client"
                )
                service = {
                    "id": len(services),
                    "index": index,
                    "ticket": ticket["id"],
                    "outputID": source["id"],
                    "actor": source["actor"],
                    "sourceKind": source["kind"],
                    "inputHex": raw,
                    "output": service_output,
                    "disposition": disposition,
                    "direction": selected_direction,
                    "nextHop": hop,
                    "checks": checks,
                    "observationsMatch": matched,
                    "routeRoleMatch": role_ok,
                }
                services.append(service)
                ticket["pending"] = False
                passed = all(checks.values()) and matched and role_ok
        elif kind == "deliver":
            if not 0 <= event["service"] < len(services):
                raise ValueError("The delivery has no earlier actual service.")
            service = services[event["service"]]
            if service["output"] is None or event["rawIPv4Hex"] != service["output"]["rawIPv4Hex"]:
                raise ValueError("The receipt differs from the actual earlier service emission.")
            decoded = wire.decode_packet(event["rawIPv4Hex"]).to_dict()
            actor = "server" if service["actor"] == "client" else "client"
            if startup.passive_phase != "ESTABLISHED":
                produced = outputs[service["outputID"]]
                operation = {
                    "activeOpen": "listenSyn",
                    "listenSyn": "synSentSynAck",
                    "synSentSynAck": "synReceivedAck",
                }.get(produced["startupOperation"], "invalid")
                expected_actor = "client" if operation == "synSentSynAck" else "server"
                if actor != expected_actor:
                    decision = {"kind": "unsupported", "reason": "phase"}
                else:
                    result = handshake.evaluate(
                        active,
                        passive,
                        startup,
                        {
                            "kind": operation,
                            "rawIPv4Hex": event["rawIPv4Hex"],
                            "path": "rewrite",
                            "policyPermitted": event["policyPermitted"],
                        },
                        index,
                    )
                    startup, decision, output = (
                        result.state,
                        result.decision,
                        result.output,
                    )
                    startup_operation = operation
                    if startup.active_seed is not None and endpoints["client"] is None:
                        endpoints["client"], established["client"] = (
                            wrap(startup.active_seed),
                            index,
                        )
                    if startup.passive_seed is not None and endpoints["server"] is None:
                        endpoints["server"], established["server"] = (
                            wrap(startup.passive_seed),
                            index,
                        )
            elif service["sourceKind"] not in ("send", "emitAck", "retry"):
                decision = {"kind": "unsupported", "reason": "startupCopy"}
            else:
                result = evaluate(
                    endpoints[actor], {"kind": "receive", "rawIPv4Hex": event["rawIPv4Hex"]}
                )
                endpoints[actor], decision = result.state, result.decision
        else:
            raise ValueError("The campus event kind is unknown.")
        if output is not None:
            attempt = None if driver is None else driver.attempt(before_endpoint, event)
            outputs.append(
                {
                    "id": len(outputs),
                    "index": index,
                    "actor": actor,
                    "kind": (kind if kind != "deliver" else "startup")
                    if driver is None
                    else driver.output_kind(event),
                    "startupOperation": startup_operation,
                    **({} if attempt is None else {"attempt": attempt}),
                    **output,
                }
            )
        steps.append(
            {
                "index": index,
                "event": event,
                "before": before,
                "decision": decision,
                "supported": decision["kind"] != "unsupported",
                "passed": passed,
                "output": output,
                "decodedInput": decoded,
                "readHex": read.hex(),
                "service": service if kind == "serve" else None,
                "state": snapshot(),
            }
        )
        compliant &= passed
        if decision["kind"] == "unsupported":
            supported = compliant = False
            break
    return {
        "supported": supported,
        "compliant": bool(compliant),
        "inputEvents": len(events),
        "evaluatedEvents": len(steps),
        "initial": initial,
        "steps": steps,
        "final": snapshot(),
        "outputs": outputs,
        "services": services,
        "reads": reads,
        "remainingEvents": events[len(steps) :],
    }


def load(name):
    return json.loads((DIRECTORY / (name + ".json")).read_text())
