"""Inspect supplied pre-defragmentation guards without claiming a native capture."""

import ipaddress

from attachment_capture_evidence import resolve_iif
from capture_evidence import require

TABLE = "netlib_fragment_attachment"
CHAIN = "early_ingress"


def _host(value):
    if isinstance(value, dict):
        require(
            set(value) == {"prefix"}
            and set(value["prefix"]) == {"addr", "len"}
            and type(value["prefix"]["len"]) is int
            and value["prefix"]["len"] == 32,
            "The selected early guard requires exact IPv4 hosts.",
        )
        value = value["prefix"]["addr"]
    require(isinstance(value, str), "Early guard address is not a native IPv4 string.")
    return str(ipaddress.IPv4Address(value))


def canonical_fragment_rule(rule, links, *, transaction=False):
    require(
        set(rule) <= {"family", "table", "chain", "handle", "comment", "expr"}
        and (rule["family"], rule["table"], rule["chain"]) == ("ip", TABLE, CHAIN)
        and rule.get("comment") in {"SYNC", "ORIGINAL", "REPLY", "FALLBACK"},
        "Unexpected pre-defragmentation guard rule identity or role.",
    )
    expressions = rule["expr"]
    require(
        isinstance(expressions, list)
        and expressions
        and expressions[-1] in ({"accept": None}, {"drop": None}),
        "Early guard lacks a supported final verdict.",
    )
    result = {
        "role": rule["comment"],
        "verdict": "accept" if expressions[-1] == {"accept": None} else "drop",
    }
    fields = {}
    for expression in expressions[:-1]:
        if set(expression) == {"log"}:
            prefix = "FRAG_ALLOW" if result["verdict"] == "accept" else "FRAG_DROP"
            require(
                "log" not in result
                and all(
                    type(expression["log"].get(key)) is int
                    for key in ("group", "snaplen", "queue-threshold")
                )
                and expression["log"]
                == {"prefix": prefix, "group": 42, "snaplen": 65531, "queue-threshold": 1},
                "Early guard log contradicts its decision or raw evidence contract.",
            )
            result["log"] = prefix
            continue
        require(
            set(expression) == {"match"} and "log" not in result,
            "Unsupported early effect or predicate after its log.",
        )
        match = expression["match"]
        require(
            set(match) == {"left", "right", "op"} and match["op"] == "==",
            "Early predicates must be exact equalities.",
        )
        left, right = match["left"], match["right"]
        if left == {"meta": {"key": "iif"}}:
            require(
                "ifindex" not in result and (not transaction or type(right) is int),
                "Early input identity must be one actual numeric installation.",
            )
            result["ifindex"] = resolve_iif(expression, links)
            continue
        require(
            isinstance(left, dict)
            and set(left) == {"payload"}
            and set(left["payload"]) == {"protocol", "field"}
            and left["payload"]["protocol"] == "ip"
            and left["payload"]["field"] in {"saddr", "daddr", "protocol"},
            "Early fragment guard may read only IPv4 addresses/protocol and numeric iif.",
        )
        field = left["payload"]["field"]
        if field == "protocol":
            require(
                (type(right) is int and right == 17) or (not transaction and right == "udp"),
                "Early protected protocol must be actual IPv4 UDP.",
            )
            key, value = "protocol", 17
        else:
            key, value = ("source" if field == "saddr" else "destination"), _host(right)
        require(key not in fields, "Duplicate early IPv4 envelope predicate.")
        fields[key] = value
    if fields:
        require(
            set(fields) == {"source", "destination", "protocol"}
            and "ifindex" in result
            and result["verdict"] == "accept"
            and (
                result.get("log") == "FRAG_ALLOW"
                or result["role"] == "SYNC"
                and "log" not in result
            ),
            "Early allow omits its complete protected envelope, interface, or observation.",
        )
        result["envelope"] = fields
    else:
        require(
            result == {"role": "FALLBACK", "verdict": "drop", "log": "FRAG_DROP"},
            "Early fallback must unconditionally log and drop.",
        )
    return result


def canonical_fragment_guard(document, links, *, transaction=False, replace=False):
    require(
        isinstance(document, dict) and set(document) == {"nftables"},
        "Malformed early ruleset envelope.",
    )
    rows = document["nftables"]
    require(
        isinstance(rows, list) and all(isinstance(row, dict) and len(row) == 1 for row in rows),
        "Malformed early ruleset objects.",
    )
    objects = {
        kind: [row[kind] for row in rows if kind in row]
        for kind in ("metainfo", "delete", "table", "chain", "rule")
    }
    require(
        sum(map(len, objects.values())) == len(rows), "Unsupported early ruleset object or bypass."
    )
    require(
        len(objects["metainfo"]) == len(objects["table"]) == len(objects["chain"]) == 1,
        "Early ruleset requires one table, one hook, and one producer envelope.",
    )
    metadata = objects["metainfo"][0]
    require(
        type(metadata.get("json_schema_version")) is int
        and (
            metadata == {"json_schema_version": 1}
            if transaction
            else metadata.get("version") == "1.1.3" and metadata["json_schema_version"] == 1
        ),
        "Unexpected early ruleset producer or JSON schema.",
    )
    require(
        objects["delete"]
        == ([{"table": {"family": "ip", "name": TABLE}}] if transaction and replace else []),
        "Early table replacement must be explicit and limited to its own table.",
    )
    require(
        [next(iter(row)) for row in rows]
        == ["metainfo"]
        + (["delete"] if transaction and replace else [])
        + ["table", "chain"]
        + ["rule"] * len(objects["rule"]),
        "Early objects must preserve delete, table creation, chain creation, and ordered rules.",
    )
    require(
        {key: value for key, value in objects["table"][0].items() if key != "handle"}
        == {"family": "ip", "name": TABLE}
        and {key: value for key, value in objects["chain"][0].items() if key != "handle"}
        == {
            "family": "ip",
            "table": TABLE,
            "name": CHAIN,
            "type": "filter",
            "hook": "prerouting",
            "prio": -450,
            "policy": "drop",
        },
        "Early attachment hook must deny by default before IPv4 defragmentation.",
    )
    rules = [
        canonical_fragment_rule(rule, links, transaction=transaction) for rule in objects["rule"]
    ]
    require(
        rules
        and rules[-1] == {"role": "FALLBACK", "verdict": "drop", "log": "FRAG_DROP"}
        and all(rule["role"] != "FALLBACK" for rule in rules[:-1]),
        "Early ruleset lacks one final unconditional drop.",
    )
    return rules


def installed_allows(rules, index, packet):
    for rule in rules:
        if "envelope" not in rule or (
            index == rule["ifindex"]
            and all(packet[key] == value for key, value in rule["envelope"].items())
        ):
            return rule["verdict"] == "accept"
    return False


def compare_current(rules, index, packet, expected_allowed):
    require(type(expected_allowed) is bool, "Missing current attachment decision.")
    actual = installed_allows(rules, index, packet)
    return {
        "actualAllowed": actual,
        "expectedAllowed": expected_allowed,
        "mismatch": actual != expected_allowed,
    }


def maintenance_separated(rules, applications):
    require(
        applications
        and all(set(row) == {"source", "destination", "protocol"} for row in applications),
        "Missing protected coarse application envelopes.",
    )
    for rule in rules:
        if rule["role"] == "SYNC":
            require(
                all(
                    any(rule["envelope"][key] != application[key] for key in application)
                    for application in applications
                ),
                "Maintenance exception overlaps a protected fragment envelope after ports are erased.",
            )
    return True
