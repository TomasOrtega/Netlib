"""Independent packet custody for the joint campus replay.

Only actual endpoint outputs and gateway emissions create original packets.
"""

import copy
import json
from dataclasses import dataclass, field
from pathlib import Path

DIRECTORY = Path(__file__).resolve().parent.parent / "examples/packet-custody"


@dataclass(frozen=True)
class Packet:
    id: int
    parent: int | None
    stage: str
    source: int
    raw: str

    def to_dict(self):
        return {
            "id": self.id,
            "parent": self.parent,
            "stage": self.stage,
            "source": self.source,
            "rawIPv4Hex": self.raw,
        }


@dataclass
class Custody:
    packets: list = field(default_factory=list)
    pending: list = field(default_factory=list)
    resolved: list = field(default_factory=list)

    def mint(self, stage, source, raw, parent=None):
        packet = Packet(len(self.packets), parent, stage, source, raw)
        self.packets.append(packet)
        self.pending.append(packet.id)
        return packet

    def copy(self, identity):
        if type(identity) is not int or not 0 <= identity < len(self.packets):
            raise ValueError("The packet source does not exist.")
        source = self.packets[identity]
        return self.mint(source.stage, source.source, source.raw, source.id)

    def resolve(self, identity, kind):
        if type(identity) is not int or identity not in self.pending:
            raise ValueError("The packet identity is not pending.")
        self.pending.remove(identity)
        self.resolved.append({"packet": identity, "kind": kind})
        return self.packets[identity]

    def consume(self, stage, source, kind):
        identity = next(
            (
                identity
                for identity in self.pending
                if self.packets[identity].stage == stage and self.packets[identity].source == source
            ),
            None,
        )
        if identity is None:
            if stage == "ingress":
                raise ValueError("No pending ingress packet remains for this endpoint output.")
            raise ValueError("No pending receiver-link packet remains for this gateway service.")
        return self.resolve(identity, kind)

    def snapshot(self):
        return {
            "nextID": len(self.packets),
            "pending": list(self.pending),
            "resolved": [dict(row) for row in self.resolved],
            "copies": sum(packet.parent is not None for packet in self.packets),
        }

    def inventory(self):
        return [packet.to_dict() for packet in self.packets]

    def assurance(self):
        return {
            "scope": "automatic-packet-custody",
            "status": "checked",
            "pending": len(self.pending),
            **{
                kind: sum(row["kind"] == kind for row in self.resolved)
                for kind in ("assigned", "delivered", "dropped")
            },
            "copies": sum(packet.parent is not None for packet in self.packets),
        }


def replay(value):
    import campus_tcp_recovery_reference as recovery

    return recovery.replay(value)


def projection(report):
    import campus_tcp_recovery_reference as recovery

    return recovery.projection(report)


def load_fixtures():
    data = json.loads((DIRECTORY / "fixtures.json").read_text())
    for key in ("cases", "inputErrors"):
        for case in data[key]:
            value = copy.deepcopy(data["input"])
            for replacement in case.get("replacements", []):
                if not replacement["path"]:
                    value = copy.deepcopy(replacement["value"])
                    continue
                target = value
                for name in replacement["path"][:-1]:
                    target = target[name]
                target[replacement["path"][-1]] = copy.deepcopy(replacement["value"])
            case["input"] = value
    return data
