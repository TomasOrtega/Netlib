"""Check complete network inventories for the attachment capture profile."""

import ipaddress
import json

import check_eap_capture as eap
from attachment_capture_evidence import INTERFACES, LINKS, OPPOSITE
from capture_evidence import require


def _prefix(name):
    return 30 if name in {"aal", "aar", "abl", "abr"} else 24


def _linkdown(name, fenced, withdrawn):
    return (fenced and name in {"cal", "sal"}) or (withdrawn and name in {"syncr", "aal"})


def _sort_key(row):
    return json.dumps(row, sort_keys=True)


def _routes(actor, owners, fenced, withdrawn):
    routes = []
    for name, (address, _) in LINKS[actor].items():
        if fenced and actor == "a" and name in {"car", "sar"}:
            continue
        routes.append(
            {
                "dst": str(ipaddress.IPv4Network(f"{address}/{_prefix(name)}", strict=False)),
                "dev": name,
                "protocol": "kernel",
                "scope": "link",
                "prefsrc": address,
                "flags": ["linkdown"] if _linkdown(name, fenced, withdrawn) else [],
            }
        )
    if actor == "client":
        primary = owners["original"] == "a"
        routes.append(
            {
                "dst": "203.0.113.2",
                "gateway": "192.0.2.1" if primary else "192.0.3.1",
                "dev": "cal" if primary else "cbl",
                "prefsrc": "192.0.2.2",
                "flags": [],
            }
        )
    elif actor == "server":
        primary = owners["reply"] == "a"
        routes.append(
            {
                "dst": "203.0.113.1",
                "gateway": "198.51.100.1" if primary else "198.51.101.1",
                "dev": "sal" if primary else "sbl",
                "prefsrc": "198.51.100.2",
                "flags": [],
            }
        )
    elif actor in {"a", "b"}:
        routes.append({"type": "blackhole", "dst": "203.0.113.1", "flags": []})
        if actor == "b":
            routes.extend(
                [
                    {
                        "dst": "192.0.2.2",
                        "gateway": "192.0.3.2",
                        "dev": "cbr",
                        "flags": [],
                    },
                    {
                        "dst": "198.51.100.2",
                        "gateway": "198.51.101.2",
                        "dev": "sbr",
                        "flags": [],
                    },
                ]
            )
    return routes


def check_network(boundary, owners, fenced, modes, withdrawn, auth_link):
    require(
        set(owners) == {"original", "reply"}
        and all(owner in {"a", "b"} for owner in owners.values())
        and type(fenced) is bool
        and type(withdrawn) is bool
        and (not withdrawn or fenced)
        and set(modes) <= {"cal", "cbl", "sbl"},
        "Unsupported network ownership, fence, withdrawal, or queue state.",
    )
    require(
        set(boundary["networks"]) == set(LINKS) - ({"a"} if withdrawn else set()),
        "Missing live namespace network readbacks or a live withdrawn primary.",
    )
    for actor, documents in boundary["networks"].items():
        require(
            set(documents) == {"links", "addresses", "routes", "rules", "neighbors"},
            "Unsupported namespace network inventory.",
        )
        links = documents["links"]
        names = {"lo", *LINKS[actor]} | ({"peer0"} if actor == "client" else set())
        require(
            len(links) == len(names) and {row["ifname"] for row in links} == names,
            "Unexpected namespace link inventory.",
        )
        indices = [row["ifindex"] for row in links]
        require(
            all(type(index) is int and 0 < index <= 2**31 - 1 for index in indices)
            and len(indices) == len(set(indices)),
            "Invalid or repeated namespace interface index.",
        )
        for row in links:
            name = row["ifname"]
            fields = {
                "ifindex",
                "ifname",
                "flags",
                "mtu",
                "qdisc",
                "operstate",
                "linkmode",
                "group",
                "txqlen",
                "link_type",
                "address",
                "broadcast",
            }
            if name != "lo":
                fields |= {"link_index", "link_netnsid"}
            require(
                set(row) == fields
                and row["linkmode"] == "DEFAULT"
                and row["group"] == "default"
                and row["txqlen"] == 1000
                and row["broadcast"]
                == ("00:00:00:00:00:00" if name == "lo" else "ff:ff:ff:ff:ff:ff")
                and (
                    name == "lo"
                    or type(row["link_netnsid"]) is int
                    and row["link_netnsid"] >= 0
                    and type(row["link_index"]) is int
                    and 0 < row["link_index"] <= 2**31 - 1
                ),
                "Unsupported native link attributes or queue envelope.",
            )
            if name == "lo":
                require(
                    row["ifindex"] == 1
                    and row["flags"] == ["LOOPBACK", "UP", "LOWER_UP"]
                    and row["link_type"] == "loopback"
                    and row["mtu"] == 65536
                    and row["qdisc"] == "noqueue"
                    and row["operstate"] == "UNKNOWN"
                    and row["address"] == "00:00:00:00:00:00",
                    "Loopback is unavailable.",
                )
                continue
            down = fenced and actor == "a" and name in {"car", "sar"}
            no_carrier = _linkdown(name, fenced, withdrawn)
            flags = (
                ["BROADCAST", "MULTICAST"]
                if down
                else ["NO-CARRIER", "BROADCAST", "MULTICAST", "UP"]
                if no_carrier
                else ["BROADCAST", "MULTICAST", "UP", "LOWER_UP"]
            )
            qdisc = "netem" if name in modes and modes[name] is not None else "noqueue"
            require(
                (row["mtu"], row["address"], row["link_type"], row["qdisc"])
                == (1500, eap.PEER if name == "peer0" else LINKS[actor][name][1], "ether", qdisc)
                and row["flags"] == flags
                and row["operstate"] == ("DOWN" if down or no_carrier else "UP"),
                "Native link queue, MTU, MAC, type, or fence state disagrees.",
            )
            if name != "peer0":
                peer = OPPOSITE[name]
                peer_actor = INTERFACES[peer]
                if peer_actor in boundary["networks"]:
                    peer_links = boundary["networks"][peer_actor]["links"]
                    peer_rows = [value for value in peer_links if value["ifname"] == peer]
                    require(
                        len(peer_rows) == 1 and row["link_index"] == peer_rows[0]["ifindex"],
                        "Native veth peer index contradicts the topology.",
                    )
        if actor == "client":
            require(
                next(row for row in links if row["ifname"] == "peer0") == auth_link,
                "The authenticated client link changed identity or state.",
            )
        require(
            len(documents["addresses"]) == len(links)
            and {row["ifname"] for row in documents["addresses"]} == names,
            "Incomplete address interface inventory.",
        )
        actual_addresses = set()
        for row in documents["addresses"]:
            link = next(value for value in links if value["ifname"] == row["ifname"])
            require(
                {key: value for key, value in row.items() if key != "addr_info"}
                == {key: value for key, value in link.items() if key != "linkmode"}
                and len(row["addr_info"]) == (0 if row["ifname"] == "peer0" else 1),
                "Native address interface attributes contradict the link readback.",
            )
            for value in row["addr_info"]:
                require(
                    set(value)
                    == {
                        "family",
                        "local",
                        "prefixlen",
                        "scope",
                        "label",
                        "valid_life_time",
                        "preferred_life_time",
                    }
                    and value["family"] == "inet"
                    and value["label"] == row["ifname"]
                    and value["scope"] == ("host" if row["ifname"] == "lo" else "global")
                    and type(value["prefixlen"]) is int
                    and type(value["valid_life_time"]) is int
                    and type(value["preferred_life_time"]) is int
                    and value["valid_life_time"] == value["preferred_life_time"] == 2**32 - 1,
                    "Unsupported native address attributes or lifetime.",
                )
                actual_addresses.add((row["ifname"], value["local"], value["prefixlen"]))
        require(
            actual_addresses
            == {("lo", "127.0.0.1", 8)}
            | {(name, value[0], _prefix(name)) for name, value in LINKS[actor].items()},
            "Namespace address inventory disagrees.",
        )
        require(
            sorted(documents["routes"], key=_sort_key)
            == sorted(_routes(actor, owners, fenced, withdrawn), key=_sort_key),
            "Per-leg route owners, selectors, or blackhole readback disagree.",
        )
        require(
            _sort_key(documents["rules"])
            == _sort_key(
                [
                    {"priority": 0, "src": "all", "table": "local"},
                    {"priority": 32766, "src": "all", "table": "main"},
                    {"priority": 32767, "src": "all", "table": "default"},
                ]
            ),
            "Unexpected policy routing rules.",
        )
        neighbors = []
        for name in LINKS[actor]:
            if fenced and actor == "a" and name in {"car", "sar"}:
                continue
            peer = OPPOSITE[name]
            address, mac = LINKS[INTERFACES[peer]][peer]
            neighbors.append({"dst": address, "dev": name, "lladdr": mac, "state": ["PERMANENT"]})
        require(
            sorted(documents["neighbors"], key=_sort_key) == sorted(neighbors, key=_sort_key),
            "Permanent neighbor isolation disagrees.",
        )
