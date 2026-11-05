"""Check retained EAPOL bytes, native TLS results, and logical port observations."""

import argparse
import hashlib
import json
import re
import ssl
import sys
from pathlib import Path

AUTHENTICATOR = "02:00:00:00:ea:01"
PEER = "02:00:00:00:ea:02"
PAE = "01:80:c2:00:00:03"
SUBJECT = "alice@campus.example.test"
OUTER = "anonymous@campus.example.test"
SERVER = "radius.campus.example.test"
METHOD = 13
SOURCES = {
    "hostapd-2.12.tar.gz": "f43502561c28ba47ab77e18e1a973d07361c68cc8b14178e619bd5796b70eabd",
    "wpa_supplicant-2.12.tar.gz": "08e23937e16d0155e55cab2b51f51fbe10d80a1aa91c4e15442645059b737ef6",
}
HEXDUMP = re.compile(r"(RX|TX) EAPOL - hexdump\(len=(\d+)\): ([0-9a-f ]+)$")


class EvidenceError(ValueError):
    """Retained observations contradict the capture profile."""


def require(condition, message):
    if not condition:
        raise EvidenceError(message)


def integer(value):
    return type(value) is int and value >= 0


def read_json(path):
    return json.loads(path.read_text())


def read_lines(path, window):
    rows = [json.loads(line) for line in path.read_text().splitlines()]
    times = [row.get("timeNs") for row in rows]
    require(
        rows
        and all(integer(value) and window["startNs"] < value < window["endNs"] for value in times)
        and all(left < right for left, right in zip(times, times[1:])),
        f"{path.name}: invalid, stale, or unordered capture times.",
    )
    return rows


def decode_frame(row):
    raw = row.get("hex")
    require(isinstance(raw, str) and re.fullmatch(r"(?:[0-9a-f]{2})+", raw), "Invalid frame hex.")
    frame = bytes.fromhex(raw)
    require(len(frame) >= 18 and frame[12:14] == b"\x88\x8e", "Malformed Ethernet EAPOL frame.")
    destination, source = frame[:6].hex(":"), frame[6:12].hex(":")
    version, kind = frame[14:16]
    length = int.from_bytes(frame[16:18], "big")
    require(version == 2 and kind in (0, 1, 2), "Unsupported EAPOL capture profile.")
    require(18 + length <= len(frame), "Truncated EAPOL body length.")
    body, padding = frame[18 : 18 + length], frame[18 + length :]
    require(source in (AUTHENTICATOR, PEER), "Wrong Ethernet peer or authenticator MAC.")
    role = "authenticator" if source == AUTHENTICATOR else "peer"
    require(
        (role == "authenticator" and destination == PEER and row.get("packetType") == 4)
        or (role == "peer" and destination == PAE and row.get("packetType") == 2),
        "Ethernet role, destination, or AF_PACKET direction disagreement.",
    )
    packet = None
    if kind == 0:
        require(len(body) >= 4, "Truncated EAP header.")
        code, identifier = body[:2]
        eap_length = int.from_bytes(body[2:4], "big")
        require(4 <= eap_length <= len(body), "Invalid EAP declared length.")
        require(code in (1, 2, 3, 4), "Unsupported EAP code.")
        require(
            (code == 2 and role == "peer") or (code != 2 and role == "authenticator"),
            "EAP code contradicts the Ethernet role.",
        )
        require(eap_length >= 5 if code < 3 else eap_length == 4, "Invalid EAP code length.")
        packet = {
            "code": code,
            "identifier": identifier,
            "method": body[4] if code < 3 else None,
            "dataHex": body[5:eap_length].hex() if code < 3 else "",
            "paddingHex": body[eap_length:].hex(),
        }
    else:
        require(
            role == "peer" and length == 0, "Start or Logoff contradicts the version 2 profile."
        )
    return {
        "raw": raw,
        "timeNs": row["timeNs"],
        "packetType": row["packetType"],
        "role": role,
        "eapol": {"version": version, "type": kind, "length": length, "paddingHex": padding.hex()},
        "eap": packet,
    }


def one_line(rows, text, source):
    found = [index for index, row in enumerate(rows, 1) if text in row["line"]]
    require(len(found) == 1, f"{source}: missing or duplicate method observation: {text}")
    return {"source": f"{source}:{found[0]}", "timeNs": rows[found[0] - 1]["timeNs"]}


def native_markers(rows, prefix, expected, source, unique=False):
    found = [(index, row) for index, row in enumerate(rows, 1) if row["line"].startswith(prefix)]
    require(
        found
        and all(row["line"] == expected for _, row in found)
        and (not unique or len(found) == 1),
        f"{source}: missing, duplicate, or contradictory native {prefix}",
    )
    return [{"source": f"{source}:{index}", "timeNs": row["timeNs"]} for index, row in found]


def line_order(*references):
    positions = [int(reference["source"].rsplit(":", 1)[1]) for reference in references]
    require(
        all(left < right for left, right in zip(positions, positions[1:])),
        "Native method result order contradicts the authentication exchange.",
    )


def certificate(directory, role, principal, alternative=None):
    path = directory / f"{role}.pem"
    pem = path.read_text()
    require("PRIVATE KEY" not in pem, "Private key retained in a public certificate artifact.")
    der = ssl.PEM_cert_to_DER_cert(pem)
    fingerprint = hashlib.sha256(der).hexdigest()
    details = ssl._ssl._test_decode_cert(str(path))
    require(
        details["subject"] == ((("commonName", principal),),), "Certificate principal disagreement."
    )
    if alternative:
        require(
            alternative in details.get("subjectAltName", ()),
            "Certificate alternate identity disagreement.",
        )
    text = (directory / f"{role}-certificate.txt").read_text()
    printed = ":".join(fingerprint[index : index + 2].upper() for index in range(0, 64, 2))
    require(f"sha256 Fingerprint={printed}" in text, "Certificate fingerprint disagreement.")
    require(f"subject=CN={principal}\n" in text, "Certificate subject export disagreement.")
    return fingerprint


def configuration(directory):
    expected = {
        "interface": "auth0",
        "driver": "wired",
        "ieee8021x": "1",
        "eapol_version": "2",
        "eap_server": "1",
        "ctrl_interface": "/run/netlib-eap/hostapd",
        "eap_user_file": "/run/netlib-eap/users",
        "ca_cert": "/run/netlib-eap/ca-chain.pem",
        "server_cert": "/run/netlib-eap/server.pem",
        "private_key": "/run/netlib-eap/server.key",
        "check_crl": "2",
        "check_crl_strict": "1",
        "check_cert_subject": f"CN={SUBJECT}",
        "tls_session_lifetime": "0",
        "ocsp_stapling_response": "/run/netlib-eap/server.ocsp.der",
        "tls_flags": "[DISABLE-TLSv1.0][DISABLE-TLSv1.1][DISABLE-TLSv1.2][ENABLE-TLSv1.3]",
        "logger_stdout": "-1",
        "logger_stdout_level": "0",
    }
    lines = (directory / "hostapd.conf").read_text().splitlines()
    require(len(lines) == len(expected), "Unexpected or duplicate authenticator configuration.")
    require(
        dict(line.split("=", 1) for line in lines) == expected,
        "Authenticator certificate policy disagreement.",
    )
    require((directory / "users").read_text() == "* TLS\n", "Unexpected EAP user method policy.")
    for name, domain in (("success", SERVER), ("bad-server", "wrong.campus.example.test")):
        lines = (directory / f"{name}-supplicant.conf").read_text().splitlines()
        require(
            lines[3] == "network={" and lines[-1] == "}",
            "Supplicant network configuration disagreement.",
        )
        entries = [
            line.strip().split("=", 1) for line in lines if "=" in line and line != "network={"
        ]
        expected_peer = {
            "ctrl_interface": "/run/netlib-eap/supplicant",
            "eapol_version": "2",
            "ap_scan": "0",
            "key_mgmt": "IEEE8021X",
            "eap": "TLS",
            "identity": f'"{OUTER}"',
            "ca_cert": '"/run/netlib-eap/ca.pem"',
            "client_cert": '"/run/netlib-eap/client.pem"',
            "private_key": '"/run/netlib-eap/client.key"',
            "domain_match": f'"{domain}"',
            "ocsp": "2",
            "phase1": '"tls_disable_tlsv1_0=1 tls_disable_tlsv1_1=1 tls_disable_tlsv1_2=1 tls_disable_tlsv1_3=0"',
        }
        require(
            len(entries) == len(expected_peer) and dict(entries) == expected_peer,
            "Supplicant certificate policy disagreement.",
        )
    for namespace, interface, mac in (("auth", "auth0", AUTHENTICATOR), ("peer", "peer0", PEER)):
        links = [
            row
            for row in read_json(directory / f"{namespace}-links.json")
            if row["ifname"] == interface
        ]
        require(
            len(links) == 1 and links[0]["address"] == mac and "UP" in links[0]["flags"],
            "Namespace link MAC or state disagreement.",
        )


def check_sequence(frames, success):
    require(frames[0]["eapol"]["type"] == 1, "Capture must begin with EAPOL Start.")
    outstanding = None
    previous_identifier = None
    last_response = None
    terminal = None
    logoff = None
    outer = []
    for index, frame in enumerate(frames):
        kind, packet = frame["eapol"]["type"], frame["eap"]
        if kind == 1:
            require(index == 0, "Duplicate or extra Start event.")
            continue
        if kind == 2:
            require(success and terminal is not None and logoff is None, "Unexpected Logoff.")
            logoff = index
            outstanding = None
            continue
        code, identifier = packet["code"], packet["identifier"]
        if code == 1:
            require(
                outstanding is None and identifier != previous_identifier,
                "Duplicate or overlapping EAP Request.",
            )
            require(packet["method"] in (1, METHOD), "Unexpected EAP method.")
            require(
                packet["method"] == METHOD
                or index == 1
                or (logoff is not None and index == len(frames) - 1),
                "Unexpected Identity Request.",
            )
            outstanding = packet
            previous_identifier = identifier
        elif code == 2:
            require(
                outstanding is not None
                and identifier == outstanding["identifier"]
                and packet["method"] == outstanding["method"],
                "Response does not match the outstanding Request identifier or method.",
            )
            if packet["method"] == 1:
                outer.append(bytes.fromhex(packet["dataHex"]).decode())
            outstanding = None
            last_response = packet
        else:
            require(
                terminal is None
                and outstanding is None
                and last_response is not None
                and last_response["method"] == METHOD
                and identifier == last_response["identifier"],
                "Terminal identifier or method does not match the last Response.",
            )
            require(
                code == (3 if success else 4),
                "Terminal result contradicts the native method result.",
            )
            terminal = index
            if success:
                require(
                    last_response["dataHex"] == "00",
                    "TLS protected success needs a final empty method Response.",
                )
    require(
        outer == [OUTER] and terminal is not None, "Missing outer Identity or EAP terminal result."
    )
    require(
        (logoff == terminal + 1 and logoff == len(frames) - 2)
        if success
        else terminal == len(frames) - 1,
        "Unexpected extra or missing terminal events.",
    )
    return terminal, logoff


def check_tls_fragments(frames):
    pending = {}
    flights = []
    starts = 0
    expected_ack = None
    expected_continuation = None
    for frame in frames:
        packet = frame["eap"]
        if packet is None or packet["method"] != METHOD:
            continue
        data = bytes.fromhex(packet["dataHex"])
        require(data and not data[0] & 0x1F, "Invalid TLS fragment flags.")
        flags, fragment = data[0], data[1:]
        role = frame["role"]
        if expected_ack is not None:
            require(
                role == expected_ack and data == b"\x00",
                "TLS fragment ACK must be empty and use the opposite role.",
            )
            expected_ack = None
            continue
        if expected_continuation is not None:
            require(role == expected_continuation, "TLS fragment continuation changed direction.")
            expected_continuation = None
        if flags & 0x20:
            starts += 1
            require(
                role == "authenticator" and flags == 0x20 and not fragment and starts == 1,
                "Invalid TLS Start fragment.",
            )
            continue
        require(starts == 1, "TLS fragment before method Start.")
        if flags & 0x80:
            require(
                role not in pending and len(fragment) >= 4, "Invalid TLS fragment length header."
            )
            declared, fragment = int.from_bytes(fragment[:4], "big"), fragment[4:]
            pending[role] = (declared, b"")
        if not fragment and flags == 0:
            require(role not in pending, "Empty TLS fragment interrupts its own flight.")
            continue
        declared, previous = pending.get(role, (len(fragment), b""))
        payload = previous + fragment
        require(len(payload) <= declared, "TLS fragment flight exceeds its declared length.")
        if flags & 0x40:
            require(
                role in pending and len(payload) < declared,
                "TLS fragment continuation lacks a valid total length.",
            )
            pending[role] = (declared, payload)
            expected_ack = "peer" if role == "authenticator" else "authenticator"
            expected_continuation = role
            continue
        require(len(payload) == declared, "TLS fragment flight does not match its declared length.")
        pending.pop(role, None)
        record_types, cursor = [], 0
        while cursor < len(payload):
            require(cursor + 5 <= len(payload), "Truncated TLS record header.")
            kind, version = payload[cursor], payload[cursor + 1 : cursor + 3]
            size = int.from_bytes(payload[cursor + 3 : cursor + 5], "big")
            require(
                kind in (20, 21, 22, 23)
                and version in (b"\x03\x01", b"\x03\x03")
                and size > 0
                and cursor + 5 + size <= len(payload),
                "Invalid TLS record framing.",
            )
            record_types.append(kind)
            cursor += 5 + size
        require(record_types, "Empty TLS record flight.")
        if not any(flight["role"] == role for flight in flights):
            require(
                record_types[0] == 22 and payload[5] == (1 if role == "peer" else 2),
                "TLS flight does not begin with the role's Hello.",
            )
        flights.append(
            {
                "role": role,
                "length": len(payload),
                "recordTypes": record_types,
                "sha256": hashlib.sha256(payload).hexdigest(),
            }
        )
    require(not pending and starts == 1, "Incomplete TLS fragment flight.")
    require(
        {flight["role"] for flight in flights} == {"peer", "authenticator"},
        "Missing TLS peer or server flight.",
    )
    return flights


def check_phase(directory, phase, fingerprints):
    name, success = phase["name"], phase["name"] == "success"
    source = f"{name}-frames.jsonl"
    raw_rows = read_lines(directory / source, phase)
    frames = [
        dict(decode_frame(row), source=f"{source}:{index}") for index, row in enumerate(raw_rows, 1)
    ]
    auth_source, peer_source = f"{name}-authenticator.jsonl", f"{name}-supplicant.jsonl"
    auth, peer = (
        read_lines(directory / auth_source, phase),
        read_lines(directory / peer_source, phase),
    )
    require(
        all(isinstance(row.get("line"), str) for row in auth + peer), "Invalid producer log line."
    )
    auth_versions = native_markers(
        auth, "SSL: Using TLS version ", "SSL: Using TLS version TLSv1.3", auth_source
    )
    peer_versions = native_markers(
        peer, "SSL: Using TLS version ", "SSL: Using TLS version TLSv1.3", peer_source
    )
    native_payloads = []
    for row in peer:
        match = HEXDUMP.fullmatch(row["line"])
        if match:
            payload = bytes.fromhex(match[3])
            require(len(payload) == int(match[2]), "Native hexdump length disagreement.")
            native_payloads.append(("authenticator" if match[1] == "RX" else "peer", payload))
    wire_payloads = [(frame["role"], bytes.fromhex(frame["raw"])[14:]) for frame in frames]
    require(
        wire_payloads == native_payloads,
        "Raw frame payloads or event sequence contradict the native EAPOL hexdumps.",
    )
    terminal, logoff = check_sequence(frames, success)
    flights = check_tls_fragments(frames)
    method_sources = [
        one_line(auth, "CTRL-EVENT-EAP-PROPOSED-METHOD vendor=0 method=13", auth_source),
        one_line(peer, "CTRL-EVENT-EAP-METHOD EAP vendor 0 method 13 (TLS) selected", peer_source),
    ]
    server_certificate = one_line(
        peer, f"depth=0 subject='/CN={SERVER}' hash={fingerprints['server']}", peer_source
    )
    if success:
        server_success = native_markers(
            auth,
            "EAP-TLS: Send protected success indication",
            "EAP-TLS: Send protected success indication (appl data 0x00)",
            auth_source,
            unique=True,
        )[0]
        peer_success = native_markers(
            peer,
            "EAP-TLS: ACKing protected success indication",
            "EAP-TLS: ACKing protected success indication (appl data 0x00)",
            peer_source,
            unique=True,
        )[0]
        method_sources += [
            one_line(
                auth,
                f"preverify_ok=1 err=0 (ok) ca_cert_verify=1 depth=0 buf='/CN={SUBJECT}'",
                auth_source,
            ),
            one_line(auth, "EAP-TLS: CONTINUE -> SUCCESS", auth_source),
            one_line(auth, "EAP-TLS: Client acknowledged final TLS handshake message", auth_source),
            peer_success,
            one_line(auth, f"CTRL-EVENT-EAP-SUCCESS {PEER}", auth_source),
            one_line(
                peer,
                "CTRL-EVENT-EAP-SUCCESS EAP authentication completed successfully",
                peer_source,
            ),
        ]
        ocsp = one_line(peer, "OpenSSL: OCSP response verification succeeded", peer_source)
        one_line(peer, "OpenSSL: OCSP status for server certificate: good", peer_source)
        connected = one_line(auth, f"AP-STA-CONNECTED {PEER}", auth_source)
        disconnected = one_line(auth, f"AP-STA-DISCONNECTED {PEER}", auth_source)
        line_order(
            method_sources[0],
            auth_versions[0],
            method_sources[2],
            auth_versions[-1],
            server_success,
            method_sources[3],
            method_sources[4],
            method_sources[6],
            connected,
            disconnected,
        )
        line_order(
            method_sources[1],
            peer_versions[0],
            server_certificate,
            ocsp,
            peer_versions[-1],
            method_sources[5],
            method_sources[7],
        )
        require(
            not any(
                "CTRL-EVENT-EAP-FAILURE" in row["line"] or "CERT-ERROR" in row["line"]
                for row in auth + peer
            ),
            "Success capture contains a native method failure.",
        )
    else:
        method_sources += [
            one_line(peer, "CTRL-EVENT-EAP-TLS-CERT-ERROR reason=10 depth=0", peer_source),
            one_line(peer, "TLS: Domain match 'wrong.campus.example.test' not found", peer_source),
            one_line(auth, f"CTRL-EVENT-EAP-FAILURE {PEER}", auth_source),
            one_line(peer, "CTRL-EVENT-EAP-FAILURE EAP authentication failed", peer_source),
        ]
        line_order(method_sources[0], *auth_versions, method_sources[4])
        line_order(
            method_sources[1],
            peer_versions[0],
            server_certificate,
            method_sources[2],
            method_sources[5],
        )
        line_order(method_sources[1], *peer_versions, method_sources[5])
        require(
            not any(
                "CTRL-EVENT-EAP-SUCCESS" in row["line"]
                or "AP-STA-CONNECTED" in row["line"]
                or "protected success indication" in row["line"]
                for row in auth + peer
            ),
            "Rejected certificate contradicts a native success.",
        )
    return {
        "phaseId": phase["phaseId"],
        "name": name,
        "window": {"startNs": phase["startNs"], "endNs": phase["endNs"]},
        "producerCommands": {
            "authenticator": phase["authenticatorCommand"],
            "supplicant": phase["supplicantCommand"],
        },
        "frames": frames,
        "tlsFlights": flights,
        "terminalIdentifier": frames[terminal]["eap"]["identifier"],
        "terminalFrame": terminal + 1,
        "logoffFrame": logoff + 1 if logoff is not None else None,
        "methodEvidence": {
            "accepted": success,
            "subject": SUBJECT,
            "method": METHOD,
            "phaseId": phase["phaseId"],
            "source": method_sources,
            "correlationAssumption": "same-isolated-producer-window-and-configured-certificate-policy",
        },
        "logicalAuthorization": {"beforeLogoff": True, "afterLogoff": False}
        if success
        else {"afterFailure": False},
    }


def check_capture(directory):
    directory = Path(directory)
    source_lines = (directory / "source-sha256.txt").read_text().splitlines()
    require(
        source_lines == [f"{digest}  /tmp/{name}" for name, digest in SOURCES.items()],
        "Pinned producer source hash disagreement.",
    )
    require(
        (directory / "hostapd-version.txt").read_text().startswith("hostapd v2.12\n")
        and (directory / "supplicant-version.txt").read_text().startswith("wpa_supplicant v2.12\n")
        and (directory / "openssl-version.txt").read_text().startswith("OpenSSL 3.5.9 "),
        "Native producer version disagreement.",
    )
    observations = read_json(directory / "observations.json")
    require(
        type(observations["schema"]) is int and observations["schema"] == 1,
        "Invalid evidence schema.",
    )
    require(
        observations["capture"] == "wired-eap-tls-private-veth"
        and observations["authenticator"] == AUTHENTICATOR
        and observations["peer"] == PEER
        and observations["subject"] == SUBJECT
        and observations["outerIdentity"] == OUTER
        and type(observations["method"]) is int
        and observations["method"] == METHOD,
        "Capture subject, method, or link role disagreement.",
    )
    configuration(directory)
    fingerprints = {
        "ca": certificate(directory, "ca", "Netlib private EAP test CA"),
        "server": certificate(directory, "server", SERVER, ("DNS", SERVER)),
        "client": certificate(directory, "client", SUBJECT, ("email", SUBJECT)),
    }
    phases = observations["phases"]
    require(
        len(phases) == 2
        and [(phase["name"], phase["phaseId"]) for phase in phases]
        == [("success", 1), ("bad-server", 2)],
        "Missing, duplicate, or misbound capture phase.",
    )
    previous_end = 0
    for phase in phases:
        require(
            type(phase["phaseId"]) is int
            and integer(phase["startNs"])
            and integer(phase["endNs"])
            and previous_end < phase["startNs"] < phase["endNs"],
            "Invalid or overlapping phase windows.",
        )
        previous_end = phase["endNs"]
        require(
            phase["authenticatorCommand"]
            == ["ip", "netns", "exec", "auth", "hostapd", "-dd", "/tmp/netlib-eap/hostapd.conf"],
            "Unexpected authenticator producer command.",
        )
        require(
            phase["supplicantCommand"]
            == [
                "ip",
                "netns",
                "exec",
                "peer",
                "wpa_supplicant",
                "-dd",
                "-D",
                "wired",
                "-i",
                "peer0",
                "-c",
                f"/tmp/netlib-eap/{phase['name']}-supplicant.conf",
            ],
            "Unexpected supplicant producer command.",
        )
    reports = [check_phase(directory, phase, fingerprints) for phase in phases]
    status = (directory / "supplicant-status.txt").read_text()
    require(
        all(
            text in status
            for text in (
                "suppPortStatus=Authorized\n",
                "EAP state=SUCCESS\n",
                "selectedMethod=13 (EAP-TLS)\n",
                "eap_tls_version=TLSv1.3\n",
                "tls_session_reused=0\n",
                f"address={PEER}\n",
            )
        ),
        "Supplicant TLS or logical authorization status disagreement.",
    )
    before, after = [
        (directory / filename).read_text()
        for filename in ("authorized-station.txt", "logged-off-station.txt")
    ]
    require(
        before.startswith(PEER + "\nflags=[AUTHORIZED]\n")
        and "dot1xAuthAuthControlledPortStatus=1\n" in before
        and "dot1xAuthEapolLogoffFramesRx=0\n" in before,
        "Missing native authorized port state.",
    )
    require(
        after.startswith(PEER + "\nflags=\n")
        and "dot1xAuthAuthControlledPortStatus=2\n" in after
        and "dot1xAuthEapolLogoffFramesRx=1\n" in after,
        "Missing native Logoff revocation state.",
    )
    return {
        "schema": 1,
        "scope": "checked-native-eap-evidence",
        "link": {"authenticator": AUTHENTICATOR, "peer": PEER},
        "subject": SUBJECT,
        "outerIdentity": OUTER,
        "method": METHOD,
        "phases": reports,
        "frameCount": sum(len(phase["frames"]) for phase in reports),
        "certificateSHA256": fingerprints,
        "limits": [
            "finite-capture",
            "trusted-native-TLS-method-and-certificate-policy",
            "collector-phase-is-not-wire-epoch",
            "current-round-and-link-attribution-assumption",
            "no-offline-TLS-signature-or-transcript-verification",
            "no-capture-authenticity-proof",
            "no-physical-data-port-enforcement-proof",
        ],
    }


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--capture-dir", type=Path, default=Path("examples/eap/native"))
    parser.add_argument("--output", type=Path)
    args = parser.parse_args(argv)
    try:
        report = check_capture(args.capture_dir)
        if args.output:
            args.output.write_text(json.dumps(report, indent=2) + "\n")
        print(f"Verified {report['frameCount']} EAPOL frames and two native TLS outcomes.")
    except (ValueError, OSError, KeyError, TypeError, OverflowError, IndexError) as error:
        print(f"EAP evidence: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
