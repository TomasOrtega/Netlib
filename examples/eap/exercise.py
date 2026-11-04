"""Capture a private wired EAP-TLS exchange and a rejected server identity."""

import json
import os
import shutil
import signal
import socket
import subprocess
import sys
import threading
import time
from pathlib import Path

OUTPUT = Path("/tmp/netlib-eap")
RUNTIME = Path("/run/netlib-eap")
COMMANDS = []


def run(*arguments, check=True):
    start = time.monotonic_ns()
    result = subprocess.run(arguments, capture_output=True, text=True, check=False)
    COMMANDS.append(
        {
            "command": list(arguments),
            "startNs": start,
            "endNs": time.monotonic_ns(),
            "returncode": result.returncode,
            "stdout": result.stdout,
            "stderr": result.stderr,
        }
    )
    if check and result.returncode:
        raise RuntimeError(f"Command failed: {arguments}: {result.stderr}")
    return result.stdout


class Producer:
    def __init__(self, phase, role, *arguments):
        self.rows = []
        self.path = OUTPUT / f"{phase}-{role}.jsonl"
        self.process = subprocess.Popen(arguments, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        self.thread = threading.Thread(target=self.read, daemon=True)
        self.thread.start()
        self.command = list(arguments)

    def read(self):
        with self.path.open("w") as stream:
            for raw in self.process.stdout:
                line = raw.decode(errors="strict").rstrip("\n")
                if line.startswith("EAP-TLS: Derived key - hexdump"):
                    line = "EAP-TLS: Derived key - hexdump(len=64): [COLLECTOR-REDACTED]"
                row = {"timeNs": time.monotonic_ns(), "line": line}
                self.rows.append(row)
                stream.write(json.dumps(row) + "\n")
                stream.flush()

    def wait_for(self, text, timeout=12):
        end = time.monotonic() + timeout
        while time.monotonic() < end:
            if any(text in row["line"] for row in self.rows):
                return
            if self.process.poll() is not None:
                break
            time.sleep(0.02)
        raise RuntimeError(f"Missing {text!r} in {self.path.name}")

    def stop(self):
        self.process.terminate()
        self.process.wait(timeout=5)
        self.thread.join(timeout=5)


def certificates():
    os.chdir(RUNTIME)
    Path("index.txt").touch()
    Path("serial").write_text("1000\n")
    Path("crlnumber").write_text("1000\n")
    Path("ca.conf").write_text(
        "[ca]\ndefault_ca=local\n[local]\ndatabase=index.txt\nserial=serial\n"
        "crlnumber=crlnumber\nnew_certs_dir=.\ncertificate=ca.pem\nprivate_key=ca.key\n"
        "default_md=sha256\ndefault_days=7\ndefault_crl_days=7\npolicy=names\n"
        "[names]\ncommonName=supplied\n"
    )
    run(
        "openssl",
        "req",
        "-new",
        "-x509",
        "-newkey",
        "ec",
        "-pkeyopt",
        "ec_paramgen_curve:P-256",
        "-noenc",
        "-keyout",
        "ca.key",
        "-out",
        "ca.pem",
        "-days",
        "7",
        "-subj",
        "/CN=Netlib private EAP test CA",
        "-addext",
        "basicConstraints=critical,CA:TRUE,pathlen:0",
        "-addext",
        "keyUsage=critical,keyCertSign,cRLSign",
    )
    for role, principal, alternate in (
        ("server", "radius.campus.example.test", "DNS:radius.campus.example.test"),
        ("client", "alice@campus.example.test", "email:alice@campus.example.test"),
    ):
        Path(f"{role}.ext").write_text(
            f"basicConstraints=critical,CA:FALSE\nkeyUsage=critical,digitalSignature\n"
            f"extendedKeyUsage={role}Auth\nsubjectAltName={alternate}\n"
        )
        run(
            "openssl",
            "req",
            "-new",
            "-newkey",
            "ec",
            "-pkeyopt",
            "ec_paramgen_curve:P-256",
            "-noenc",
            "-keyout",
            f"{role}.key",
            "-out",
            f"{role}.csr",
            "-subj",
            f"/CN={principal}",
        )
        run(
            "openssl",
            "ca",
            "-batch",
            "-config",
            "ca.conf",
            "-extfile",
            f"{role}.ext",
            "-in",
            f"{role}.csr",
            "-out",
            f"{role}.pem",
            "-notext",
        )
    run("openssl", "ca", "-config", "ca.conf", "-gencrl", "-out", "ca.crl.pem")
    Path("ca-chain.pem").write_bytes(Path("ca.pem").read_bytes() + Path("ca.crl.pem").read_bytes())
    run(
        "openssl",
        "ocsp",
        "-index",
        "index.txt",
        "-rsigner",
        "ca.pem",
        "-rkey",
        "ca.key",
        "-CA",
        "ca.pem",
        "-issuer",
        "ca.pem",
        "-cert",
        "server.pem",
        "-respout",
        "server.ocsp.der",
        "-ndays",
        "1",
    )
    for name in (
        "ca.pem",
        "ca.crl.pem",
        "ca-chain.pem",
        "server.pem",
        "client.pem",
        "server.ocsp.der",
    ):
        shutil.copyfile(name, OUTPUT / name)
    for role in ("ca", "server", "client"):
        (OUTPUT / f"{role}-certificate.txt").write_text(
            run(
                "openssl",
                "x509",
                "-in",
                f"{role}.pem",
                "-noout",
                "-subject",
                "-issuer",
                "-serial",
                "-fingerprint",
                "-sha256",
                "-dates",
            )
        )
    os.chdir(OUTPUT)


def configurations():
    (RUNTIME / "users").write_text("* TLS\n")
    (OUTPUT / "users").write_text("* TLS\n")
    hostapd = (
        "interface=auth0\ndriver=wired\nieee8021x=1\neapol_version=2\neap_server=1\n"
        "ctrl_interface=/run/netlib-eap/hostapd\neap_user_file=/run/netlib-eap/users\n"
        "ca_cert=/run/netlib-eap/ca-chain.pem\nserver_cert=/run/netlib-eap/server.pem\n"
        "private_key=/run/netlib-eap/server.key\ncheck_crl=2\ncheck_crl_strict=1\n"
        "check_cert_subject=CN=alice@campus.example.test\ntls_session_lifetime=0\n"
        "ocsp_stapling_response=/run/netlib-eap/server.ocsp.der\n"
        "tls_flags=[DISABLE-TLSv1.0][DISABLE-TLSv1.1][DISABLE-TLSv1.2][ENABLE-TLSv1.3]\n"
        "logger_stdout=-1\nlogger_stdout_level=0\n"
    )
    (OUTPUT / "hostapd.conf").write_text(hostapd)
    for phase, domain in (
        ("success", "radius.campus.example.test"),
        ("bad-server", "wrong.campus.example.test"),
    ):
        supplicant = (
            "ctrl_interface=/run/netlib-eap/supplicant\neapol_version=2\nap_scan=0\nnetwork={\n"
            ' key_mgmt=IEEE8021X\n eap=TLS\n identity="anonymous@campus.example.test"\n'
            ' ca_cert="/run/netlib-eap/ca.pem"\n client_cert="/run/netlib-eap/client.pem"\n'
            ' private_key="/run/netlib-eap/client.key"\n'
            f' domain_match="{domain}"\n'
            ' phase1="tls_disable_tlsv1_0=1 tls_disable_tlsv1_1=1 tls_disable_tlsv1_2=1 tls_disable_tlsv1_3=0"\n'
            " ocsp=2\n}\n"
        )
        (OUTPUT / f"{phase}-supplicant.conf").write_text(supplicant)


def sniff(path):
    active = True

    def stop(*_):
        nonlocal active
        active = False

    signal.signal(signal.SIGTERM, stop)
    sock = socket.socket(socket.AF_PACKET, socket.SOCK_RAW, socket.htons(3))
    sock.bind(("auth0", 0))
    sock.settimeout(0.1)
    with Path(path).open("w") as stream:
        while active:
            try:
                frame, address = sock.recvfrom(65535)
            except TimeoutError:
                continue
            if frame[12:14] != bytes.fromhex("888e"):
                continue
            stream.write(
                json.dumps(
                    {"timeNs": time.monotonic_ns(), "packetType": address[2], "hex": frame.hex()}
                )
                + "\n"
            )
            stream.flush()


def phase(name, round_number):
    start = time.monotonic_ns()
    capture = subprocess.Popen(
        [
            "ip",
            "netns",
            "exec",
            "auth",
            "python3",
            "/task/exercise.py",
            "sniff",
            str(OUTPUT / f"{name}-frames.jsonl"),
        ]
    )
    time.sleep(0.15)
    auth = Producer(
        name,
        "authenticator",
        "ip",
        "netns",
        "exec",
        "auth",
        "hostapd",
        "-dd",
        str(OUTPUT / "hostapd.conf"),
    )
    auth.wait_for("AP-ENABLED")
    peer = Producer(
        name,
        "supplicant",
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
        str(OUTPUT / f"{name}-supplicant.conf"),
    )
    try:
        peer.wait_for("CTRL-EVENT-EAP-SUCCESS" if name == "success" else "CTRL-EVENT-EAP-FAILURE")
        if name == "success":
            auth.wait_for("AP-STA-CONNECTED")
            (OUTPUT / "authorized-station.txt").write_text(
                run(
                    "ip",
                    "netns",
                    "exec",
                    "auth",
                    "hostapd_cli",
                    "-p",
                    "/run/netlib-eap/hostapd",
                    "-i",
                    "auth0",
                    "sta",
                    "02:00:00:00:ea:02",
                )
            )
            (OUTPUT / "supplicant-status.txt").write_text(
                run(
                    "ip",
                    "netns",
                    "exec",
                    "peer",
                    "wpa_cli",
                    "-p",
                    "/run/netlib-eap/supplicant",
                    "-i",
                    "peer0",
                    "status",
                )
            )
            run(
                "ip",
                "netns",
                "exec",
                "peer",
                "wpa_cli",
                "-p",
                "/run/netlib-eap/supplicant",
                "-i",
                "peer0",
                "logoff",
            )
            auth.wait_for("AP-STA-DISCONNECTED")
            (OUTPUT / "logged-off-station.txt").write_text(
                run(
                    "ip",
                    "netns",
                    "exec",
                    "auth",
                    "hostapd_cli",
                    "-p",
                    "/run/netlib-eap/hostapd",
                    "-i",
                    "auth0",
                    "sta",
                    "02:00:00:00:ea:02",
                )
            )
        time.sleep(0.2)
    finally:
        peer.stop()
        auth.stop()
        capture.terminate()
        capture.wait(timeout=5)
    return {
        "name": name,
        "phaseId": round_number,
        "startNs": start,
        "endNs": time.monotonic_ns(),
        "authenticatorCommand": auth.command,
        "supplicantCommand": peer.command,
    }


def capture():
    OUTPUT.mkdir(exist_ok=True)
    RUNTIME.mkdir(exist_ok=True)
    certificates()
    configurations()
    for namespace in ("auth", "peer"):
        run("ip", "netns", "add", namespace)
        run("ip", "-n", namespace, "link", "set", "lo", "up")
    run(
        "ip",
        "link",
        "add",
        "auth0",
        "address",
        "02:00:00:00:ea:01",
        "type",
        "veth",
        "peer",
        "name",
        "peer0",
        "address",
        "02:00:00:00:ea:02",
    )
    for namespace, interface in (("auth", "auth0"), ("peer", "peer0")):
        run("ip", "link", "set", interface, "netns", namespace)
        run("ip", "-n", namespace, "link", "set", interface, "up")
        (OUTPUT / f"{namespace}-links.json").write_text(
            run("ip", "-n", namespace, "-j", "link", "show")
        )
    try:
        rounds = [phase("success", 1), phase("bad-server", 2)]
        (OUTPUT / "observations.json").write_text(
            json.dumps(
                {
                    "schema": 1,
                    "capture": "wired-eap-tls-private-veth",
                    "authenticator": "02:00:00:00:ea:01",
                    "peer": "02:00:00:00:ea:02",
                    "outerIdentity": "anonymous@campus.example.test",
                    "subject": "alice@campus.example.test",
                    "method": 13,
                    "phases": rounds,
                },
                indent=2,
            )
            + "\n"
        )
    finally:
        (OUTPUT / "commands.json").write_text(json.dumps(COMMANDS, indent=2) + "\n")
        shutil.rmtree(RUNTIME)


if __name__ == "__main__":
    if sys.argv[1] == "sniff":
        sniff(sys.argv[2])
    else:
        capture()
