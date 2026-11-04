# EAP authentication evidence

This note supports the private [wired EAP-TLS capture](../../examples/eap/README.md).
It uses RFC 3748, RFC 9190, and the official hostapd 2.12 source release.

## Wire rules

EAP has a one-byte code, one-byte identifier, and two-byte network-order length.
The length includes its header.
Request and Response also contain a type byte.
Bytes beyond that length are padding and are ignored.
A length beyond the received bytes causes rejection.
Success and Failure have length four and contain no method data.
[RFC 3748, sections 4–4.2](https://www.rfc-editor.org/rfc/rfc3748.html#section-4).

A Response identifier matches the outstanding Request.
A retransmitted Request keeps its identifier.
A new Request changes the previous identifier; identifiers can repeat later.
A terminal identifier matches the Response it answers.
EAP depends on lower-layer ordering and duplicate handling.
Its identifier has only eight bits and is no global replay token.
[RFC 3748, sections 3.1, 4.1, and 4.2](https://www.rfc-editor.org/rfc/rfc3748.html#section-4.1).

An unsolicited Success does not establish authentication.
The peer discards a terminal packet before the method permits completion.
The finite admission model therefore requires separate method evidence.
[RFC 3748, section 4.2](https://www.rfc-editor.org/rfc/rfc3748.html#section-4.2).

## TLS and identity

For TLS 1.3, the server sends a protected success indication as TLS application data `0x00`.
The peer then sends an empty EAP-TLS Response.
The server sends EAP-Success after that Response.
The terminal identifier therefore matches this final method Response, including when earlier TLS messages required fragmentation.
[RFC 9190, section 2.1.1](https://www.rfc-editor.org/rfc/rfc9190.html#section-2.1.1).

An EAP-TLS fragment with the More flag requires an empty opposite-role EAP-TLS acknowledgment before its next fragment.
The initial fragment carries the total TLS message length.
The verifier checks that total, acknowledgment ordering, and reconstructed TLS record lengths.
[RFC 5216, section 2.1.5](https://www.rfc-editor.org/rfc/rfc5216.html#section-2.1.5).
[RFC 9190, section 2.1.9](https://www.rfc-editor.org/rfc/rfc9190.html#section-2.1.9).

The outer EAP Identity is not authenticated by EAP-TLS.
An attacker can forge or replay it.
Authorization must use authenticated information such as the client certificate.
TLS 1.3 peers use a privacy-friendly outer identity.
The capture uses `anonymous@campus.example.test` outside and `alice@campus.example.test` in the checked client certificate.
[RFC 9190, sections 2.1.8, 2.2, and 5.6](https://www.rfc-editor.org/rfc/rfc9190.html#section-5.6).

Certificate validation and revocation checks remain part of the method implementation's obligations.
The recipe supplies a private CA, a current CRL, and an OCSP response.
It requires the server name and the client subject, disables older TLS versions, and disables session resumption.
This is a private test policy, with no claim of a CNSA-approved cipher suite.
[RFC 9190, sections 5.3–5.4](https://www.rfc-editor.org/rfc/rfc9190.html#section-5.3).

## EAPOL and the native boundary

IEEE 802.1X defines port access control and EAPOL encapsulation.
The IEEE working-group material identifies EtherType `0x888e` and a two-byte EAPOL body length.
It also identifies extensions in newer EAPOL versions.
This example selects version 2 with an empty Start or Logoff body.
It does not model all version 3 TLVs or MACsec.
[IEEE 802.1X project](https://www.ieee802.org/1/pages/802.1x.html).
[IEEE working-group EAPOL presentation, pages 6–8](https://grouper.ieee.org/groups/1904/4/meeting_archive/2023/04/tf4_2304_goeringer_1_EAPOLMessages.pdf).

The source's `src/common/eapol_common.h` defines the four-byte EAPOL header and packet types 0, 1, and 2.
Its `src/drivers/driver_wired.c` exchanges EAPOL through raw Ethernet sockets.
The wired driver's operations contain no station-authorization callback.
Inference: this capture can observe hostapd's logical authorization state without establishing a physical data-port barrier.
[Official hostapd 2.12 source archive](https://w1.fi/releases/hostapd-2.12.tar.gz).

The retained raw frames and producer logs provide separate observations.
The offline verifier joins their link roles, method, certificate identity, and isolated capture window.
Log timestamps record when the wrapper reads each line; they do not measure the internal TLS decision instant.
Method evidence can therefore be inserted before or after the terminal event within the same local round.
[Capture producer](../../examples/eap/exercise.py).
[Offline verifier](../../scripts/check_eap_capture.py).

The local round is a collector label, not an EAP wire field.
Restart, Start, Logoff, or disconnect invalidates admission under the model's explicit policy.
Authentic delivery to the intended link and correct current-round attribution remain assumptions.
Raw MAC addresses and eight-bit identifiers do not provide those guarantees.
The verifier does not reimplement TLS, validate signatures, prove capture authenticity, or establish universal replay protection.
Finite agreement also gives no liveness, implementation refinement, or physical port-enforcement theorem.
