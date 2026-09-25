#!/usr/bin/env python3
"""Offline validation of real absence-oracle evidence.

Validates, with no network access, that real deployed infrastructure produces
the two kinds of signed evidence the paper's absence oracle relies on:

  1. DNSSEC: a captured denial-of-existence for `thisnamedoesnotexist-zz99
     .ietf.org.` --- an NSEC record plus its ECDSA-P256 RRSIG --- verified
     against the zone's captured DNSKEY, whose own DNSKEY-set RRSIG is verified
     against the zone KSK.  Canonicalization per RFC 4034.

  2. CT: a live Cloudflare Nimbus2026 signed tree head (STH) verified against
     the log's published public key, per RFC 6962.

Run:  python3 scripts/validate_real_oracle.py
Deps: python3 stdlib + openssl(1) on PATH.  Fixtures live in tests/fixtures/.
"""

import base64
import json
import struct
import subprocess
import sys
import tempfile
from pathlib import Path

FIXTURES = Path(__file__).resolve().parent.parent / "tests" / "fixtures"

TYPE = {"nsec": 47, "dnskey": 48, "soa": 6}


def canon_name(name: str) -> bytes:
    """RFC 4034 canonical wire form of a lower-cased, uncompressed name.

    `\\000`-style escapes denote a literal label byte, as produced by dig/DoH.
    """
    out = bytearray()
    name = name.rstrip(".")
    if not name:
        return b"\x00"
    i = 0
    for label in name.split("."):
        if label.startswith("\\"):
            # a \\DDD label: the single byte value
            data = bytes([int(label[1:])])
        else:
            data = label.lower().encode()
        out += bytes([len(data)]) + data
        i += 1
    return bytes(out) + b"\x00"


def key_tag(rdata: bytes) -> int:
    """RFC 4034 App. B key tag of a DNSKEY's RDATA."""
    ac = 0
    for i, b in enumerate(rdata):
        ac += b << 8 if i % 2 == 0 else b
    return (ac + (ac >> 16 & 0xFFFF)) & 0xFFFF


def rrsig_rdata_prefix(rrsig: dict) -> bytes:
    """RRSIG RDATA excluding the signature field (the signed prefix)."""
    d = rrsig["data"].split()
    covered, alg, labels, ttl, exp, inc, tag, signer = (
        TYPE[d[0]], int(d[1]), int(d[2]), int(d[3]),
        int(d[4]), int(d[5]), int(d[6]), d[7],
    )
    sig = base64.b64decode(d[8])
    prefix = (struct.pack(">HBBIIIH", covered, alg, labels, ttl, exp, inc, tag)
              + canon_name(signer))
    return prefix, sig, tag


def type_bitmap(types) -> bytes:
    """RFC 4034 NSEC type bitmap."""
    windows = {}
    for t in types:
        w, bit = t >> 8, t & 255
        octet, mask = bit >> 3, 1 << (7 - (bit & 7))
        bits = windows.setdefault(w, {})
        bits[octet] = bits.get(octet, 0) | mask
    out = bytearray()
    for w, bits in sorted(windows.items()):
        ln = max(bits) + 1
        bm = bytearray(ln)
        for o, m in bits.items():
            bm[o] |= m
        out += bytes([w, ln]) + bm
    return bytes(out)


def verify_ecdsa_p256(pubkey_b64: str, sig_raw: bytes, data: bytes, tag: str) -> bool:
    """Verify an alg-13 (ECDSA P-256/SHA-256) DNSSEC signature via openssl."""
    pub = base64.b64decode(pubkey_b64)                    # X || Y, 64 bytes
    # SPKI DER for prime256v1: fixed prefix || 04 || X || Y
    spki = bytes.fromhex(
        "3059301306072a8648ce3d020106082a8648ce3d03010703420004") + pub
    r, s = int.from_bytes(sig_raw[:32], "big"), int.from_bytes(sig_raw[32:], "big")

    def der_int(x):
        b = x.to_bytes((x.bit_length() + 7) // 8 or 1, "big")
        return b"\x02" + bytes([len(b) + (1 if b[0] & 0x80 else 0)]) + \
               (b"\x00" + b if b[0] & 0x80 else b)

    der = b"\x30" + bytes([len(der_int(r)) + len(der_int(s))]) + der_int(r) + der_int(s)
    with tempfile.TemporaryDirectory() as td:
        td = Path(td)
        (td / "key.der").write_bytes(spki)
        (td / "sig.der").write_bytes(der)
        (td / "data.bin").write_bytes(data)
        subprocess.run(["openssl", "pkey", "-pubin", "-inform", "DER",
                        "-in", str(td / "key.der"), "-out", str(td / "key.pem")],
                       check=True, capture_output=True)
        res = subprocess.run(["openssl", "dgst", "-sha256", "-verify",
                              str(td / "key.pem"), "-signature",
                              str(td / "sig.der"), str(td / "data.bin")],
                             capture_output=True, text=True)
    ok = "Verified OK" in res.stdout
    print(f"    [{tag}] ECDSA-P256/SHA-256 RRSIG: {res.stdout.strip()}")
    return ok


def main() -> int:
    ok = True

    print("== DNSSEC denial-of-existence (ietf.org) ==")
    dnskey = json.load(open(FIXTURES / "dnskey.json"))
    nxd = json.load(open(FIXTURES / "nxdomain.json"))
    assert nxd["AD"], "resolver did not mark the denial as authenticated"

    keys = {}   # key_tag -> raw pubkey
    dnskey_rds = []
    ksk_rdata = None
    for r in dnskey["Answer"]:
        if r["type"] == 48:
            fl, pr, al, pk = r["data"].split(None, 3)
            rdata = struct.pack(">HBB", int(fl), int(pr), int(al)) + \
                base64.b64decode(pk)
            dnskey_rds.append((rdata, pk))
            keys[key_tag(rdata)] = pk
            if int(fl) == 257:
                ksk_rdata = (rdata, pk)

    zsk = keys.get(34505)
    assert zsk, "no captured DNSKEY with key tag 34505"
    print(f"    key tags: {sorted(keys)}; ZSK tag 34505 found")

    # 1. Verify the NSEC's RRSIG (the denial evidence) under the zone ZSK.
    nsec_rr = next(r for r in nxd["Authority"] if r["type"] == 47)
    rrsig_rr = next(r for r in nxd["Authority"]
                    if r["type"] == 46 and r["data"].startswith("nsec "))
    prefix, sig, tag = rrsig_rdata_prefix(rrsig_rr)

    # canonical RR: owner || type || class || origTTL || rdlen || RDATA
    nsec_rdata = canon_name(nsec_rr["data"].split(None, 1)[0]) + \
        type_bitmap([46, 47, 128])
    rr = (canon_name(nsec_rr["name"]) + struct.pack(">HHIH", 47, 1, 1800,
          len(nsec_rdata)) + nsec_rdata)
    ok &= verify_ecdsa_p256(zsk, sig, prefix + rr, "NSEC denial")

    # 2. Verify the DNSKEY-set RRSIG under the zone KSK (chain link).
    dk_sig = next(r for r in dnskey["Answer"]
                  if r["type"] == 46 and r["data"].startswith("dnskey "))
    prefix, sig, tag = rrsig_rdata_prefix(dk_sig)
    rrset = b""
    for rdata, _ in sorted(dnskey_rds):       # RRset sorted by canonical RDATA
        rrset += (canon_name("ietf.org.") + struct.pack(">HHIH", 48, 1, 3600,
                  len(rdata)) + rdata)
    ok &= verify_ecdsa_p256(ksk_rdata[1], sig, prefix + rrset,
                            "DNSKEY set (KSK chain link)")

    print("== CT signed tree head (Cloudflare Nimbus2026) ==")
    sth = json.load(open(FIXTURES / "ct_sth_nimbus2026.json"))
    root = base64.b64decode(sth["sha256_root_hash"])
    dsig = base64.b64decode(sth["tree_head_signature"])
    assert dsig[0] == 4 and dsig[1] == 3, "expected SHA-256/ECDSA"
    der_sig = dsig[4:4 + int.from_bytes(dsig[2:4], "big")]
    data = (bytes([0x00, 0x01]) + struct.pack(">Q", sth["timestamp"])
            + struct.pack(">Q", sth["tree_size"]) + root)
    key_der = base64.b64decode(
        (FIXTURES / "ct_log_key_nimbus2026.b64").read_text().strip())
    with tempfile.TemporaryDirectory() as td:
        td = Path(td)
        (td / "key.der").write_bytes(key_der)
        (td / "sig.der").write_bytes(der_sig)
        (td / "data.bin").write_bytes(data)
        subprocess.run(["openssl", "pkey", "-pubin", "-inform", "DER",
                        "-in", str(td / "key.der"), "-out", str(td / "key.pem")],
                       check=True, capture_output=True)
        res = subprocess.run(["openssl", "dgst", "-sha256", "-verify",
                              str(td / "key.pem"), "-signature",
                              str(td / "sig.der"), str(td / "data.bin")],
                             capture_output=True, text=True)
    print(f"    [STH] tree_size={sth['tree_size']} "
          f"ts={sth['timestamp']}: {res.stdout.strip()}")
    ok &= "Verified OK" in res.stdout

    print("RESULT:", "all real-oracle evidence verified" if ok else "FAILED")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
