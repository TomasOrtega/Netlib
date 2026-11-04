set -eu
apk add --no-cache build-base bison flex pkgconf libmnl-dev libnftnl-dev jansson-dev readline-dev libedit-dev gmp-dev >&2
wget -q https://netfilter.org/projects/nftables/files/nftables-1.1.3.tar.xz -O /tmp/nftables.tar.xz
printf '%s  %s\n' 9c8a64b59c90b0825e540a9b8fcb9d2d942c636f81ba50199f068fde44f34ed8 /tmp/nftables.tar.xz | sha256sum -c - >&2
tar -xJf /tmp/nftables.tar.xz -C /tmp
cd /tmp/nftables-1.1.3
./configure --disable-man-doc --disable-python --with-json >/tmp/configure.log 2>&1 || { cat /tmp/configure.log >&2; exit 1; }
make -j2 >/tmp/build.log 2>&1 || { cat /tmp/build.log >&2; exit 1; }
./src/nft --version >/tmp/nft-version.txt
./src/nft -f - <<'RULES'
table ip netlib_capture {
  chain forward {
    type filter hook forward priority 0; policy drop;
    ip saddr 192.0.2.0/24 ip daddr 198.51.100.0/24 tcp dport 443 accept
  }
}
RULES
./src/nft -j -nn list ruleset >/tmp/nftables.json
cat >/tmp/generated.json <<'NETLIB_COMPILER_JSON'
{"nftables":
 [{"metainfo":
   {"version": "1.1.3",
    "release_name": "Netlib compiler",
    "json_schema_version": 1}},
  {"table": {"name": "netlib", "handle": 1, "family": "ip"}},
  {"chain":
   {"type": "filter",
    "table": "netlib",
    "prio": 0,
    "policy": "drop",
    "name": "forward",
    "hook": "forward",
    "handle": 2,
    "family": "ip"}},
  {"rule":
   {"table": "netlib",
    "handle": 3,
    "family": "ip",
    "expr":
    [{"match":
      {"right": {"prefix": {"len": 24, "addr": "10.0.0.0"}},
       "op": "==",
       "left": {"payload": {"protocol": "ip", "field": "saddr"}}}},
     {"match": {"right": 6, "op": "==", "left": {"meta": {"key": "l4proto"}}}},
     {"match":
      {"right": {"range": [443, 444]},
       "op": "==",
       "left": {"payload": {"protocol": "tcp", "field": "dport"}}}},
     {"accept": null}],
    "comment": "WEB",
    "chain": "forward"}},
  {"rule":
   {"table": "netlib",
    "handle": 4,
    "family": "ip",
    "expr":
    [{"match": {"right": 17, "op": "==", "left": {"meta": {"key": "l4proto"}}}},
     {"match":
      {"right": 53,
       "op": "==",
       "left": {"payload": {"protocol": "udp", "field": "dport"}}}},
     {"accept": null}],
    "comment": "DNS",
    "chain": "forward"}},
  {"rule":
   {"table": "netlib",
    "handle": 5,
    "family": "ip",
    "expr":
    [{"match": {"right": 1, "op": "==", "left": {"meta": {"key": "l4proto"}}}},
     {"accept": null}],
    "comment": "ICMP",
    "chain": "forward"}}]}
NETLIB_COMPILER_JSON
./src/nft -c -j -f /tmp/generated.json
./src/nft -j -f /tmp/generated.json
./src/nft -j -nn list table ip netlib >/tmp/loaded.json
grep -n 'NFTNL_UDATA_COMMENT_MAXLEN' /usr/include/libnftnl/udata.h >/tmp/comment-header.txt
grep -n -B3 -A3 'comment too long' src/parser_json.c >/tmp/comment-check.txt || true
tar -cf - -C /tmp nftables.json nft-version.txt loaded.json comment-header.txt comment-check.txt
