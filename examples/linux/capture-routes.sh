set -eu
apk add --no-cache build-base linux-headers bison flex pkgconf libmnl-dev libcap-dev elfutils-dev nftables >&2
wget -q https://www.kernel.org/pub/linux/utils/net/iproute2/iproute2-6.19.0.tar.gz -O /tmp/iproute2.tar.gz
printf '%s  %s\n' b39ac6a76f8299968408d3f2948ea59d9502b299d3e0c78c93658b65df3be5be /tmp/iproute2.tar.gz | sha256sum -c - >&2
tar -xzf /tmp/iproute2.tar.gz -C /tmp
cd /tmp/iproute2-6.19.0
make -j2 SUBDIRS='lib ip' >/tmp/build.log 2>&1 || { cat /tmp/build.log >&2; exit 1; }
./ip/ip -Version >/tmp/ip-version.txt
nft --version >/tmp/nft-version.txt
./ip/ip route add 198.51.100.0/24 dev eth0 metric 500
./ip/ip route add blackhole 198.51.100.128/25 metric 9999
./ip/ip route add unreachable 203.0.113.7
./ip/ip route add prohibit 203.0.113.8
./ip/ip -j -4 route show table main >/tmp/routes.json
nft -f - <<'RULES'
table ip netlib_capture {
  chain forward {
    type filter hook forward priority 0; policy drop;
    ip saddr 192.0.2.0/24 ip daddr 198.51.100.0/24 tcp dport 443 accept
  }
}
RULES
nft -j -nn list ruleset >/tmp/nftables.json
tar -cf - -C /tmp routes.json nftables.json ip-version.txt nft-version.txt
