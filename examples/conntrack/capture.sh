set -eu
mkdir -p /tmp/netlib-native
cd /tmp/netlib-native
trap 'touch /tmp/netlib-native/finish' EXIT
uname -r > kernel.txt
conntrack -V > conntrack-version.txt
nft --version > nftables-version.txt
pkg-config --modversion libnetfilter_conntrack > library-version.txt
apk info -vv > packages.txt
for namespace in client router server; do
  ip netns add "$namespace"
  ip -n "$namespace" link set lo up
done
ip link add client0 type veth peer name inside0
ip link set client0 netns client
ip link set inside0 netns router
ip link add outside0 type veth peer name server0
ip link set outside0 netns router
ip link set server0 netns server
ip -n client addr add 192.0.2.2/24 dev client0
ip -n router addr add 192.0.2.1/24 dev inside0
ip -n router addr add 198.51.100.1/24 dev outside0
ip -n router addr add 203.0.113.1/32 dev outside0
ip -n server addr add 198.51.100.2/24 dev server0
ip -n server addr add 198.51.100.3/24 dev server0
ip -n client link set client0 up
ip -n router link set inside0 up
ip -n router link set outside0 up
ip -n server link set server0 up
ip -n client route add default via 192.0.2.1
ip -n server route add 192.0.2.0/24 via 198.51.100.1
ip -n server route add 203.0.113.0/24 via 198.51.100.1
# The default container /proc/sys mount is read-only.
mkdir -p /tmp/netlib-proc
mount -t proc proc /tmp/netlib-proc
ip netns exec router sh -c 'echo 1 > /tmp/netlib-proc/sys/net/ipv4/ip_forward'
cat > rules.nft <<'RULES'
table ip netlib_capture {
  chain forward {
    type filter hook forward priority 0; policy drop;
    ct state established accept
    ip saddr 192.0.2.0/24 meta l4proto { tcp, udp } th dport { 9000, 9001 } accept
  }
  chain source_nat {
    type nat hook postrouting priority 100; policy accept;
    ip saddr 192.0.2.0/24 meta l4proto { tcp, udp } snat to 203.0.113.1:40000
  }
  chain late_drop {
    type filter hook postrouting priority 200; policy accept;
    udp dport 9001 drop
  }
}
RULES
ip netns exec router nft -f rules.nft
ip netns exec router nft -j -nn list ruleset > rules.json
ip netns exec server python3 /task/examples/conntrack/exercise.py server &
server_pid=$!
for attempt in $(seq 1 100); do
  test -e server-ready && break
  sleep 0.05
done
test -e server-ready
ip netns exec client python3 /task/examples/conntrack/exercise.py client &
client_pid=$!
for attempt in $(seq 1 200); do
  test -e client-ready && break
  sleep 0.05
done
test -e client-ready
ip netns exec router conntrack -L -f ipv4 -o xml > conntrack.xml
ip netns exec router python3 /task/scripts/capture_conntrack.py --output netlink.json
touch finish
wait "$client_pid"
wait "$server_pid"
tar -cf - kernel.txt conntrack-version.txt nftables-version.txt library-version.txt \
  packages.txt rules.nft rules.json conntrack.xml netlink.json client.json server.json
