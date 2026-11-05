set -eu
mkdir -p /tmp/netlib-drain
cd /tmp/netlib-drain
uname -r > kernel.txt
conntrack -V > conntrack-version.txt
nft --version > nftables-version.txt
ip -Version > iproute2-version.txt
tc -Version > tc-version.txt
pkg-config --modversion libnetfilter_conntrack > library-version.txt
apk --no-network info -vv > packages.txt
mkdir -p /tmp/netlib-proc
mount -t proc proc /tmp/netlib-proc
for namespace in client router server; do
  ip netns add "$namespace"
  ip netns exec "$namespace" sh -c 'echo 0 > /tmp/netlib-proc/sys/net/ipv4/ip_forward'
  ip netns exec "$namespace" sh -c 'echo 1 > /tmp/netlib-proc/sys/net/ipv6/conf/all/disable_ipv6; echo 1 > /tmp/netlib-proc/sys/net/ipv6/conf/default/disable_ipv6'
  ip -n "$namespace" link set lo up
done
ip link add client0 address 02:00:00:00:01:02 type veth peer name inside0 address 02:00:00:00:01:01
ip link set client0 netns client
ip link set inside0 netns router
ip link add outside0 address 02:00:00:00:02:01 type veth peer name server0 address 02:00:00:00:02:02
ip link set outside0 netns router
ip link set server0 netns server
ip -n client addr add 192.0.2.2/24 dev client0
ip -n router addr add 192.0.2.1/24 dev inside0
ip -n router addr add 198.51.100.1/24 dev outside0
ip -n router addr add 203.0.113.1/32 dev outside0
ip -n router addr add 203.0.113.2/32 dev outside0
ip -n server addr add 198.51.100.2/24 dev server0
ip -n client link set client0 up
ip -n router link set inside0 up
ip -n router link set outside0 up
ip -n server link set server0 up
ip -n client route add default via 192.0.2.1
ip -n server route add 192.0.2.0/24 via 198.51.100.1
ip -n server route add 203.0.113.0/24 via 198.51.100.1
ip -n client neigh add 192.0.2.1 lladdr 02:00:00:00:01:01 nud permanent dev client0
ip -n router neigh add 192.0.2.2 lladdr 02:00:00:00:01:02 nud permanent dev inside0
ip -n router neigh add 198.51.100.2 lladdr 02:00:00:00:02:02 nud permanent dev outside0
ip -n server neigh add 198.51.100.1 lladdr 02:00:00:00:02:01 nud permanent dev server0
ip netns exec router sh -c 'echo 1 > /tmp/netlib-proc/sys/net/ipv4/ip_forward'
ip netns exec router ip -j -4 route show table main > routes.json
ip netns exec router ip -j neigh show > neighbors.json
ip netns exec router ip -j link show > links.json
for namespace in client router server; do
  ip netns exec "$namespace" sysctl net.ipv4.ip_forward net.ipv6.conf.all.disable_ipv6 net.ipv6.conf.default.disable_ipv6 > "$namespace-settings.txt"
done
python3 /task/examples/drain/exercise.py capture
tar -cf - *.json *.nft *.txt
