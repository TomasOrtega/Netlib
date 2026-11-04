set -eu
mkdir -p /tmp/netlib-lifecycle
cd /tmp/netlib-lifecycle
uname -r > kernel.txt
conntrack -V > conntrack-version.txt
nft --version > nftables-version.txt
ip -Version > iproute2-version.txt
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
ip -n router addr add 203.0.113.2/32 dev outside0
ip -n server addr add 198.51.100.2/24 dev server0
ip -n client link set client0 up
ip -n router link set inside0 up
ip -n router link set outside0 up
ip -n server link set server0 up
ip -n client route add default via 192.0.2.1
ip -n server route add 192.0.2.0/24 via 198.51.100.1
ip -n server route add 203.0.113.0/24 via 198.51.100.1
mkdir -p /tmp/netlib-proc
mount -t proc proc /tmp/netlib-proc
ip netns exec router sh -c 'echo 1 > /tmp/netlib-proc/sys/net/ipv4/ip_forward'
ip netns exec router ip -j -4 route show table main > routes.json
python3 /task/examples/lifecycle/exercise.py capture
tar -cf - *.json *.nft *.txt
