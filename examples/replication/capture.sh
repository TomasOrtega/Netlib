set -eu
mkdir -p /tmp/netlib-replication /tmp/netlib-proc /run/netlib-failover
mount -t proc proc /tmp/netlib-proc
cd /tmp/netlib-replication
uname -a > kernel.txt
conntrack -V > conntrack-version.txt
conntrackd -v > conntrackd-version.txt
nft --version > nftables-version.txt
ip -Version > iproute2-version.txt
apk --no-network info -vv > packages.txt
sha256sum /opt/netlib/sbin/conntrackd /opt/netlib/sbin/conntrack /opt/netlib/sbin/nft /opt/netlib/sbin/ip /tmp/tools.tar.xz /tmp/library.tar.xz > producer-sha256.txt
sha256sum /task/replication/exercise.py /task/replication/nflog.py /task/wire/exercise.py /task/capture_conntrack.py > helper-sha256.txt
python3 /task/replication/exercise.py capture
