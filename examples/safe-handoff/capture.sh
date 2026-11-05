set -eu
mkdir -p /tmp/netlib-safe-handoff /tmp/netlib-proc /run/netlib-failover
mount -t proc proc /tmp/netlib-proc
cd /tmp/netlib-safe-handoff
uname -a > kernel.txt
conntrack -V > conntrack-version.txt
conntrackd -v > conntrackd-version.txt
nft --version > nftables-version.txt
ip -Version > iproute2-version.txt
/opt/netlib/sbin/tc -V > tc-version.txt
apk --no-network info -vv > packages.txt
sha256sum /opt/netlib/sbin/conntrackd /opt/netlib/sbin/conntrack /opt/netlib/sbin/nft /opt/netlib/sbin/ip /opt/netlib/sbin/tc /tmp/tools.tar.xz /tmp/library.tar.xz /tmp/iproute2.tar.gz /tmp/iproute2-6.19.0/tc/q_netem.c > producer-sha256.txt
sha256sum /task/safe-handoff/exercise.py /task/replication/exercise.py /task/replication/nflog.py /task/wire/exercise.py /task/capture_conntrack.py > helper-sha256.txt
python3 /task/safe-handoff/exercise.py capture
