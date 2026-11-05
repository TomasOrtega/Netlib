set -eu
mkdir -p /tmp/netlib-safe-handoff/eap /tmp/netlib-proc /run/netlib-failover /run/netlib-eap /run/netlib-attachments
mount -t proc proc /tmp/netlib-proc
cd /tmp/netlib-safe-handoff
uname -a > kernel.txt
conntrack -V > conntrack-version.txt
conntrackd -v > conntrackd-version.txt
nft --version > nftables-version.txt
ip -Version > iproute2-version.txt
/opt/netlib/sbin/tc -V > tc-version.txt
apk --no-network info -vv > packages.txt
openssl version -a > eap/openssl-version.txt
hostapd -v > eap/hostapd-version.txt 2>&1 || test "$?" = 1
wpa_supplicant -v > eap/supplicant-version.txt 2>&1
sha256sum /usr/local/bin/hostapd /usr/local/bin/wpa_supplicant /usr/local/bin/hostapd_cli /usr/local/bin/wpa_cli /usr/bin/openssl /opt/netlib/sbin/conntrackd /opt/netlib/sbin/conntrack /opt/netlib/sbin/nft /opt/netlib/sbin/ip /opt/netlib/sbin/tc /tmp/tools.tar.xz /tmp/library.tar.xz /tmp/iproute2.tar.gz /tmp/iproute2-6.19.0/tc/q_netem.c > producer-sha256.txt
sha256sum /tmp/hostapd-2.12.tar.gz /tmp/wpa_supplicant-2.12.tar.gz > eap/source-sha256.txt
sha256sum /task/attachments/exercise.py /task/campus/exercise.py /task/safe-handoff/exercise.py /task/replication/exercise.py /task/replication/nflog.py /task/wire/exercise.py /task/capture_conntrack.py /task/eap_exercise.py > helper-sha256.txt
python3 /task/attachments/exercise.py capture
