set -eu
mkdir -p /tmp/netlib-admission/eap /run/netlib-eap /run/netlib-admission /tmp/netlib-proc
mount -t proc proc /tmp/netlib-proc
cd /tmp/netlib-admission
uname -r > kernel.txt
nft --version > nftables-version.txt
ip -Version > iproute2-version.txt
conntrack -V > conntrack-version.txt
openssl version -a > openssl-version.txt
hostapd -v > hostapd-version.txt 2>&1 || test "$?" = 1
wpa_supplicant -v > supplicant-version.txt 2>&1
apk --no-network info -vv > packages.txt
sha256sum /usr/local/bin/hostapd /usr/local/bin/wpa_supplicant /opt/netlib/sbin/nft /opt/netlib/sbin/ip > producer-sha256.txt
sha256sum /task/eap_exercise.py /task/capture_conntrack.py > helper-sha256.txt
python3 /task/admission/exercise.py capture
