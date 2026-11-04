set -eu
mkdir -p /tmp/netlib-eap /run/netlib-eap
cd /tmp/netlib-eap
uname -r > kernel.txt
openssl version -a > openssl-version.txt
hostapd -v > hostapd-version.txt 2>&1 || test "$?" = 1
wpa_supplicant -v > supplicant-version.txt 2>&1
apk --no-network info -vv > packages.txt
sha256sum /usr/local/bin/hostapd /usr/local/bin/wpa_supplicant > producer-sha256.txt
sha256sum /tmp/hostapd-2.12.tar.gz /tmp/wpa_supplicant-2.12.tar.gz > source-sha256.txt
python3 /task/exercise.py capture
