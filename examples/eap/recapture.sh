#!/bin/sh
set -eu
recipe_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
capture_dir=${1:-"$recipe_dir"}
build_dir=$(mktemp -d /tmp/netlib-eap-build.XXXXXX)
container_name="netlib-eap-capture-$$"
trap 'docker rm -f "$container_name" >/dev/null 2>&1 || true; rm -rf "$build_dir"' EXIT
test "$(docker image inspect netlib-lifecycle-capture:6.19.0 --format '{{.Id}}')" = \
  sha256:566c6af8672a432d7b9db65593d54e5d6d5f0fd5e98e644979f9adefedc0bebd
curl --fail --location --output "$build_dir/hostapd-2.12.tar.gz" https://w1.fi/releases/hostapd-2.12.tar.gz
curl --fail --location --output "$build_dir/wpa_supplicant-2.12.tar.gz" https://w1.fi/releases/wpa_supplicant-2.12.tar.gz
cp "$recipe_dir/Dockerfile" "$recipe_dir/hostapd-build.config" \
  "$recipe_dir/supplicant-build.config" "$recipe_dir/exercise.py" "$recipe_dir/capture.sh" "$build_dir/"
mkdir -p "$capture_dir/native"
docker build -t netlib-eap-capture:2.12 "$build_dir" > "$capture_dir/build-stdout.txt" 2> "$capture_dir/build-stderr.txt"
docker create --name "$container_name" --network none --cap-add NET_ADMIN --cap-add SYS_ADMIN \
  --security-opt seccomp=unconfined --security-opt apparmor=unconfined netlib-eap-capture:2.12 >/dev/null
docker start -a "$container_name" > "$capture_dir/capture-stdout.txt" 2> "$capture_dir/capture-stderr.txt"
docker cp "$container_name:/tmp/netlib-eap/." "$capture_dir/native/"
docker image inspect netlib-eap-capture:2.12 --format '{{.Id}}' > "$capture_dir/image-id.txt"
docker inspect "$container_name" --format '{{json .}}' > "$capture_dir/container-inspect.json"
