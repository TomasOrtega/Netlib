#!/bin/sh
set -eu
recipe_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
capture_dir=${1:-"/tmp/netlib-reassembly-recapture-$$"}
build_dir=$(mktemp -d /tmp/netlib-reassembly-build.XXXXXX)
container_name="netlib-reassembly-capture-$$"
trap 'docker rm -f "$container_name" >/dev/null 2>&1 || true; rm -rf "$build_dir"' EXIT
test "$(docker image inspect netlib-received-icmp-capture:1 --format '{{.Id}}')" = \
  sha256:05d09351510c9fc2a6107d961530efdef25570cd5807506a2e20ad5883a7346b
cp "$recipe_dir/Dockerfile" "$recipe_dir/exercise.py" "$recipe_dir/nflog.py" \
  "$recipe_dir/capture.sh" "$recipe_dir/requirements.json" "$recipe_dir/deny.json" \
  "$recipe_dir/permit.json" "$recipe_dir/demo-credential.json" "$build_dir/"
mkdir -p "$capture_dir/native"
docker build --network none -t netlib-reassembly-capture:1 "$build_dir" > "$capture_dir/build-stdout.txt" 2> "$capture_dir/build-stderr.txt"
docker create --name "$container_name" --network none --cap-add NET_ADMIN --cap-add SYS_ADMIN \
  --security-opt seccomp=unconfined --security-opt apparmor=unconfined netlib-reassembly-capture:1 >/dev/null
docker start -a "$container_name" > "$capture_dir/capture-stdout.txt" 2> "$capture_dir/capture-stderr.txt"
docker cp "$container_name:/tmp/netlib-admission/." "$capture_dir/native/"
docker inspect "$container_name" --format '{{json .}}' > "$capture_dir/container-inspect.json"
docker image inspect netlib-reassembly-capture:1 --format '{{.Id}}' > "$capture_dir/image-id.txt"
