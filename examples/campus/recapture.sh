#!/bin/sh
set -eu
recipe_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
capture_dir=${1:-"/tmp/netlib-campus-recapture-$$"}
build_dir=$(mktemp -d /tmp/netlib-campus-build.XXXXXX)
container_name="netlib-campus-capture-$$"
trap 'docker rm -f "$container_name" >/dev/null 2>&1 || true; rm -rf "$build_dir"' EXIT
test "$(docker image inspect netlib-safe-handoff-capture:1 --format '{{.Id}}')" = \
  sha256:0de06682f606f74cd8f67ad189e92a240077bec45928be5e91792237d8f08b10
cp "$recipe_dir/Dockerfile" "$recipe_dir/exercise.py" "$recipe_dir/capture.sh" \
  "$recipe_dir/requirements.json" "$recipe_dir/demo-credential.json" \
  "$recipe_dir/permit.json" "$recipe_dir/deny.json" "$build_dir/"
mkdir -p "$capture_dir/native"
docker build --network none -t netlib-campus-capture:1 "$build_dir" > "$capture_dir/build-stdout.txt" 2> "$capture_dir/build-stderr.txt"
docker create --name "$container_name" --network none --cap-add NET_ADMIN --cap-add SYS_ADMIN \
  --security-opt seccomp=unconfined --security-opt apparmor=unconfined netlib-campus-capture:1 >/dev/null
docker start -a "$container_name" > "$capture_dir/capture-stdout.txt" 2> "$capture_dir/capture-stderr.txt"
docker cp "$container_name:/tmp/netlib-safe-handoff/." "$capture_dir/native/"
docker inspect "$container_name" --format '{{json .}}' > "$capture_dir/container-inspect.json"
docker image inspect netlib-campus-capture:1 --format '{{.Id}}' > "$capture_dir/image-id.txt"
