#!/bin/sh
set -eu
recipe_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
capture_dir=${1:-"/tmp/netlib-attachments-recapture-$$"}
build_dir=$(mktemp -d /tmp/netlib-attachments-build.XXXXXX)
container_name="netlib-attachments-capture-$$"
trap 'docker rm -f "$container_name" >/dev/null 2>&1 || true; rm -rf "$build_dir"' EXIT
test "$(docker image inspect netlib-campus-capture:1 --format '{{.Id}}')" = \
  sha256:b17fdb28779b150b7f4ef45dd9e01ede24b05de251f276542c8f38dc6e1392b2
cp "$recipe_dir/Dockerfile" "$recipe_dir/exercise.py" "$recipe_dir/capture.sh" \
  "$recipe_dir/requirements.json" "$recipe_dir/demo-credential.json" \
  "$recipe_dir/permit.json" "$recipe_dir/deny.json" "$build_dir/"
mkdir -p "$capture_dir/native"
docker build --network none -t netlib-attachments-capture:1 "$build_dir" > "$capture_dir/build-stdout.txt" 2> "$capture_dir/build-stderr.txt"
docker create --name "$container_name" --network none --cap-add NET_ADMIN --cap-add SYS_ADMIN \
  --security-opt seccomp=unconfined --security-opt apparmor=unconfined netlib-attachments-capture:1 >/dev/null
capture_status=0
docker start -a "$container_name" > "$capture_dir/capture-stdout.txt" 2> "$capture_dir/capture-stderr.txt" || capture_status=$?
docker cp "$container_name:/tmp/netlib-safe-handoff/." "$capture_dir/native/"
docker inspect "$container_name" --format '{{json .}}' > "$capture_dir/container-inspect.json"
docker image inspect netlib-attachments-capture:1 --format '{{.Id}}' > "$capture_dir/image-id.txt"
exit "$capture_status"
