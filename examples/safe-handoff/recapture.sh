#!/bin/sh
set -eu
recipe_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
capture_dir=${1:-"/tmp/netlib-safe-handoff-recapture-$$"}
build_dir=$(mktemp -d /tmp/netlib-safe-handoff-build.XXXXXX)
container_name="netlib-safe-handoff-capture-$$"
trap 'docker rm -f "$container_name" >/dev/null 2>&1 || true; rm -rf "$build_dir"' EXIT
test "$(docker image inspect netlib-replication-capture:1 --format '{{.Id}}')" = \
  sha256:2e4db031fbbdf6afde48186e0765b0e464cb1719bfde11cb42b40ede5d89c73f
cp "$recipe_dir/Dockerfile" "$recipe_dir/exercise.py" "$recipe_dir/capture.sh" "$build_dir/"
mkdir -p "$capture_dir/native"
docker build --network none -t netlib-safe-handoff-capture:1 "$build_dir" > "$capture_dir/build-stdout.txt" 2> "$capture_dir/build-stderr.txt"
docker create --name "$container_name" --network none --cap-add NET_ADMIN --cap-add SYS_ADMIN \
  --security-opt seccomp=unconfined --security-opt apparmor=unconfined netlib-safe-handoff-capture:1 >/dev/null
docker start -a "$container_name" > "$capture_dir/capture-stdout.txt" 2> "$capture_dir/capture-stderr.txt"
docker cp "$container_name:/tmp/netlib-safe-handoff/." "$capture_dir/native/"
docker inspect "$container_name" --format '{{json .}}' > "$capture_dir/container-inspect.json"
docker image inspect netlib-safe-handoff-capture:1 --format '{{.Id}}' > "$capture_dir/image-id.txt"
