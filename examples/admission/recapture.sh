#!/bin/sh
set -eu
recipe_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
repository_dir=$(CDPATH= cd -- "$recipe_dir/../.." && pwd)
capture_dir=${1:-"$recipe_dir"}
build_dir=$(mktemp -d /tmp/netlib-admission-build.XXXXXX)
container_name="netlib-admission-capture-$$"
trap 'docker rm -f "$container_name" >/dev/null 2>&1 || true; rm -rf "$build_dir"' EXIT
test "$(docker image inspect netlib-eap-capture:2.12 --format '{{.Id}}')" = \
  sha256:1e4be80167e3f444cc3f82c5f96f59e1f72149fca6d2b7ed885013639da4f075
cp "$recipe_dir/Dockerfile" "$recipe_dir/exercise.py" "$recipe_dir/capture.sh" \
  "$recipe_dir/requirements.json" "$recipe_dir/deny.json" "$recipe_dir/permit.json" \
  "$recipe_dir/demo-credential.json" "$build_dir/"
cp "$repository_dir/examples/eap/exercise.py" "$build_dir/eap_exercise.py"
cp "$repository_dir/scripts/capture_conntrack.py" "$build_dir/capture_conntrack.py"
mkdir -p "$capture_dir/native"
docker build --network none -t netlib-admission-capture:1 "$build_dir" > "$capture_dir/build-stdout.txt" 2> "$capture_dir/build-stderr.txt"
docker create --name "$container_name" --network none --cap-add NET_ADMIN --cap-add SYS_ADMIN \
  --security-opt seccomp=unconfined --security-opt apparmor=unconfined netlib-admission-capture:1 >/dev/null
docker start -a "$container_name" > "$capture_dir/capture-stdout.txt" 2> "$capture_dir/capture-stderr.txt"
docker cp "$container_name:/tmp/netlib-admission/." "$capture_dir/native/"
docker inspect "$container_name" --format '{{json .}}' > "$capture_dir/container-inspect.json"
