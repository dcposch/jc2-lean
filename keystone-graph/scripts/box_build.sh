#!/usr/bin/env bash
# Sync keystone-graph to the box and run a fail-closed build + axiom probe.
set -euo pipefail
box_host="${BOX_LEAN_HOST:-ubuntu@54.81.66.156}"
box_key="${BOX_LEAN_KEY:-/Users/dc/.ssh/claude-cli.pem}"
here="$(cd "$(dirname "$0")/.." && pwd)"
rsync -a --delete --exclude='.lake' -e "ssh -i $box_key -o BatchMode=yes -o StrictHostKeyChecking=no" "$here/" "$box_host":/home/ubuntu/"${KG_BOX_DIR:-keystone-graph}"/
ssh -i "$box_key" -o BatchMode=yes -o StrictHostKeyChecking=no "$box_host" "KG_BOX_DIR=${KG_BOX_DIR:-keystone-graph} bash -s" <<'REMOTE'
set -u
export PATH=$HOME/.elan/bin:$PATH
cd /home/ubuntu/"$KG_BOX_DIR"
lake exe cache get >/dev/null 2>&1 || true
log="$(mktemp)"
set +e
lake build >"$log" 2>&1
rc=$?
set -e
grep -E "depends on axioms|error:|sorryAx|warning:.*sorry" "$log" || true
tail -12 "$log"
echo "BUILD_EXIT=$rc"
exit $rc
REMOTE
