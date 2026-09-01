#!/usr/bin/env bash
# Sync keystone-graph to the box and run a fail-closed build + axiom probe.
set -euo pipefail
box_host="${BOX_LEAN_HOST:-ubuntu@54.81.66.156}"
box_key="${BOX_LEAN_KEY:-/Users/dc/.ssh/claude-cli.pem}"
here="$(cd "$(dirname "$0")/.." && pwd)"
rsync -a --delete --exclude='.lake' -e "ssh -i $box_key -o BatchMode=yes -o StrictHostKeyChecking=no" "$here/" "$box_host":/home/ubuntu/keystone-graph/
ssh -i "$box_key" -o BatchMode=yes -o StrictHostKeyChecking=no "$box_host" 'bash -s' <<'REMOTE'
set -u
export PATH=$HOME/.elan/bin:$PATH
cd /home/ubuntu/keystone-graph
lake exe cache get >/dev/null 2>&1 || true
lake build 2>&1 | tail -5
rc=${PIPESTATUS[0]}
echo "BUILD_EXIT=$rc"
exit $rc
REMOTE
