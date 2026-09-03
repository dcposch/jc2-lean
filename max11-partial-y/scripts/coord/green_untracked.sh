#!/bin/bash
# List untracked *Scratch.lean whose current SHA-256 appears in a green receipt.
cd "${MAX11_DIR:-$HOME/code/math/jc2/jc2-lean/max11-partial-y}" || exit 1
grep -h "^VERIFIED_SHA256=" .max11-lanes/gates/*.receipt 2>/dev/null | sort -u > /tmp/.verified_lines.$$
for f in *Scratch.lean; do
  git ls-files --error-unmatch "$f" >/dev/null 2>&1 && continue
  sha=$(sha256sum 2>/dev/null "$f" | cut -d' ' -f1)
  if grep -q "^VERIFIED_SHA256=$sha FILE=$f\$" /tmp/.verified_lines.$$; then
    echo "GREEN $f $(stat -c %y "$f") ${sha:0:12}"
  else
    echo "nogreen $f $(stat -c %y "$f")"
  fi
done
rm -f /tmp/.verified_lines.$$
