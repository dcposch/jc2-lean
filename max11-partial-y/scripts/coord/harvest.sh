#!/bin/bash
# harvest.sh File.lean — report whether the file's current SHA-256 has a green receipt; list its final theorems.
P="${MAX11_DIR:-$HOME/code/math/jc2/jc2-lean/max11-partial-y}"; cd "$P" || exit 1
f="${1%.lean}"; sha=$(sha256sum "$f.lean" 2>/dev/null | cut -d' ' -f1 || shasum -a 256 "$f.lean" | cut -d' ' -f1)
r=$(grep -l "^VERIFIED_SHA256=$sha FILE=$f.lean\$" .max11-lanes/gates/*.receipt 2>/dev/null | head -1)
echo "$f: $(wc -l < $f.lean)L sha=${sha:0:12} receipt=${r:+$(basename $r | cut -c1-12)} $( [ -z "$r" ] && echo NOGREEN)"
grep -nE "^(theorem|def) |^#print" "$f.lean" | tail -12
