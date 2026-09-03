#!/bin/bash
# Block until a grok lane exits or a new receipt lands (max $1 seconds, default 570).
P="${MAX11_DIR:-$HOME/code/math/jc2/jc2-lean/max11-partial-y}"; G=$P/.max11-lanes/gates
max=${1:-570}; t=0
lanes0=$(ps -axo command= | grep -c "^grok --yolo.*LOCAL_LEAN_GUARD=enabled")
r0=$(ls $G/*.receipt 2>/dev/null | wc -l | tr -d ' ')
while [ $t -lt $max ]; do
  sleep 20; t=$((t+20))
  lanes=$(ps -axo command= | grep -c "^grok --yolo.*LOCAL_LEAN_GUARD=enabled")
  r=$(ls $G/*.receipt 2>/dev/null | wc -l | tr -d ' ')
  if [ "$lanes" != "$lanes0" ] || [ "$r" != "$r0" ]; then
    echo "EVENT after ${t}s: lanes $lanes0->$lanes receipts $r0->$r"
    [ "$r" != "$r0" ] && { f=$(ls -t $G/*.receipt | head -1); grep "^VERIFIED_SHA256" $f | tail -1 | cut -c1-160; }
    exit 0
  fi
done
echo "TIMEOUT ${max}s: lanes=$lanes0 receipts=$r0"
