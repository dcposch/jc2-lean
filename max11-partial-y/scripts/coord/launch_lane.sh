#!/bin/bash
# Direct-launch one Grok proof lane with the Max-11 verification contract.
# usage: launch_lane.sh Target.lean logname "instruction text"
# env: MAX11_DIR (project dir), MAX11_LANE_LOGS (log dir)
set -u
target="$1"; logname="$2"; shift 2; instr="$*"
P="${MAX11_DIR:-$HOME/code/math/jc2/jc2-lean/max11-partial-y}"
S="${MAX11_LANE_LOGS:-$HOME/coord/lanes}"; mkdir -p "$S"
cd "$P" || exit 1
[[ "$target" =~ ^Grok[A-Za-z0-9_.-]*Scratch\.lean$ ]] || { echo "bad target $target"; exit 2; }
git ls-files --error-unmatch -- "$target" >/dev/null 2>&1 && { echo "refusing tracked target"; exit 65; }
n=$(ps -axo command= | grep -c "^grok --yolo.*LOCAL_LEAN_GUARD=enabled")
(( n >= 8 )) && { echo "worker cap reached: $n/8"; exit 75; }
ps -axo command= | grep "^grok --yolo" | grep -q "$target" && { echo "a worker already mentions $target"; exit 75; }
C="Work autonomously in $P. No tracked edits, sorry, new axioms, finite-root shortcuts, or closure overclaims. Do not invoke local Lean or Lake; the guarded PATH intentionally disables them. Use ./scripts/box_lean_verify.sh --file $target for every Lean compilation/check, run it in the FOREGROUND and never exit while a verify is running. Finish only after literal BUILD_EXIT=0 ERROR_COUNT=0 SORRYAX_COUNT=0, and report the file SHA-256, exact gain, next unused row, and residual. LOCAL_LEAN_GUARD=enabled. Requested output: $target"
env PATH="$P/scripts/no-local-lean:$PATH" nohup grok --yolo --output-format plain -p "$instr $C" > "$S/$logname.log" 2>&1 &
echo "$! $target" >> "$S/pid_targets.txt"
echo "launched pid=$! target=$target log=$S/$logname.log workers_before=$n"
